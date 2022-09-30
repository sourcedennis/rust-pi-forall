extern crate nom;

// stdlib imports
use std::collections::HashSet;
// external library imports
use nom::{
  IResult,
  bytes::complete::{tag, take_while, take_until, take_while1},
  combinator::{opt, recognize, verify, map},
  sequence::{delimited, separated_pair, preceded},
  error::{Error, ErrorKind, ParseError},
  branch::alt, multi::{many1_count, separated_list1, many1, many0},
  Parser
};
use nom_locate::LocatedSpan;
// local imports
use crate::unbound::{FreeName, Name, Bind};
use crate::syntax::{
  ManyBind, Epsilon, Arg, Sig, Match, Pattern, Module, Decl, Term, Prec
};
use crate::pretty_print::{RESERVED};


type Indent = usize;
type Span< 'a > = LocatedSpan< &'a str >;


type PResult< 'a, O > = IResult< Span< 'a >, O, nom::error::Error<Span< 'a >> >;


// # Lexer

#[derive(Debug, PartialEq)]
pub enum BlockElement< T > {
  NewLine( Indent ),
  Token( T )
}

/// Discards the output of a parser. (i.e., it becomes `()`)
fn discard< I, O, E, F >(
  f: F
) -> impl FnMut( I ) -> IResult< I, (), E >
where
  F: FnMut( I ) -> IResult< I, O, E >
{
  map( f, |_| () )
}

/// Parses: [a-zA-Z_'] [a-zA-Z0-9_']*
///   (also parses other Unicode Alphabetic chars, that's ok)
#[must_use]
fn lex_word( input: Span ) -> PResult< () > {
  // this is actually: [a-zA-Z]* [a-zA-Z0-9]* but ambiguity is irrelevant
  let (input, _) = take_while1( |c:char| c.is_alphabetic( ) || c == '_' || c == '\'' )( input )?;
  let (input, _) = take_while( |c:char| c.is_alphanumeric( ) || c == '_' || c == '\'' )( input )?;
  Ok( (input, ()) )
}

/// parses: \ ( ) -> : .
fn lex_symbol( input: Span ) -> PResult< () > {
  discard(
    alt(
      (
        tag( "\\" ), // for lambdas
        tag( "()" ),
        tag( "(" ),
        tag( ")" ),
        tag( "->" ),
        tag( ":" ),
        tag( "." ), // for lambdas
        tag( "=" ),
        tag( "{" ), // for sigma types
        tag( "|" ), // for sigma types
        tag( "}" ), // for sigma types
        tag( "," ),
        tag( "[" ), // for irrelevance
        tag( "]" )  // for irrelevance
      )
    )
  )( input )
}

fn lex_line_comment( input: Span ) -> PResult< () > {
  let (input, _) = tag( "--" )( input )?;
  let (input, _) = take_until( "\n" )( input )?;
  // Actually consume the "\n" value
  let (input, _) = opt( tag( "\n" ) )( input )?;
  Ok( (input, ()) )
}

fn lex_block_comment( input: Span ) -> PResult< () > {
  // no such thing as nested comments
  let (input, _) = tag( "{-" )( input )?;
  let (input, _) = take_until( "-}" )( input )?;
  let (input, _) = tag( "-}" )( input )?;
  Ok( (input, ()) )
}

/// 
fn lex_padding( input: Span ) -> PResult< () > {
  discard(
    many1_count(
      alt(
        (
          discard( tag( " " ) ),
          discard( tag( "\t" ) ),
          discard( tag( "\r" ) ),
          discard( tag( "\n" ) ),
          lex_line_comment,
          lex_block_comment,
        )
      )
    )
  )( input )
}

/// We distinguish between:
/// - tokens. all words and symbols
/// - padding. whitespace and comments. we do report vertical spacing, and track
///   indentation after newlines.
pub fn lex( mut input: Span ) -> PResult< BlockElement< Span > > {
  if let Ok( (input2, _) ) = lex_padding( input ) { // Ignore garbage
    if input2.is_empty( ) {
      return Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Eof)));
    } else if input.location_line( ) < input2.location_line( ) {
      // we skipped through a newline somewhere, but are *not* at a new block
      return Ok( (input2, BlockElement::NewLine( input2.get_utf8_column( ) - 1 )) );
    } else {
      input = input2;
    }
  }

  map(
    recognize( alt( ( lex_word, lex_symbol ) ) ),
    BlockElement::Token
  )( input )
}

/// Returns true iff the input contains no meaningful content. (It may still
/// contains whitespace and comments)
pub fn is_lex_end( input: Span ) -> bool {
  if input.is_empty( ) {
    true
  } else if let Ok( (input, _) ) = lex_padding( input ) {
    input.is_empty( )
  } else {
    false
  }
}

#[must_use]
pub fn lex_token_if< 'i, F >(
  mut cond: F
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Span< 'i > >
where
  F: FnMut( &'i str ) -> bool
{
  move |input| {
    match lex( input ) {
      Ok( ( input2, BlockElement::Token( x ) ) ) =>
        if cond( x.fragment( ) ) {
          Ok( ( input2, x ) )
        } else {
          Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag)))
        },
      Ok( ( input2, _ ) ) =>
        Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag))),
      Err( err ) => Err( err )
    }
  }
}


// # Parse

/// Context for the parser.
/// 
/// We require indentation level for parsing layout-sensitive fragments.
/// Constructor names are needed to disambiguate between constructor names and
/// variables.
/// 
/// # Decision: Copy
/// 
/// We specifically allow copying. That enables easily passing it into closures.
/// It incurs little performance penalty, as the contained HashSet is passed *by
/// reference*.
#[derive(Clone, Copy)]
struct PCtx< 'i: 'a, 'a > {
  i: Indent,
  /// Data constructor names
  dcon_names : &'a HashSet< &'i str >,
  // /// Type constructor names
  // tcon_names : HashSet< String >
}

impl< 'i: 'a, 'a > PCtx< 'i, 'a > {
  fn set_indent( self, indent: Indent ) -> Self {
    PCtx { i: indent, ..self }
  }
}

fn p_newline( input: Span ) -> PResult< Indent > {
  if let Ok( ( input2, BlockElement::NewLine( indent ) ) ) = lex( input ) {
    Ok( (input2, indent) )
  } else { // no whitespace whatsoever, that's ok
    Err(nom::Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
  }
}

/// Skip 0 or 1 newline, provided that the *indentation does not decrease*.
/// Intuitively this means that the subsequent lines belong to the same
/// syntactic block (or a sub-block).
fn p_skip_newline( indent: Indent ) -> impl Fn( Span ) -> PResult< Indent > {
  move |input|
    if let Ok( ( input2, BlockElement::NewLine( indent2 ) ) ) = lex( input ) {
      if indent2 >= indent {
        Ok( (input2, indent2) )
      } else { // we're dropping to an "outer scope". so, don't consume it
        Ok( (input, indent))
      }
    } else { // no whitespace whatsoever, that's ok
      Ok( (input, indent) )
    }
}

/// 
/// This returns a `LexResult`, because we don't care about indentation
/// "outside" the module.
pub fn p_module< 'i >( input: Span< 'i > ) -> PResult< 'i, Module > {
  let (input, _)    = p_skip_newline( 0 )( input )?;
  let (input, _)    = lex_token_if( |x| x == "module" )( input )?;
  let (input, _)    = p_skip_newline( 1 )( input )?;
  let (input, name) = lex_token_if( is_identifier )( input )?;
  let (input, _)    = p_skip_newline( 1 )( input )?;
  let (input, _)    = lex_token_if( |x| x == "where" )( input )?;


  let mut dcon_names = HashSet::new( );
  dcon_names.insert( "True" );
  dcon_names.insert( "False" );

  let mut entries: Vec< Decl< String > > = Vec::new( );

  let mut input = input;

  // ensure new declarations start at indentation 0
  while let Ok( (input2, _) ) = verify( lex, |x| *x == BlockElement::NewLine( 0 ) )( input ) {
    let (input2, decl): (Span< 'i >, Decl< &'i str >) = p_decl( &dcon_names )( input2 )?;

    match decl {
      Decl::TypeSig( sig ) => {
        entries.push( Decl::TypeSig( Sig::new( sig.name.to_owned( ), sig.eps, sig.ttype ) ) );
      },
      Decl::Def( name, term ) => {
        entries.push( Decl::Def( name.to_owned( ), term ) );
      }
    }

    input = input2;
  }

  Ok( (input, Module { name: (*name.fragment( )).to_owned( ), entries } ) )
}

fn is_word( x: &str ) -> bool {
  if let Ok( (rem, ()) ) = lex_word( LocatedSpan::new( x ) ) {
    rem.is_empty( )
  } else {
    false
  }
}

fn is_identifier( x: &str ) -> bool {
  is_word( x ) && !RESERVED.contains( &x )
}

pub fn p_identifier( input: Span ) -> PResult< &str > {
  let (input, v) = lex_token_if( is_identifier )( input )?;
  Ok( (input, v.fragment( )) )
}

fn p_term_prec< 'i: 'a, 'a >( prec: Prec, ctx: PCtx< 'i, 'a > )
  -> impl Fn( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  move |input| {
    match prec {
      Prec::Colon      => p_term_colon( ctx )( input ),
      Prec::Lambda     => p_term_lambda( ctx )( input ),
      Prec::Arrow      => p_term_arrow( ctx )( input ),
      Prec::IfThenElse => p_term_iflet( ctx )( input ),
      Prec::Equality   => p_equality( ctx )( input ),
      Prec::App        => p_term_app( ctx )( input ),
      Prec::Atom       => p_term_atom( ctx )( input )
    }
  }
}

/// Parses terms with precedence 4. (Weakest)
/// <term4> := <term3> [':' <term4>]
/// 
/// So, in theory, we can have an expression:
/// > f : Nat -> Nat : Set
/// which parses as:
/// > f : (Nat -> Nat : Set)
fn p_term_colon< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  move |input| {
    let (input, x) = p_term_prec( Prec::Colon.inc( ), ctx )( input )?;
    let (input, _) = p_skip_newline( ctx.i )( input )?;
    let (input, t) = opt( lex_token_if( |x| x == ":" ) )( input )?;
    let (input, _) = p_skip_newline( ctx.i )( input )?;
  
    if t.is_some( ) {
      let (input, y) = p_term_prec( Prec::Colon, ctx )( input )?;
      Ok( ( input, Term::Ann( Box::new( x ), Box::new( y ) ) ) )
    } else {
      Ok( (input, x) )
    }
  }
}

/// Skip (optional) subsequent newlines.
/// 
/// intuitively: ws( f, d ) = terminated( f, p_skip_newline( d ) )
fn ws< 'a, 'i: 'a, O, F >(
  mut f: F,
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, O > + 'a
where
  F : 'a + Parser< Span< 'i >, O, nom::error::Error<Span< 'i >> >
  // FnMut( Span< 'i > ) -> IResult< Span< 'i >, O, nom::error::Error<Span< 'i >>> + 'a
{
  move |input: Span< 'i >| {
    let (input, x) = f.parse( input )?;
    let (input, _) = p_skip_newline( ctx.i )( input )?;
    Ok( (input, x) )
  }
}

/// Parse:
/// <term> := <term+1> '->' <term>
///         | '[' <term> ']' '->' <term>
///         | '(' <identifier> ':' <term> ')' '->' <term>
///         | '[' <identifier> ':' <term> ']' '->' <term>
///         | <term+1>
fn p_term_arrow< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  /// Parses: '(' <identifier> ':' <term> ')'
  fn p_named_type< 'i: 'a, 'a >(
    ctx: PCtx< 'i, 'a >
  ) -> impl FnMut( Span< 'i > ) -> PResult< 'i, (&'i str, Term) > + 'a {

    delimited(
      ws( lex_token_if( |x| x == "(" ), ctx ),
      separated_pair(
        ws( p_identifier, ctx ),
        ws( lex_token_if( |x| x == ":" ), ctx ),
        ws( p_term_prec( Prec::Arrow, ctx ), ctx )
      ),
      lex_token_if( |x| x == ")" )
    )
  }

  /// Parses: '[' <identifier> ':' <term> ']'
  fn p_irr_named_type< 'i: 'a, 'a >(
    ctx: PCtx< 'i, 'a >
  ) -> impl FnMut( Span< 'i > ) -> PResult< 'i, (&'i str, Term) > + 'a {

    delimited(
      ws( lex_token_if( |x| x == "[" ), ctx ),
      separated_pair(
        ws( p_identifier, ctx ),
        ws( lex_token_if( |x| x == ":" ), ctx ),
        ws( p_term_prec( Prec::Arrow, ctx ), ctx )
      ),
      lex_token_if( |x| x == "]" )
    )
  }

  /// Parses: '[' <term> ']'
  fn p_irr_type< 'i: 'a, 'a >(
    ctx: PCtx< 'i, 'a >
  ) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
    delimited(
      ws( lex_token_if( |x| x == "[" ), ctx ),
      ws( p_term_prec( Prec::Arrow, ctx ), ctx ),
      lex_token_if( |x| x == "]" )
    )
  }

  move |input| {
    let (input, (lhs_name, eps, lhs_term)) =
      ws(
        alt(
          (
            map( p_named_type( ctx ), |(n,t)| (Some(n), Epsilon::Rel, t) ),
            map( p_irr_named_type( ctx ), |(n,t)| (Some(n), Epsilon::Irr, t) ),
            map( p_irr_type( ctx ), |t| (None, Epsilon::Irr, t) ),
            map( p_term_prec( Prec::Arrow.inc( ), ctx ), |t| (None, Epsilon::Rel, t) )
          )
        ),
        ctx
      )( input )?;
  
    let (input, m_rhs) =
      opt(
        preceded(
          ws( lex_token_if( |x| x == "->" ), ctx ),
          p_term_prec( Prec::Arrow, ctx )
        )
      )( input )?;
  
  
    if let Some( rhs ) = m_rhs {
      let t =
        if let Some( lhs_name ) = lhs_name {
          let name = FreeName::from( FreeName::Text( lhs_name.to_owned( ) ) );
          Term::Pi( eps, Box::new( lhs_term ), Bind::bind( &name, Box::new( rhs ) ) )
        } else {
          Term::Pi( eps, Box::new( lhs_term ), Bind::nameless_bind( Box::new( rhs ) ) )
        };
      Ok( (input, t ) )
    } else if let Some( lhs_name ) = lhs_name {
      if eps == Epsilon::Irr { // cannot have just [x : A] as term
        Err(nom::Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
      } else { // eps == Epsilon::Rel. we parsed (x : A) without arrow
        let name = FreeName::from( FreeName::Text( lhs_name.to_owned( ) ) );
        let term = Term::Var( Name::Free( name ) );
        let ttype = lhs_term;
        Ok( ( input, Term::Ann( Box::new( term ), Box::new( ttype ) ) ) )
      }
    } else { // case: <term> := <term+1>
      Ok( ( input, lhs_term ) )
    }
  }
}

/// Parse: <eps-identifier> := <identifier>
///                          | '[' <identifier> ']'
fn p_eps_identifier< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, (Epsilon, &'a str) > {
  alt(
    (
      map( p_identifier, |x| (Epsilon::Rel, x) ),
      map(
        delimited(
          lex_token_if( |x| x == "[" ), // no subsequent newlines allowed
          p_identifier, // no subsequent newlines allowed
          lex_token_if( |x| x == "]" )
        ),
        |x| (Epsilon::Irr, x)
      )
    )
  )( input )
}

/// Parse:
/// <term> := '\' <eps-identifier>* '.' <term>
///         | <term+1>
fn p_term_lambda< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  move |input| {
    let (input, m_lambda) = opt( ws( lex_token_if( |x| x == "\\" ), ctx ) )( input )?;
  
    if m_lambda.is_some( ) {
      let (input, identifiers) = many1( ws( p_eps_identifier, ctx ) )( input )?;
      let (input, _) = ws( lex_token_if( |x| x == "." ), ctx )( input )?;
      let (input, mut body) = p_term_prec( Prec::Lambda, ctx )( input )?;
  
      for (eps, id) in identifiers.into_iter( ).rev( ) {
        let name = FreeName::from( FreeName::Text( id.to_owned( ) ) );
        body = Term::Lam( eps, Bind::bind( &name, Box::new( body ) ) );
      }
  
      Ok( (input, body) )
    } else {
      p_term_prec( Prec::Lambda.inc( ), ctx )( input )
    }
  }
}

fn p_term_iflet< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  alt(
    (
      p_ifthenelse( ctx ),
      p_letin( ctx ),
      p_case( ctx ),
      p_subst( ctx ),
      p_term_prec( Prec::IfThenElse.inc( ), ctx )
    )
  )
}

fn p_case< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  move |input| {
    let (input, case_token) = ws( lex_token_if( |x| x == "case" ), ctx )( input )?;
    let (input, t)          = ws( p_term_prec( Prec::IfThenElse.inc( ), ctx ), ctx )( input )?;
    let (input, _)          = lex_token_if( |x| x == "of" )( input )?;

    let (input, match_indent) = p_newline( input )?;

    // -1, because nom_locate starts at index 1, we at 0.
    // +1, because it must be indented further than the case statement
    if match_indent < case_token.get_utf8_column( ) - 1 + 1 {
      return Err(nom::Err::Error(Error::from_error_kind(input, ErrorKind::Tag)));
    }

    let (input, xs) =
      separated_list1(
        verify( p_newline, |i| *i == match_indent ),
        p_match( ctx )
      )( input )?;

    Ok( (input, Term::Case( Box::new( t ), xs ) ) )
  }
}

/// Parse:
/// <match> := <pattern> '->' <term>
fn p_match< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Match > + 'a {
  move |input| {
    let match_indent = input.get_utf8_column() - 1;

    let (input, (pattern, names)) = p_pattern( ctx )( input )?;

    let ctx2 = ctx.set_indent( match_indent + 1 );
    let (input, _) = ws( lex_token_if( |x| x == "->" ), ctx2 )( input )?;
    let (input, term) = p_term_prec( Prec::Arrow.inc( ), ctx2 )( input )?;

    let term =
      names.into_iter( ).rev( )
        .fold(
          ManyBind::Base( term ),
          |acc,name| ManyBind::Bind1( Bind::bind( &FreeName::Text( name.to_owned( ) ), Box::new( acc ) ) )
        );

    Ok( (input, Match::new( pattern, term ) ) )
  }
}

/// Parse:
/// <pattern> := <identifier>
///            | '(' <in-pattern> ')'
/// 
/// <in-pattern> := <identifier> <eps-pattern>+
/// 
/// <eps-pattern> := '[' <in-pattern> ']'
///                | '[' <identifier> ']'
///                | <pattern>
fn p_pattern< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, (Pattern, Vec< &'i str >) > + 'a {

  /// Parse:
  /// <in-pattern> := <identifier> <eps-pattern>+
  fn p_in_pattern< 'i: 'a, 'a >(
    ctx: PCtx< 'i, 'a >
  ) -> impl FnMut( Span< 'i > ) -> PResult< 'i, ( Pattern, Vec< &'i str > ) > + 'a {
    move |input| {
      let (input, con_name) = p_identifier( input )?;
      let (input, xs) = many1( p_eps_pattern( ctx ) )( input )?;

      let (patterns, names) =
        xs.into_iter( )
          .fold(
            ( Vec::new( ), Vec::new( ) ),
            |(mut patterns, mut names), (pat,eps,mut ns)| {
              patterns.push( (pat, eps) );
              names.append( &mut ns );
              (patterns, names)
            }
          );

      Ok( (input, ( Pattern::Con( con_name.to_owned( ), patterns ), names ) ) )
    }
  }

  /// Parse:
  /// <eps-pattern> := '[' <in-pattern> ']'
  ///                | '[' <identifier> ']'
  ///                | <pattern>
  fn p_eps_pattern< 'i: 'a, 'a >(
    ctx: PCtx< 'i, 'a >
  ) -> impl FnMut( Span< 'i > ) -> PResult< 'i, (Pattern, Epsilon, Vec< &'i str >) > + 'a {
    alt(
      (
        delimited(
          lex_token_if( |x| x == "[" ),
          map( p_in_pattern( ctx ), |(x,ns)| (x, Epsilon::Irr, ns) ),
          lex_token_if( |x| x == "]" )
        ),
        delimited(
          lex_token_if( |x| x == "[" ),
          map( p_identifier, |x| {
            if ctx.dcon_names.contains( x ) { // it's a constructor without arguments
              (Pattern::Con( x.to_owned( ), Vec::new( ) ), Epsilon::Irr, Vec::new( ))
            } else { // it's a variable
              (Pattern::Var, Epsilon::Irr, vec![ x ])
            }
          }),
          lex_token_if( |x| x == "]" )
        ),
        map( p_pattern( ctx ), |(x,ns)| (x, Epsilon::Rel, ns) )
      )
    )
  }

  alt(
    (
      // specifically match a *word* (not an identifier), because the built-in
      // constructors (e.g., True/False) may also occur here.
      map( recognize( lex_word ), |x| {
        if ctx.dcon_names.contains( x.fragment( ) ) { // it's a constructor without arguments
          (Pattern::Con( (*x.fragment( )).to_owned( ), Vec::new( ) ), Vec::new( ))
        } else { // it's a variable
          (Pattern::Var, Vec::new( ))
        }
      }),
      delimited(
        lex_token_if( |x| x == "(" ),
        p_in_pattern( ctx ),
        lex_token_if( |x| x == ")" )
      )
    )
  )
}

/// Parse:
/// <term> := 'if' <term> 'then' <term> 'else' <term>
///         | <term+1>
/// 
/// Remarkably, we can have nested if-then-else statements inside any of its
/// three arguments, as no ambiguity occurs.
fn p_ifthenelse< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _) = ws( lex_token_if( |x| x == "if" ), ctx )( input )?;
    let (input, cond) = ws( p_term_prec( Prec::IfThenElse, ctx ), ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "then" ), ctx )( input )?;
    let (input, if_case) = ws( p_term_prec( Prec::IfThenElse, ctx ), ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "else" ), ctx )( input )?;
    let (input, else_case) = ws( p_term_prec( Prec::IfThenElse, ctx ), ctx )( input )?;
  
    Ok( (input, Term::If( Box::new( cond ), Box::new( if_case ), Box::new( else_case ) ) ) )
  }
}

fn p_letin< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _) = ws( lex_token_if( |x| x == "let" ), ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "(" ), ctx )( input )?;
    let (input, x_name) = ws( p_identifier, ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "," ), ctx )( input )?;
    let (input, y_name) = ws( p_identifier, ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == ")" ), ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "=" ), ctx )( input )?;
    let (input, scrut) = ws( p_term_prec( Prec::IfThenElse.inc( ), ctx ), ctx )( input )?;
    let (input, _) = ws( lex_token_if( |x| x == "in" ), ctx )( input )?;
    let (input, body) = p_term_prec( Prec::IfThenElse, ctx )( input )?;
  
    let bnd1 = Bind::bind( &FreeName::Text( y_name.to_string( ) ), Box::new( body ) );
    let bnd2 = Bind::bind( &FreeName::Text( x_name.to_string( ) ), bnd1 );
  
    Ok( (input, Term::LetPair( Box::new( scrut ), bnd2 ) ) )
  }
}

/// Parse: <term> := 'subst' <term+1> 'by' <term+1>
fn p_subst< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _)  = ws( lex_token_if( |x| x == "subst" ), ctx )( input )?;
    let (input, x)  = ws( p_term_prec( Prec::IfThenElse.inc( ), ctx ), ctx )( input )?;
    let (input, _)  = ws( lex_token_if( |x| x == "by" ), ctx )( input )?;
    let (input, pf) = p_term_prec( Prec::IfThenElse.inc( ), ctx )( input )?;
  
    Ok( (input, Term::Subst( Box::new( x ), Box::new( pf ) ) ) )
  }
}

/// Parse: <term> := <term+1> '=' <term+1>
///                | <term+1>
fn p_equality< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {

  move |input| {
    let (input, x) = ws( p_term_prec( Prec::Equality.inc( ), ctx ), ctx )( input )?;
  
    if let Ok( (input, _) ) = ws( lex_token_if( |x| x == "=" ), ctx )( input ) {
      let (input, y) = p_term_prec( Prec::Equality.inc( ), ctx )( input )?;
      Ok( (input, Term::TyEq( Box::new( x ), Box::new( y ) ) ) )
    } else {
      Ok( (input, x) )
    }
  }
}

fn p_arg< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Arg > + 'a {
  alt(
    (
      map( p_term_prec( Prec::App.inc( ), ctx ), |x| Arg::new( Epsilon::Rel, x ) ),
      map(
        delimited(
          ws( lex_token_if( |x| x == "[" ), ctx ),
          ws( p_term_prec( Prec::weakest( ), ctx ), ctx ),
          lex_token_if( |x| x == "]" )
        ),
        |x| Arg::new( Epsilon::Irr, x ) ),
    )
  )
}

/// Parse: <term> := <term+1>+
fn p_term_app< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, mut term) = ws( p_term_prec( Prec::App.inc( ), ctx ), ctx )( input )?;
  
    let (input, args) = many0( ws( p_arg( ctx ), ctx ) )( input )?;
  
    for arg in args {
      term = Term::App( Box::new( term ), Box::new( arg ) );
    }
    Ok( (input, term) )
  }
}

fn p_term_atom< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  alt(
    (
      map( lex_token_if( |x| x == "Type" ), |_| Term::Type ),
      map( lex_token_if( |x| x == "Bool" ), |_| Term::TyBool ),
      map( lex_token_if( |x| x == "True" ), |_| Term::LitBool( true ) ),
      map( lex_token_if( |x| x == "False" ), |_| Term::LitBool( false ) ),
      map( lex_token_if( |x| x == "()" ), |_| Term::LitUnit ),
      map( lex_token_if( |x| x == "Unit" ), |_| Term::TyUnit ),
      map( lex_token_if( |x| x == "Refl" ), |_| Term::Refl ),
      map( p_identifier, |x| Term::Var( Name::Free( FreeName::Text( x.to_owned( ) ) ) ) ),
      p_contra( ctx ),
      p_sigma_type( ctx ),
      p_tuple( ctx )
    )
  )
}

/// Parse:
/// <term> := '(' <term-w> ')'
///         | '(' <term-w> ',' <term-w> ')'
fn p_tuple< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _) = ws( lex_token_if( |x| x == "(" ), ctx )( input )?;
    let (input, v1) = ws( p_term_prec( Prec::weakest( ), ctx ), ctx )( input )?;
  
    let (input, m_v2) =
      opt( preceded(
        ws( lex_token_if( |x| x == "," ), ctx ),
        ws( p_term_prec( Prec::weakest( ), ctx ), ctx )
      ) )( input )?;
  
    let (input, _) = lex_token_if( |x| x == ")" )( input )?;
  
    if let Some( v2 ) = m_v2 {
      Ok( ( input, Term::Prod( Box::new( v1 ), Box::new( v2 ) ) ) )
    } else {
      Ok( ( input, v1 ) )
    }
  }
}

fn p_contra< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _) = ws( lex_token_if( |x| x == "contra" ), ctx )( input )?;
    let (input, x) = p_term_prec( Prec::Atom, ctx )( input )?;
    Ok( ( input, Term::Contra( Box::new( x ) ) ) )
  }
}

fn p_sigma_type< 'i: 'a, 'a >(
  ctx: PCtx< 'i, 'a >
) -> impl FnMut( Span< 'i > ) -> PResult< 'i, Term > + 'a {
  move |input| {
    let (input, _)     = ws( lex_token_if( |x| x == "{" ), ctx )( input )?;
    let (input, name)  = ws( p_identifier, ctx )( input )?;
    let (input, _)     = ws( lex_token_if( |x| x == ":" ), ctx )( input )?;
    let (input, a)     = ws( p_term_prec( Prec::weakest( ), ctx ), ctx )( input )?;
    let (input, _)     = ws( lex_token_if( |x| x == "|" ), ctx )( input )?;
    let (input, b)     = ws( p_term_prec( Prec::weakest( ), ctx ), ctx )( input )?;
    let (input, _)     = lex_token_if( |x| x == "}" )( input )?;
  
    Ok( (input, Term::Sigma( Box::new( a ), Bind::bind( &FreeName::Text( name.to_owned( ) ), Box::new( b ) ) ) ) )
  }
}

///
/// Precondition: indentation = 0
fn p_decl< 'i: 'a, 'a >(
  dcon_names: &'a HashSet< &'i str >
) -> impl FnOnce( Span< 'i > ) -> PResult< 'i, Decl< &'i str > > + 'a {
  move |input| {
    let (input, name) = lex_token_if( is_identifier )( input )?;

    // the declaration itself starts at indentation 0. *All lexical tokens* of its
    // body must start at a greater indentation (1).
    let body_indent = 1;
    let ctx = PCtx { i: body_indent, dcon_names };
  
    let (input, _) = p_skip_newline( ctx.i )( input )?;
    let (input, t) = lex_token_if( |x| x == ":" || x == "=" )( input )?;
    let (input, _) = p_skip_newline( ctx.i )( input )?;
  
    if *t.fragment( ) == ":" { // type signature
      let (input, y) = p_term_prec( Prec::Arrow, ctx )( input )?;
      Ok( (input, Decl::TypeSig( Sig::new( *name.fragment( ), Epsilon::Rel, y ) ) ) )
    } else { // function definition
      let (input, y) = p_term_prec( Prec::weakest( ), ctx )( input )?;
      Ok( (input, Decl::Def( *name.fragment( ), y ) ) )
    }
  }
}
