extern crate nom;

// external library imports
use nom::{
  IResult,
  bytes::complete::{tag, take_while, take_until, take_while1},
  combinator::{opt, recognize, verify, map},
  sequence::{delimited, separated_pair, preceded},
  error::{Error, ErrorKind, ParseError},
  branch::alt, multi::{many1_count, separated_list1, many1, many0}
};
use nom_locate::LocatedSpan;
// local imports
use crate::{unbound::{FreeName, Name, Bind}, syntax::{Epsilon, Arg, Sig}};
use crate::syntax::{Module, Decl, Term, Prec};
use crate::pretty_print::{RESERVED};


type Span< 'a > = LocatedSpan< &'a str >;

// # Lexer

#[derive(Debug, PartialEq)]
pub enum BlockElement< T > {
  NewBlock,
  Word( T ),
  Symbol( T )
}

/// Discards the output of a parser. (i.e., it becomes `()`)
fn discard< I, O, F >(
  f: F
) -> impl FnMut( I ) -> IResult< I, () >
where
  F: FnMut( I ) -> IResult< I, O >
{
  map( f, |_| () )
}

/// Parses: [a-zA-Z] [a-zA-Z0-9]*
///   (also parses other Unicode Alphabetic chars, that's ok)
#[must_use]
fn lex_word( input: Span ) -> IResult< Span, () > {
  // this is actually: [a-zA-Z]* [a-zA-Z0-9]* but ambiguity is irrelevant
  let (input, _) = take_while1( |c:char| c.is_alphabetic( ) || c == '_' || c == '\'' )( input )?;
  let (input, _) = take_while( |c:char| c.is_alphanumeric( ) || c == '_' || c == '\'' )( input )?;
  Ok( (input, ()) )
}

/// parses: \ ( ) -> : .
fn lex_symbol( input: Span ) -> IResult< Span, () > {
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

fn lex_line_comment( input: Span ) -> IResult< Span, () > {
  let (input, _) = tag( "--" )( input )?;
  let (input, _) = take_until( "\n" )( input )?;
  // Actually consume the "\n" value
  let (input, _) = opt( tag( "\n" ) )( input )?;
  Ok( (input, ()) )
}

fn lex_block_comment( input: Span ) -> IResult< Span, () > {
  // no such thing as nested comments
  let (input, _) = tag( "{-" )( input )?;
  let (input, _) = take_until( "-}" )( input )?;
  let (input, _) = tag( "-}" )( input )?;
  Ok( (input, ()) )
}

/// 
fn lex_padding( input: Span ) -> IResult< Span, () > {
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

/// Behold: A super-weird lexer.
/// 
/// We consider two indentation levels: zero and non-zero. An indentation of
/// zero starts a new block. Altogether ignores comments, as if they're
/// whitespace.
pub fn lex( mut input: Span ) -> IResult< Span, BlockElement< &str > > {
  if let Ok( (input2, _) ) = lex_padding( input ) { // Ignore garbage
    if input2.is_empty( ) {
      return Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Eof)));
    } else if input.get_utf8_column( ) != 1 && input2.get_utf8_column( ) == 1 {
      // it wasn't at the start of a new line before, but it is now.
      // so, it's a new block
      return Ok( (input2, BlockElement::NewBlock) );
    } else {
      input = input2;
    }
  }

  alt(
    (
      map( recognize( lex_word ), |x| BlockElement::Word( *x.fragment( ) ) ),
      map( recognize( lex_symbol ), |x| BlockElement::Symbol( *x.fragment( ) ) )
    )
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


// # Parse

#[must_use]
pub fn lex_word_if< F >(
  cond: F
) -> impl Fn( Span ) -> IResult< Span, &str >
where
  F: Fn( &str ) -> bool
{
  move |input| {
    match lex( input ) {
      Ok( ( input2, BlockElement::Word( x ) ) ) =>
        if cond( x ) {
          Ok( ( input2, x ) )
        } else {
          Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag)))
        },
      Ok( ( input2, _ ) ) =>
        Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag))),
      Err( err ) =>
        Err( err )
    }
  }
}

#[must_use]
pub fn lex_symbol_if< F >(
  cond: F
) -> impl Fn( Span ) -> IResult< Span, &str >
where
  F: Fn( &str ) -> bool
{
  move |input| {
    match lex( input ) {
      Ok( ( input2, BlockElement::Symbol( x ) ) ) =>
        if cond( x ) {
          Ok( ( input2, x ) )
        } else {
          Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag)))
        },
      Ok( ( input2, _ ) ) =>
        Err(nom::Err::Error(Error::from_error_kind(input2, ErrorKind::Tag))),
      Err( err ) =>
        Err( err )
    }
  }
}

pub fn p_module( input: Span ) -> IResult< Span, Module > {
  let (input, _) = lex_word_if( |x| x == "module" )( input )?;
  let (input, name) = lex_word_if( |_| true )( input )?;
  let (input, _) = lex_word_if( |x| x == "where" )( input )?;

  let (input, _) = verify( lex, |x| *x == BlockElement::NewBlock )( input )?;

  let (input, entries) =
    separated_list1(
      verify( lex, |x| *x == BlockElement::NewBlock ),
      p_decl
    )( input )?;

  Ok( (input, Module { name: name.to_owned( ), entries } ) )
}

pub fn p_identifier( input: Span ) -> IResult< Span, &str > {
  lex_word_if( |x| !RESERVED.contains( &x ) )( input )
}

fn p_term_prec< 'a >( prec: Prec )
  -> impl Fn( Span< 'a > ) -> IResult< Span< 'a >, Term > {

  match prec {
    Prec::Colon      => p_term_colon,
    Prec::Lambda     => p_term_lambda,
    Prec::Arrow      => p_term_arrow,
    Prec::IfThenElse => p_term_iflet,
    Prec::Equality   => p_equality,
    Prec::App        => p_term_app,
    Prec::Atom       => p_term_atom
  }
}

/// Parses terms with precedence 4. (Weakest)
/// <term4> := <term3> [':' <term4>]
/// 
/// So, in theory, we can have an expression:
/// > f : Nat -> Nat : Set
/// which parses as:
/// > f : (Nat -> Nat : Set)
pub fn p_term_colon< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, x) = p_term_prec( Prec::Colon.inc( ) )( input )?;
  let (input, t) = opt( lex_symbol_if( |x| x == ":" ) )( input )?;

  if t.is_some( ) {
    let (input, y) = p_term_prec( Prec::Colon )( input )?;
    Ok( ( input, Term::Ann( Box::new( x ), Box::new( y ) ) ) )
  } else {
    Ok( (input, x) )
  }
}

/// Parse:
/// <term> := <term+1> '->' <term>
///         | '[' <term> ']' '->' <term>
///         | '(' <identifier> ':' <term> ')' '->' <term>
///         | '[' <identifier> ':' <term> ']' '->' <term>
///         | <term+1>
pub fn p_term_arrow< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  /// Parses: '(' <identifier> ':' <term> ')'
  fn p_named_type< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, (&'a str, Term) > {
    delimited(
      lex_symbol_if( |x| x == "(" ),
      separated_pair(
        p_identifier,
        lex_symbol_if( |x| x == ":" ),
        p_term_prec( Prec::Arrow )
      ),
      lex_symbol_if( |x| x == ")" )
    )( input )
  }

  /// Parses: '[' <identifier> ':' <term> ']'
  fn p_irr_named_type< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, (&'a str, Term) > {
    delimited(
      lex_symbol_if( |x| x == "[" ),
      separated_pair( p_identifier, lex_symbol_if( |x| x == ":" ), p_term_prec( Prec::Arrow ) ),
      lex_symbol_if( |x| x == "]" )
    )( input )
  }

  /// Parses: '[' <term> ']'
  fn p_irr_type< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
    delimited(
      lex_symbol_if( |x| x == "[" ),
      p_term_prec( Prec::Arrow ),
      lex_symbol_if( |x| x == "]" )
    )( input )
  }

  let (input, (lhs_name, eps, lhs_term)) =
    alt(
      (
        map( p_named_type, |(n,t)| (Some(n), Epsilon::Rel, t) ),
        map( p_irr_named_type, |(n,t)| (Some(n), Epsilon::Irr, t) ),
        map( p_irr_type, |t| (None, Epsilon::Irr, t) ),
        map( p_term_prec( Prec::Arrow.inc( ) ), |t| (None, Epsilon::Rel, t) )
      )
    )( input )?;

  let (input, m_rhs) =
    opt(
      preceded(
        lex_symbol_if( |x| x == "->" ),
        p_term_prec( Prec::Arrow )
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

/// Parse: <eps-identifier> := <identifier>
///                          | '[' <identifier> ']'
fn p_eps_identifier< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, (Epsilon, &'a str) > {
  alt(
    (
      map( p_identifier, |x| (Epsilon::Rel, x) ),
      map(
        delimited(
          lex_symbol_if( |x| x == "[" ),
          p_identifier,
          lex_symbol_if( |x| x == "]" )
        ),
        |x| (Epsilon::Irr, x)
      )
    )
  )( input )
}

/// Parse:
/// <term> := '\' <eps-identifier>* '.' <term>
///         | <term+1>
pub fn p_term_lambda< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, m_lambda) = opt( lex_symbol_if( |x| x == "\\" ) )( input )?;

  if m_lambda.is_some( ) {
    let (input, identifiers) = many1( p_eps_identifier )( input )?;

    let (input, _) = lex_symbol_if( |x| x == "." )( input )?;
    
    let (input, mut body) = p_term_prec( Prec::Lambda )( input )?;

    for (eps, id) in identifiers.into_iter( ).rev( ) {
      let name = FreeName::from( FreeName::Text( id.to_owned( ) ) );
      body = Term::Lam( eps, Bind::bind( &name, Box::new( body ) ) );
    }

    Ok( (input, body) )
  } else {
    p_term_prec( Prec::Lambda.inc( ) )( input )
  }
}

pub fn p_term_iflet< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  alt(
    (
      p_ifthenelse,
      p_letin,
      p_subst,
      p_term_prec( Prec::IfThenElse.inc( ) )
    )
  )( input )
}

/// Parse:
/// <term> := 'if' <term> 'then' <term> 'else' <term>
///         | <term+1>
/// 
/// Remarkably, we can have nested if-then-else statements inside any of its
/// three arguments, as no ambiguity occurs.
pub fn p_ifthenelse< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _) = lex_word_if( |x| x == "if" )( input )?;
  let (input, cond) = p_term_prec( Prec::IfThenElse )( input )?;
  let (input, _) = lex_word_if( |x| x == "then" )( input )?;
  let (input, if_case) = p_term_prec( Prec::IfThenElse )( input )?;
  let (input, _) = lex_word_if( |x| x == "else" )( input )?;
  let (input, else_case) = p_term_prec( Prec::IfThenElse )( input )?;

  Ok( (input, Term::If( Box::new( cond ), Box::new( if_case ), Box::new( else_case ) ) ) )
}

pub fn p_letin< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _) = lex_word_if( |x| x == "let" )( input )?;
  let (input, _) = lex_symbol_if( |x| x == "(" )( input )?;
  let (input, x_name) = p_identifier( input )?;
  let (input, _) = lex_symbol_if( |x| x == "," )( input )?;
  let (input, y_name) = p_identifier( input )?;
  let (input, _) = lex_symbol_if( |x| x == ")" )( input )?;
  let (input, _) = lex_symbol_if( |x| x == "=" )( input )?;
  let (input, scrut) = p_term_prec( Prec::IfThenElse.inc( ) )( input )?;
  let (input, _) = lex_word_if( |x| x == "in" )( input )?;
  let (input, body) = p_term_prec( Prec::IfThenElse )( input )?;

  let bnd1 = Bind::bind( &FreeName::Text( y_name.to_string( ) ), Box::new( body ) );
  let bnd2 = Bind::bind( &FreeName::Text( x_name.to_string( ) ), bnd1 );

  Ok( (input, Term::LetPair( Box::new( scrut ), bnd2 ) ) )
}

/// Parse: <term> := 'subst' <term+1> 'by' <term+1>
pub fn p_subst< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _)  = lex_word_if( |x| x == "subst" )( input )?;
  let (input, x)  = p_term_prec( Prec::IfThenElse.inc( ) )( input )?;
  let (input, _)  = lex_word_if( |x| x == "by" )( input )?;
  let (input, pf) = p_term_prec( Prec::IfThenElse.inc( ) )( input )?;

  Ok( (input, Term::Subst( Box::new( x ), Box::new( pf ) ) ) )
}

/// Parse: <term> := <term+1> '=' <term+1>
///                | <term+1>
pub fn p_equality< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, x) = p_term_prec( Prec::Equality.inc( ) )( input )?;

  if let Ok( (input, _) ) = lex_symbol_if( |x| x == "=" )( input ) {
    let (input, y) = p_term_prec( Prec::Equality.inc( ) )( input )?;
    Ok( (input, Term::TyEq( Box::new( x ), Box::new( y ) ) ) )
  } else {
    Ok( (input, x) )
  }
}

pub fn p_arg< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Arg > {
  alt(
    (
      map( p_term_prec( Prec::App.inc( ) ), |x| Arg::new( Epsilon::Rel, x ) ),
      map(
        delimited(
          lex_symbol_if( |x| x == "[" ),
          p_term_prec( Prec::weakest( ) ),
          lex_symbol_if( |x| x == "]" )
        ),
        |x| Arg::new( Epsilon::Irr, x ) ),
    )
  )( input )
}

/// Parse: <term> := <term+1>+
pub fn p_term_app< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, mut term) = p_term_prec( Prec::App.inc( ) )( input )?;

  let (input, args) = many0( p_arg )( input )?;

  for arg in args {
    term = Term::App( Box::new( term ), Box::new( arg ) );
  }
  Ok( (input, term) )
}

pub fn p_term_atom< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  alt(
    (
      map( lex_word_if( |x| x == "Type" ), |_| Term::Type ),
      map( lex_word_if( |x| x == "Bool" ), |_| Term::TyBool ),
      map( lex_word_if( |x| x == "True" ), |_| Term::LitBool( true ) ),
      map( lex_word_if( |x| x == "False" ), |_| Term::LitBool( false ) ),
      map( lex_symbol_if( |x| x == "()" ), |_| Term::LitUnit ),
      map( lex_word_if( |x| x == "Unit" ), |_| Term::TyUnit ),
      map( lex_word_if( |x| x == "Refl" ), |_| Term::Refl ),
      map( p_identifier, |x| Term::Var( Name::Free( FreeName::Text( x.to_owned( ) ) ) ) ),
      p_contra,
      p_sigma_type,
      p_tuple
    )
  )( input )
}

/// Parse:
/// <term> := '(' <term-w> ')'
///         | '(' <term-w> ',' <term-w> ')'
pub fn p_tuple< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _) = lex_symbol_if( |x| x == "(" )( input )?;
  let (input, v1) = p_term_prec( Prec::weakest( ) )( input )?;

  let (input, m_v2) =
    opt( preceded(
      lex_symbol_if( |x| x == "," ),
      p_term_prec( Prec::weakest( ) )
    ) )( input )?;

  let (input, _) = lex_symbol_if( |x| x == ")" )( input )?;

  if let Some( v2 ) = m_v2 {
    Ok( ( input, Term::Prod( Box::new( v1 ), Box::new( v2 ) ) ) )
  } else {
    Ok( ( input, v1 ) )
  }
}

fn p_contra< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _) = lex_word_if( |x| x == "contra" )( input )?;
  let (input, x) = p_term_prec( Prec::Atom )( input )?;
  Ok( ( input, Term::Contra( Box::new( x ) ) ) )
}

pub fn p_sigma_type< 'a >( input: Span< 'a > ) -> IResult< Span< 'a >, Term > {
  let (input, _)     = lex_symbol_if( |x| x == "{" )( input )?;
  let (input, name)  = p_identifier( input )?;
  let (input, _)     = lex_symbol_if( |x| x == ":" )( input )?;
  let (input, a)     = p_term_prec( Prec::weakest( ) )( input )?;
  let (input, _)     = lex_symbol_if( |x| x == "|" )( input )?;
  let (input, b)     = p_term_prec( Prec::weakest( ) )( input )?;
  let (input, _)     = lex_symbol_if( |x| x == "}" )( input )?;

  Ok( (input, Term::Sigma( Box::new( a ), Bind::bind( &FreeName::Text( name.to_owned( ) ), Box::new( b ) ) ) ) )
}

pub fn p_decl( input: Span ) -> IResult< Span, Decl< String > > {
  let (input, name) = lex_word_if( |_| true )( input )?;
  let (input, t) = lex_symbol_if( |x| x == ":" || x == "=" )( input )?;

  if t == ":" { // type signature
    let (input, y) = p_term_prec( Prec::Arrow )( input )?;
    Ok( (input, Decl::TypeSig( Sig::new( name.to_owned( ), Epsilon::Rel, y ) ) ) )
  } else { // function definition
    let (input, y) = p_term_prec( Prec::weakest( ) )( input )?;
    Ok( (input, Decl::Def( name.to_owned( ), y ) ) )
  }
}
