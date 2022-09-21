// stdlib imports
use std::fmt::{Display, Formatter};
use std::collections::{HashSet, HashMap};
// local imports
use crate::unbound::{Bind, Name, Subst, FreeName, LocallyNameless, Level};


pub type Type = Term;

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Term {
  /// The type of types (with type-in-type)
  Type,
  /// Variable
  Var( Name ),
  /// Lambda expression
  Lam( Bind< Box< Term > > ),
  /// Function application
  App( Box< Term >, Box< Term > ),
  /// A Pi-type, being a dependent function type: (x: A) -> B
  Pi( Box< Type >, Bind< Box< Type > > ),
  /// Annotated terms ( a : A )
  Ann( Box< Term >, Box< Type > ),
  ///
  TyBool,
  ///
  LitBool( bool ),
  ///
  If( Box< Term >, Box< Term >, Box< Term > ),
  /// The type of a dependent pair. e.g.,
  /// (x, y) : { x : Int | Int }
  Sigma( Box< Type >, Bind< Box< Type > > ),
  /// A pair. e.g., (x,y)
  Prod( Box< Term >, Box< Term > ),
  /// let (x,y) = a in b
  LetPair( Box< Term >, Bind< Bind< Box< Term > > > )
}

impl Term {
  pub fn visit_preorder< T, F >( &self, mut f: F, v: T ) -> T
    where F: FnMut( &Term, T ) -> T + Copy
  {
    match self {
      Term::Type => f( &self, v ),
      Term::Var( _ ) => f( &self, v ),
      Term::Lam( x ) => {
        let v = f( &self, v );
        x.term( ).visit_preorder( f, v )
      },
      Term::App( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::Pi( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.term( ).visit_preorder( f, v )
      },
      Term::Ann( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::TyBool => f( &self, v ),
      Term::LitBool( _ ) => f( &self, v ),
      Term::If( cond, x, y ) => {
        let v = f( &self, v );
        let v = cond.visit_preorder( f, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::Sigma( x, bnd ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        bnd.term( ).visit_preorder( f, v )
      },
      Term::Prod( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::LetPair( x, bnd ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        bnd.term( ).term( ).visit_preorder( f, v )
      }
    }
  }

  /// Returns `true` iff the term references the current bound variable at
  /// de Bruijn index 0.
  pub fn references_bind0( &self ) -> bool {
    fn rec( level: usize, t: &Term ) -> bool {
      match t {
        Term::Type => false,
        Term::Var( Name::Bound( i ) ) => i.de_bruijn_index( ) == level,
        Term::Var( _ ) => false,
        Term::Lam( x ) => rec( level + 1, x.term( ) ),
        Term::App( x, y ) =>
          rec( level, x ) || rec( level, y ),
        Term::Pi( x, y ) => rec( level, x ) || rec( level + 1, y.term( ) ),
        Term::Ann( x, y ) => rec( level, x ) || rec( level, y ),
        Term::TyBool => false,
        Term::LitBool( _ ) => false,
        Term::If( cond, x, y ) => rec( level, cond ) || rec( level, x ) || rec( level, y ),
        Term::Sigma( x, bnd ) => rec( level, x ) || rec( level + 1, bnd.term( ) ),
        Term::Prod( x, y ) => rec( level, x ) || rec( level, y ),
        Term::LetPair( x, bnd ) => rec( level, x ) || rec( level + 2, bnd.term( ).term( ) )
      }
    }

    rec( 0, self )
  }
}

impl Subst< &Term > for Box< Term > {
  fn subst( mut self, n: &Name, t: &Term ) -> Box< Term > {
    // This avoids cloning
    unsafe {
      let ptr: &mut Term = &mut *self;
      let mut x = std::ptr::read( ptr );
      x = x.subst( n, t );
      std::ptr::write( ptr, x );
    }
    self
  }
}

impl Subst< &Term > for Term {
  fn subst( self, name: &Name, t: &Term ) -> Term {
    match self {
      Term::Type => self,
      Term::Var( ref n ) =>
        if n == name {
          t.clone( )
        } else {
          self
        },
      Term::Lam( bnd ) => Term::Lam( bnd.subst( name, t ) ),
      Term::App( x, y ) => Term::App( x.subst( name, t ), y.subst( name, t ) ),
      Term::Pi( x, y ) => Term::Pi( x.subst( name, t ), y.subst( name, t ) ),
      Term::Ann( x, x_type ) => Term::Ann( x.subst( name, t ), x_type.subst( name, t ) ),
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.subst( name, t ), x.subst( name, t ), y.subst( name, t ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.subst( name, t ), bnd.subst( name, t ) ),
      Term::Prod( x, y ) => Term::Prod( x.subst( name, t ), y.subst( name, t ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.subst( name, t ), bnd.subst( name, t ) )
    }
  }
}

impl LocallyNameless for Term {
  // "open" a term. a bound variable, becomes free.
  fn open( self, level: Level, new: &FreeName ) -> Self {
    match self {
      Term::Type => self,
      Term::Var( Name::Free( _ ) ) => self,
      Term::Var( Name::Bound( n ) ) =>
        if n.de_bruijn_index( ) == level.to_usize( ) {
          Term::Var( Name::Free( new.clone( ) ) )
        } else {
          self
        },
      Term::Lam( b ) => Term::Lam( b.open( level, new ) ),
      Term::App( x, y ) => Term::App( x.open( level, new ), y.open( level, new ) ),
      Term::Pi( a, f ) => Term::Pi( a.open( level, new ), f.open( level, new ) ),
      Term::Ann( x, y ) => Term::Ann( x.open( level, new ), y.open( level, new ) ),
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.open( level, new ), x.open( level, new ), y.open( level, new ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.open( level, new ), bnd.open( level, new ) ),
      Term::Prod( x, y ) => Term::Prod( x.open( level, new ), y.open( level, new ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.open( level, new ), bnd.open( level, new ) )
    }
  }

  // "close" a term. a free variable, becomes bound.
  fn close( self, level: Level, old: &FreeName ) -> Self {
    match self {
      Term::Type => self,
      Term::Var( Name::Free( n ) ) =>
        if &n == old {
          Term::Var( Name::Bound( level.to_name( ) ) )
        } else {
          Term::Var( Name::Free( n ) ) // = self
        },
      Term::Var( Name::Bound( _ ) ) => self,
      Term::Lam( b ) => Term::Lam( b.close( level, old ) ),
      Term::App( x, y ) => Term::App( x.close( level, old ), y.close( level, old ) ),
      Term::Pi( a, f ) => Term::Pi( a.close( level, old ), f.close( level, old ) ),
      Term::Ann( x, y ) => Term::Ann( x.close( level, old ), y.close( level, old ) ),
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.close( level, old ), x.close( level, old ), y.close( level, old ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.close( level, old ), bnd.close( level, old ) ),
      Term::Prod( x, y ) => Term::Prod( x.close( level, old ), y.close( level, old ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.close( level, old ), bnd.close( level, old ) )
    }
  }
}

impl Term {
  /// Checks alpha-equivalence
  pub fn aeq( &self, y: &Term ) -> bool {
    match (self, y) {
      (Term::Ann( x, _ ), _) => x.aeq( y ),
      (_, Term::Ann( y, _ )) => self.aeq( y ),
      (Term::Type, Term::Type) => true,
      (Term::Var( x ), Term::Var( y )) => x == y,
      (Term::Lam( x ), Term::Lam( y )) =>
        x.term( ).aeq( y.term( ) ),
      (Term::App( x0, y0 ), Term::App( x1, y1 )) =>
        x0.aeq( x1 ) && y0.aeq( y1 ),
      (Term::Pi( x0, y0 ), Term::Pi( x1, y1 ) ) =>
        x0.aeq( x1 ) && y0.term( ).aeq( y1.term( ) ),
      (Term::TyBool, Term::TyBool ) => true,
      (Term::LitBool( b1 ), Term::LitBool( b2 ) ) => ( b1 == b2 ),
      (Term::If( c1, x1, y1 ), Term::If( c2, x2, y2 ) ) =>
        c1.aeq( c2 ) && x1.aeq( x2 ) && y1.aeq( y2 ),
      (Term::Sigma( x1, bnd1 ), Term::Sigma( x2, bnd2 ) ) =>
        x1.aeq( x2 ) && bnd1.term( ).aeq( bnd2.term( ) ),
      (Term::Prod( x1, y1 ), Term::Prod( x2, y2 ) ) =>
        x1.aeq( x2 ) && y1.aeq( y2 ),
      (Term::LetPair( x1, bnd1 ), Term::LetPair( x2, bnd2 ) ) =>
        x1.aeq( x2 ) && bnd1.term( ).term( ).aeq( bnd2.term( ).term( ) ),
      (_, _) => false
    }
  }

  pub fn prec( &self ) -> Prec {
    match self {
      Term::Type => Prec::Atom,
      Term::Var( _ ) => Prec::Atom,
      Term::Lam( _ ) => Prec::Lambda,
      Term::App( _, _ ) => Prec::App,
      Term::Pi( _, _ ) => Prec::Arrow,
      Term::Ann( _, _ ) => Prec::Colon,
      Term::TyBool => Prec::Atom,
      Term::LitBool( _ ) => Prec::Atom,
      Term::If( _, _, _ ) => Prec::IfThenElse,
      Term::Sigma( _, _ ) => Prec::Atom,
      Term::Prod( _, _ ) => Prec::Atom,
      Term::LetPair( _, _ ) => Prec::IfThenElse
    }
  }
}

pub enum Prec {
  Colon, // weakest
  Arrow,
  Lambda,
  IfThenElse, // also let-binding
  App,
  Atom // Strongest
}

impl Prec {
  pub fn weakest( ) -> Prec {
    Prec::Colon
  }

  /// Returns the next stronger precedence
  pub fn inc( &self ) -> Prec {
    match self {
      Prec::Colon => Prec::Arrow,
      Prec::Arrow => Prec::Lambda,
      Prec::Lambda => Prec::IfThenElse,
      Prec::IfThenElse => Prec::App,
      Prec::App => Prec::Atom,
      Prec::Atom => Prec::Atom // fix point
    }
  }

  pub fn less_than( &self, p: Prec ) -> bool {
    self.val( ) < p.val( )
  }

  /// Converts the `Prec` to some arbitrary numbers, which we use to determine
  /// a partial order between binding strengths.
  fn val( &self ) -> usize {
    match self {
      Prec::Colon      => 0,
      Prec::Arrow      => 1,
      Prec::Lambda     => 2,
      Prec::IfThenElse => 3,
      Prec::App        => 4,
      Prec::Atom       => 5
    }
  }
}

pub const RESERVED: &[&'static str] = &[ "Type", "Bool", "True", "False", "if", "then", "else", "let", "in" ];

/// A builder for `NameEnv`. We want to ensure `reserve` is *not* called after
/// fresh names are dispatched.
/// 
/// Consider the scenario where we receive fresh variable "x", but then reserve
/// "x" as a free variable. We avoid that statically.
pub struct NameEnvBuilder( HashSet< String > );

impl NameEnvBuilder {
  pub fn new( ) -> NameEnvBuilder {
    // Start with language keywords
    let reserved = RESERVED.iter( ).map( |x| (*x).to_owned( ) ).collect( );
    NameEnvBuilder( reserved )
  }

  pub fn reserve( &mut self, n: String ) {
    self.0.insert( n );
  }

  pub fn build( self ) -> NameEnv {
    NameEnv {
      reserved: self.0,
      free_names: HashMap::new( ),
      fresh_idx: 0
    }
  }
}

/// An environment that gives out pretty-printable names. We make all names
/// globally (i.e., within a module) unique.
/// 
/// Use `NameEnvBuilder` to construct it.
pub struct NameEnv {
  /// Previously-used names. These can be language keywords, module-level
  /// definitions (by this env).
  reserved: HashSet< String >,
  free_names: HashMap< usize, String >,
  fresh_idx : usize,
}

impl NameEnv {
  pub fn fresh_name( &mut self ) -> String {
    let idx = self.fresh_idx;
    self.fresh_idx += 1;

    let mut idx_name = str_name( idx );
    // Ensure our generated name was not previously used
    while self.reserved.contains( &idx_name ) {
      let idx = self.fresh_idx;
      self.fresh_idx += 1;
      idx_name = str_name( idx );
    }

    idx_name
  }

  pub fn free_name_string< 'a, 'b: 'a >( &'a mut self, n: &'b FreeName ) -> &'a str {
    match n {
      FreeName::Text( s ) => s,
      FreeName::Num( n ) => self.free_name_num_string( *n )
    }
  }

  /// Internally, we represent some free names with numbers. However, it's nicer
  /// to represent it textually.
  pub fn free_name_num_string< 'a >( &'a mut self, id: usize ) -> &'a str {
    // # Decision: Use `contains_key`
    // 
    // Preferably, we would write:
    // > if let Some( name ) = self.free_names.get( &id ) {
    // >   name
    // > } else {
    // >   let name = self.fresh_name( );
    // >   self.free_names.insert( id, name );
    // >   self.free_names.get( &id ).unwrap( )
    // > }
    // 
    // However, Rust's borrow checker does not like that. Somehow, the immutable
    // borrow in the if-case affects the else-case.
    
    if !self.free_names.contains_key( &id ) {
      let name = self.fresh_name( );
      self.free_names.insert( id, name );
    }

    // assert: self.free_names.contains_key( &id )
    self.free_names.get( &id ).unwrap( ) 
  }
}

/// Like `Display`, but we pass a `NameEnv` along.
pub trait EnvDisplay {
  fn fmt( &self, env: &mut NameEnv, f: &mut Formatter<'_> ) -> std::fmt::Result;
}

impl EnvDisplay for Term {
  fn fmt( &self, env: &mut NameEnv, f: &mut Formatter<'_> ) -> std::fmt::Result {
    fn rec_bracket(
      env: &mut NameEnv,
      bound_names: &mut Vec< String >,
      t: &Term,
      // `prec` is the lowest precedence that requires *no* brackets
      prec: Prec,
      f: &mut Formatter<'_>
    ) -> std::fmt::Result {
      if t.prec( ).less_than( prec ) {
        write!( f, "(" )?;
        rec( env, bound_names, t, f )?;
        write!( f, ")" )
      } else {
        rec( env, bound_names, t, f )
      }
    }
    
    /// We need to propagate an "environment" while printing nested terms.
    /// Which we can do with this function.
    /// 
    /// We also push around a list of "bound names". Whenever a new variable is
    /// bound by a lambda (or pi-type), we extend it for its inner term. After
    /// printing that inner term, we pop it again.
    fn rec(
      env: &mut NameEnv,
      bound_names: &mut Vec< String >,
      t: &Term,
      f: &mut Formatter<'_>
    ) -> std::fmt::Result {
      match t {
        Term::Type =>
          write!( f, "Type" )?,
        Term::Var( Name::Free( n ) ) =>
          write!( f, "{}", env.free_name_string( n ) )?,
        Term::Var( Name::Bound( n ) ) =>
          write!( f, "{}", bound_names[ bound_names.len( ) - 1 - n.de_bruijn_index( ) ] )?,
        Term::Lam( _ ) => {
          let mut t_temp = t;
          let mut num_lambdas = 0;

          write!( f, "\\" )?;
          // true for at least one iteration, by the above matching
          while let Term::Lam( b ) = t_temp {
            if b.term( ).references_bind0( ) {
              let n = env.fresh_name( );
              write!( f, "{} ", n )?;
              bound_names.push( n );
            } else {
              write!( f, "_ " )?;
              bound_names.push( "_".to_owned( ) ) // No name. Not used anyway
            };
            t_temp = b.term( );
            num_lambdas += 1;
          }
          write!( f, ". " )?;

          rec_bracket( env, bound_names, t_temp, Prec::Lambda, f )?;

          for _ in 0..num_lambdas {
            bound_names.pop( );
          }
        },
        Term::App( x, y ) => {
          rec_bracket( env, bound_names, x, Prec::App, f )?;
          write!( f, " " )?;
          rec_bracket( env, bound_names, y, Prec::Atom, f )?;
        },
        // (x : A) -> B
        Term::Pi( a, b ) => {
          let bound_name = 
            if b.term( ).references_bind0( ) {
              let n = env.fresh_name( );
              write!( f, "({} : ", n )?;
              rec_bracket( env, bound_names, a, Prec::Colon, f )?;
              write!( f, ") -> " )?;
              n
            } else {
              rec_bracket( env, bound_names, a, Prec::Arrow.inc( ), f )?;
              write!( f, " -> " )?;
              "".to_owned( ) // no name. because it's not used anyway
            };

          bound_names.push( bound_name );
          rec_bracket( env, bound_names, b.term( ), Prec::Arrow, f )?;
          bound_names.pop( );
        },
        Term::TyBool => write!( f, "Bool" )?,
        Term::LitBool( true )  => write!( f, "True" )?,
        Term::LitBool( false ) => write!( f, "False" )?,
        Term::If( cond, x, y ) => {
          write!( f, "if " )?;
          rec_bracket( env, bound_names, cond, Prec::IfThenElse, f )?;
          write!( f, " then " )?;
          rec_bracket( env, bound_names, x, Prec::IfThenElse, f )?;
          write!( f, " else " )?;
          rec_bracket( env, bound_names, y, Prec::IfThenElse, f )?;
        },
        Term::Sigma( x, bnd ) => {
          let n = env.fresh_name( );

          write!( f, "{{ {} : ", n )?;
          rec_bracket( env, bound_names, x, Prec::weakest( ), f )?;
          write!( f, " | " )?;

          bound_names.push( n );
          rec_bracket( env, bound_names, bnd.term( ), Prec::weakest( ), f )?;
          bound_names.pop( );

          write!( f, " }}" )?;
        },
        Term::Prod( x, y ) => {
          write!( f, "(" )?;
          rec_bracket( env, bound_names, x, Prec::weakest( ), f )?;
          write!( f, "," )?;
          rec_bracket( env, bound_names, y, Prec::weakest( ), f )?;
          write!( f, ")" )?;
        },
        Term::LetPair( x, bnd ) => {
          let n1 = env.fresh_name( );
          let n2 = env.fresh_name( );
          
          write!( f, "let ({},{}) = ", n1, n2 )?;
          rec_bracket( env, bound_names, x, Prec::weakest( ), f )?;
          write!( f, " in " )?;

          bound_names.push( n1 );
          bound_names.push( n2 );
          rec_bracket( env, bound_names, bnd.term( ).term( ), Prec::weakest( ), f )?;
          bound_names.pop( );
          bound_names.pop( );
        },
        Term::Ann( x, y ) => {
          write!( f, "(" )?;
          rec_bracket( env, bound_names, x, Prec::Colon.inc( ), f )?;
          write!( f, " : " )?;
          rec_bracket( env, bound_names, y, Prec::Colon, f )?;
          write!( f, ")" )?;
        }
      }
      Ok( () )
    }

    let mut bound_names: Vec< String > = Vec::new( );
    let res = rec_bracket( env, &mut bound_names, self, Prec::weakest(), f );
    assert!( bound_names.is_empty( ) );
    res
  }
}

// Parameterised over names
#[derive(Debug, Clone)]
pub enum Decl< N = String > {
  /// Type signature
  /// 
  /// Example:
  /// id : (x : Type) -> (y : x) -> x
  TypeSig( N, Type ),
  /// Definition of some name. Must already have a type declaration.
  /// 
  /// Example:
  /// id = \x y . y
  Def( N, Term )
}

impl< N > Decl< N > {
  pub fn is_def( &self ) -> bool {
    match self {
      Decl::Def( _, _ ) => true,
      _ => false
    }
  }
}

impl EnvDisplay for Decl< String > {
  fn fmt( &self, env: &mut NameEnv, f: &mut Formatter<'_> ) -> std::fmt::Result {
    match self {
      Decl::TypeSig( name, t ) => {
        write!( f, "{} : ", name )?;
        t.fmt( env, f )
      },
      Decl::Def( name, t ) => {
        write!( f, "{} = ", name )?;
        t.fmt( env, f )
      }
    }
  }
}

#[derive(Debug)]
pub struct Module {
  pub name : String,
  pub entries : Vec< Decl< String > >
}

impl Display for Module {
  fn fmt( &self, f: &mut Formatter<'_> ) -> std::fmt::Result {
    writeln!( f, "module {} where", self.name )?;
    writeln!( f, "" )?;
    
    let mut env_builder = NameEnvBuilder::new( );
    // Rule out all the free names
    for decl in &self.entries {
      match decl {
        Decl::TypeSig( name, t ) => {
          env_builder.reserve( name.to_owned( ) );
          env_builder = t.visit_preorder( |t2, mut env_builder| {
            match t2 {
              Term::Var( Name::Free( FreeName::Text( n ) ) ) =>
                env_builder.reserve( n.to_owned( ) ),
              _ => { }
            }
            env_builder
          }, env_builder );
        },
        Decl::Def( name, t ) => {
          env_builder.reserve( name.to_owned( ) );
          env_builder = t.visit_preorder( |t2, mut env_builder| {
            match t2 {
              Term::Var( Name::Free( FreeName::Text( n ) ) ) =>
                env_builder.reserve( n.to_owned( ) ),
              _ => { }
            }
            env_builder
          }, env_builder );
        }
      }
    }
    
    let mut env = env_builder.build( );

    for decl in &self.entries {
      decl.fmt( &mut env, f )?;
      writeln!( f )?;

      if decl.is_def( ) {
        writeln!( f, "" )?;
      }
    }

    Ok( () )
  }
}

const ALPHABET: [char; 26] =
  [ 'a','b','c','d','e','f','g','h','i','j'
  , 'k', 'l','m','n','o','p','q','r','s','t'
  , 'u', 'v','w','x','y','z' ];

/// Converts numbers (bijectively) to textual names.
/// 
/// Intuition:
/// [0 -> a, .., 25 -> z, 26 -> aa, .., 51 -> az, ... ]
fn str_name( mut n: usize ) -> String {
  let mut s: String = String::new( );

  while n >= ALPHABET.len( ) {
    s.push( ALPHABET[ n % ALPHABET.len( ) ] );
    n = n / ALPHABET.len( ) - 1;
  }
  s.push( ALPHABET[ n ] );

  s.chars( ).rev( ).collect( )
}
