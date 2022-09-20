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
  Ann( Box< Term >, Box< Type > )
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
      }
    }

    rec( 0, self )
  }
}

impl Subst< &Term > for Box< Term > {
  fn subst( mut self, n: Name, t: &Term ) -> Box< Term > {
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
  fn subst( self, name: Name, t: &Term ) -> Term {
    match &self {
      Term::Type => self,
      Term::Var( n ) =>
        if *n == name {
          t.clone( )
        } else {
          self
        },
      Term::Lam( bnd ) => Term::Lam( bnd.clone( ).subst( name, t ) ),
      Term::App( x, y ) => Term::App( x.clone( ).subst( name.clone( ), t ), y.clone( ).subst( name, t ) ),
      Term::Pi( x, y ) => Term::Pi( x.clone( ).subst( name.clone( ), t ), y.clone( ).subst( name, t ) ),
      Term::Ann( x, x_type ) => Term::Ann( x.clone( ).subst( name.clone( ), t ), x_type.clone( ).subst( name, t ) )
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
      Term::Ann( x, y ) => Term::Ann( x.open( level, new ), y.open( level, new ) )
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
      Term::Ann( x, y ) => Term::Ann( x.close( level, old ), y.close( level, old ) )
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
      (_, _) => false
    }
  }
}

/// A builder for `NameEnv`. We want to ensure `reserve` is *not* called after
/// fresh names are dispatched.
/// 
/// Consider the scenario where we receive fresh variable "x", but then reserve
/// "x" as a free variable. We avoid that statically.
pub struct NameEnvBuilder( HashSet< String > );

impl NameEnvBuilder {
  pub fn new( ) -> NameEnvBuilder {
    // Start with language keywords
    let reserved = HashSet::from( [ "Type".to_owned( ) ] );
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
      f: &mut Formatter<'_>,
      needs_brackets: bool // TODO: Deal with precedence
    ) -> std::fmt::Result {
      match t {
        Term::Type =>
          write!( f, "Type" )?,
        Term::Var( Name::Free( n ) ) =>
          write!( f, "{}", env.free_name_string( n ) )?,
        Term::Var( Name::Bound( n ) ) =>
          write!( f, "{}", bound_names[ bound_names.len( ) - 1 - n.de_bruijn_index( ) ] )?,
        Term::Lam( _ ) => {
          if needs_brackets {
            write!( f, "(" )?;
          }

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

          rec( env, bound_names, t_temp, f, false )?;

          for _ in 0..num_lambdas {
            bound_names.pop( );
          }

          if needs_brackets {
            write!( f, ")" )?;
          }
        },
        Term::App( x, y ) => {
          rec( env, bound_names, x, f, true )?;
          write!( f, " " )?;
          rec( env, bound_names, y, f, true )?;
        },
        // (x : A) -> B
        Term::Pi( a, b ) => {
          if needs_brackets { // TODO: Deal with precedence
            write!( f, "(" )?;
          }

          let bound_name = 
            if b.term( ).references_bind0( ) {
              let n = env.fresh_name( );
              write!( f, "({} : ", n )?;
              rec( env, bound_names, a, f, false )?;
              write!( f, ") -> " )?;
              n
            } else {
              rec( env, bound_names, a, f, true )?;
              write!( f, " -> " )?;
              "".to_owned( ) // no name. because it's not used anyway
            };

          bound_names.push( bound_name );
          rec( env, bound_names, b.term( ), f, false )?;
          bound_names.pop( );

          if needs_brackets { // TODO: Deal with precedence
            write!( f, ")" )?;
          }
        },
        Term::Ann( x, y ) => {
          write!( f, "(" )?;
          rec( env, bound_names, x, f, false )?;
          write!( f, " : " )?;
          rec( env, bound_names, y, f, false )?;
          write!( f, ")" )?;
        }
      }
      Ok( () )
    }

    let mut bound_names: Vec< String > = Vec::new( );
    let res = rec( env, &mut bound_names, self, f, false );
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
