
use std::{fmt::{Formatter, Display}, collections::{HashMap, HashSet}};

// stdlib imports
// local imports
use crate::unbound::{Name, FreeName};
use crate::syntax::*;
use crate::environment::Ctx;


pub const RESERVED: &[&'static str] =
  &[ "Type", "Bool", "True", "False",
     "if", "then", "else", "let", "in",
     "Unit", "Refl", "subst", "by", "contra"
    ];

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
        Term::Lam( _, _ ) => {
          let mut t_temp = t;
          let mut num_lambdas = 0;

          write!( f, "\\" )?;
          // true for at least one iteration, by the above matching
          while let Term::Lam( eps, b ) = t_temp {
            if b.term( ).references_bind0( ) {
              let n = env.fresh_name( );
              if *eps == Epsilon::Irr {
                write!( f, "[{}] ", n )?;
              } else {
                write!( f, "{} ", n )?;
              }
              bound_names.push( n );
            } else {
              if *eps == Epsilon::Irr {
                write!( f, "[_] " )?;
              } else {
                write!( f, "_ " )?;
              }
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
          if y.eps == Epsilon::Irr {
            write!( f, "[" )?;
            rec_bracket( env, bound_names, &y.term, Prec::weakest(), f )?;
            write!( f, "]" )?;
          } else {
            rec_bracket( env, bound_names, &y.term, Prec::Atom, f )?;
          }
        },
        // (x : A) -> B
        Term::Pi( eps, a, b ) => {
          let bound_name = 
            if b.term( ).references_bind0( ) {
              let n = env.fresh_name( );
              if *eps == Epsilon::Irr {
                write!( f, "[{} : ", n )?;
                rec_bracket( env, bound_names, a, Prec::Colon, f )?;
                write!( f, "] -> " )?;
              } else {
                write!( f, "({} : ", n )?;
                rec_bracket( env, bound_names, a, Prec::Colon, f )?;
                write!( f, ") -> " )?;
              }
              n
            } else {
              if *eps == Epsilon::Irr {
                write!( f, "[" )?;
                rec_bracket( env, bound_names, a, Prec::Arrow.inc( ), f )?;
                write!( f, "]" )?;
              } else {
                rec_bracket( env, bound_names, a, Prec::Arrow.inc( ), f )?;
              }
              write!( f, " -> " )?;
              "".to_owned( ) // no name. because it's not used anyway
            };

          bound_names.push( bound_name );
          rec_bracket( env, bound_names, b.term( ), Prec::Arrow, f )?;
          bound_names.pop( );
        },
        Term::TyUnit => write!( f, "Unit" )?,
        Term::LitUnit => write!( f, "()" )?,
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
          rec_bracket( env, bound_names, x, Prec::IfThenElse.inc( ), f )?;
          write!( f, " in " )?;

          bound_names.push( n1 );
          bound_names.push( n2 );
          rec_bracket( env, bound_names, bnd.term( ).term( ), Prec::IfThenElse, f )?;
          bound_names.pop( );
          bound_names.pop( );
        },
        Term::TyEq( x, y ) => {
          rec_bracket( env, bound_names, x, Prec::Equality.inc( ), f )?;
          write!( f, " = " )?;
          rec_bracket( env, bound_names, y, Prec::Equality.inc( ), f )?;
        },
        Term::Refl => {
          write!( f, "Refl" )?;
        },
        Term::Subst( x, pf ) => {
          write!( f, "subst " )?;
          rec_bracket( env, bound_names, x, Prec::IfThenElse.inc( ), f )?;
          write!( f, " by " )?;
          rec_bracket( env, bound_names, pf, Prec::IfThenElse.inc( ), f )?;
        },
        Term::Contra( x ) => {
          write!( f, "contra " )?;
          rec_bracket( env, bound_names, x, Prec::Atom, f )?;
        }
        Term::Ann( x, y ) => {
          rec_bracket( env, bound_names, x, Prec::Colon.inc( ), f )?;
          write!( f, " : " )?;
          rec_bracket( env, bound_names, y, Prec::Colon, f )?;
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

impl EnvDisplay for Decl< String > {
  fn fmt( &self, env: &mut NameEnv, f: &mut Formatter<'_> ) -> std::fmt::Result {
    match self {
      Decl::TypeSig( sig ) => {
        write!( f, "{} : ", sig.name )?;
        sig.ttype.fmt( env, f )
      },
      Decl::Def( name, t ) => {
        write!( f, "{} = ", name )?;
        t.fmt( env, f )
      }
    }
  }
}

impl Display for Module {
  fn fmt( &self, f: &mut Formatter<'_> ) -> std::fmt::Result {
    writeln!( f, "module {} where", self.name )?;
    writeln!( f, "" )?;
    
    let mut env_builder = NameEnvBuilder::new( );
    // Rule out all the free names
    for decl in &self.entries {
      match decl {
        Decl::TypeSig( sig ) => {
          env_builder.reserve( sig.name.to_owned( ) );
          env_builder = sig.ttype.visit_preorder( |t2, mut env_builder| {
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

impl Display for Ctx {
  fn fmt( &self, f: &mut Formatter<'_> ) -> std::fmt::Result {
    let mut env_builder = NameEnvBuilder::new( );

    for decl in self.iter( ) {
      if let FreeName::Text( n ) = decl.name( ) {
        env_builder.reserve( n.clone( ) );
      }
    }

    let mut name_env = env_builder.build( );

    for decl in self.iter( ) {
      match decl {
        Decl::Def( name, term ) => {
          write!( f, "{} = ", name_env.free_name_string( name ) )?;
          term.fmt( &mut name_env, f )?;
          writeln!( f )?;
        },
        Decl::TypeSig( sig ) => {
          write!( f, "{} : ", name_env.free_name_string( &sig.name ) )?;
          sig.ttype.fmt( &mut name_env, f )?;
          writeln!( f )?;
        }
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
