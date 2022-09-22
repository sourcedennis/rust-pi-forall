
// stdlib imports
use std::collections::HashMap;
use std::collections::hash_map::{Keys, Iter};
// local imports
use crate::unbound::FreeName;
use crate::syntax::{Term, Type};


/// Definitions that have been typechecked
/// 
/// We store both types and terms. Terms are sometimes required when expanding
/// their definitions when used elsewhere. Terms can be missing.
#[derive(Clone, Debug)]
pub struct Ctx( HashMap< FreeName, (Option< Term >, Type) > );

impl Ctx {
  pub fn new( ) -> Ctx {
    Ctx( HashMap::new( ) )
  }

  pub fn names< 'a >( &'a self ) -> Keys<'a, FreeName, (Option< Term >, Type)> {
    self.0.keys( )
  }

  pub fn iter< 'a >( &'a self ) -> Iter<'a, FreeName, (Option< Term >, Type)> {
    self.0.iter( )
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Type > {
    if let Some( ( _, t_type ) ) = self.0.get( n ) {
      Some( t_type )
    } else {
      None
    }
  }

  pub fn lookup_def( &self, n: &FreeName ) -> Option< &Term > {
    if let Some( ( Some( t ), _ ) ) = self.0.get( n ) {
      Some( t )
    } else {
      None
    }
  }

  ///
  /// Warning: This overrides the previous definition with the same name.
  pub fn extend( &mut self, n: FreeName, term: Option< Term >, term_type: Type ) {
    self.0.insert( n, (term, term_type) );
  }
}


/// An environment used during typechecking. It contains both type-checked
/// terms with their types, and (unchecked) type hints that were obtained from
/// the source.
#[derive(Clone, Debug)]
pub struct Env {
  /// Definitions that have been typechecked
  ctx  : Ctx,

  /// Type hints provided in the source, e.g.:
  /// f : Nat -> Nat
  hints : HashMap< FreeName, Type >
}

#[allow(dead_code)]
impl Env {
  pub fn new( ) -> Env {
    Env {
      ctx: Ctx::new( ),
      hints: HashMap::new( )
    }
  }

  pub fn lookup_hint( &self, n: &FreeName ) -> Option< &Type > {
    self.hints.get( n )
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Type > {
    self.ctx.lookup_type( n )
  }

  pub fn lookup_def( &self, n: &FreeName ) -> Option< &Term > {
    self.ctx.lookup_def( n )
  }

  ///
  /// Warning: This overrides the previous definition with the same name.
  pub fn extend( &mut self, n: FreeName, term: Term, term_type: Type ) {
    self.ctx.extend( n, Some( term ), term_type );
  }

  ///
  /// Warning: This overrides the previous definition with the same name.
  pub fn extend_type( &mut self, n: FreeName, term_type: Type ) {
    self.ctx.extend( n, None, term_type );
  }

  pub fn add_hint( &mut self, n: FreeName, t: Type ) {
    self.hints.insert( n, t );
  }
}

impl From< Env > for Ctx {
  fn from( env: Env ) -> Ctx {
    env.ctx
  }
}
