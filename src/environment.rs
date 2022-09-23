
use std::slice::Iter;

// stdlib imports
// local imports
use crate::unbound::FreeName;
use crate::syntax::{Term, Type, Decl};


/// Definitions that have been typechecked
/// 
/// We store both types and terms. Terms are sometimes required when expanding
/// their definitions when used elsewhere. Terms can be missing.
#[derive(Clone, Debug)]
pub struct Ctx( Vec< Decl< FreeName > > );

fn map_maybe_last< A, B, F >( f: F, xs: &[A] ) -> Option< &B >
where
  F: Fn( &A ) -> Option< &B >
{
  
  for x in xs.iter( ).rev( ) {
    if let Some( y ) = f( x ) {
      return Some( y );
    }
  }
  None
}

impl Ctx {
  pub fn new( ) -> Ctx {
    Ctx( Vec::new( ) )
  }

  pub fn iter< 'a >( &'a self ) -> Iter<'a, Decl<FreeName>> {
    self.0.iter( )
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Type > {
    map_maybe_last( |x|
      x.type_sig( )
        .filter( |(name, _)| *name == n )
        .map( |(_, ty)| ty ),
      &self.0
    )
  }

  pub fn lookup_def( &self, n: &FreeName ) -> Option< &Term > {
    map_maybe_last( |x|
      x.def( )
        .filter( |(name, _)| *name == n )
        .map( |(_, ty)| ty ),
      &self.0
    )
  }

  ///
  /// Warning: This overrides the previous definition with the same name.
  pub fn extend( &mut self, decl: Decl< FreeName > ) {
    self.0.push( decl );
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
  hints : Vec< (FreeName, Type) >
}

#[allow(dead_code)]
impl Env {
  pub fn new( ) -> Env {
    Env {
      ctx: Ctx::new( ),
      hints: Vec::new( )
    }
  }

  pub fn lookup_hint( &self, n: &FreeName ) -> Option< &Type > {
    map_maybe_last( |(name, t)|
      if name == n {
        Some( t )
      } else {
        None
      },
      &self.hints
    )
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Type > {
    self.ctx.lookup_type( n )
  }

  pub fn lookup_def( &self, n: &FreeName ) -> Option< &Term > {
    self.ctx.lookup_def( n )
  }

  ///
  /// Warning: This overrides the previous definition with the same name.
  pub fn extend( &mut self, decl: Decl< FreeName > ) {
    self.ctx.extend( decl );
  }

  pub fn add_hint( &mut self, n: FreeName, t: Type ) {
    self.hints.push( (n, t) );
  }
}

impl From< Env > for Ctx {
  fn from( env: Env ) -> Ctx {
    env.ctx
  }
}
