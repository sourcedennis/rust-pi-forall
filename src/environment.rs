
// stdlib imports
use std::slice::Iter;
// local imports
use crate::unbound::FreeName;
use crate::syntax::{Term, Decl, Sig};


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

  /// Make all declarations in the context *relevant*.
  pub fn demote_all( &mut self ) {
    for decl in &mut self.0 {
      match decl {
        Decl::Def( _, _ ) => { },
        Decl::TypeSig( sig ) => sig.demote( )
      }
    }
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Sig< FreeName > > {
    map_maybe_last( |x|
      x.type_sig( )
        .filter( |sig| sig.name == *n ),
      &self.0
    )
  }

  pub fn lookup_def< 'a >( &'a self, n: &FreeName ) -> Option< &'a Term > {
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
  hints : Vec< Sig< String > >
}

#[allow(dead_code)]
impl Env {
  pub fn new( ) -> Env {
    Env {
      ctx: Ctx::new( ),
      hints: Vec::new( )
    }
  }
  /// Make all declarations in the context *relevant*.
  pub fn demote_all( &mut self ) {
    self.ctx.demote_all( );
  }

  pub fn lookup_hint< 'a >( &'a self, n: &str ) -> Option< &'a Sig< String > > {
    map_maybe_last( |sig|
      if sig.name == *n {
        Some( sig )
      } else {
        None
      },
      &self.hints
    )
  }

  pub fn lookup_type( &self, n: &FreeName ) -> Option< &Sig< FreeName > > {
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

  pub fn add_hint( &mut self, sig: Sig< String > ) {
    self.hints.push( sig );
  }
}

impl From< Env > for Ctx {
  fn from( env: Env ) -> Ctx {
    env.ctx
  }
}

pub type ErrMsg = String;

/// Utility function. (Replaces `unless` on the typechecking monad)
pub fn assert_res( b: bool, msg: ErrMsg ) -> Result< (), ErrMsg > {
  if b {
    Ok( () )
  } else {
    Err( msg )
  }
}
