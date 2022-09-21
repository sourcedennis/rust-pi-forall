///! A simple replacement for Haskell's Unbound package, which is used in the
///! pi-forall reference implementation.
///!
///! We strip away all generic programming and Unbound's "patterns", which are
///! major contributions of its paper:
///!
///! "Binders Unbound" by S. Weirich, B.A. Yorgey, T. Sheard (at ICFP'11)
///!
///! Effectively, we end up with a somewhat-convenient interface around the
///! *locally nameless* representation.


/// A free name; i.e., it is *not* bound (e.g., by a lambda).
/// 
/// # Decision: Public field
/// 
/// In contrast to `BoundName`, we make it's field public, as it is the
/// responsibility of "the environment" to avoid name collisions.
/// (For `BoundName`, we ensure proper /de Bruijn/ indices)
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FreeName {
  Num( usize ),
  Text( String )
}

/// A bound name.
/// 
/// Represented by a *de Bruijn* index.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct BoundName( usize );

impl BoundName {
  // /// Creating this manually from a *de Bruijn* index voids all guarantees by
  // /// this library. Use at your own risk.
  // pub unsafe fn unsafe_from_de_bruijn( i: usize ) -> BoundName {
  //   BoundName( i )
  // }

  pub fn de_bruijn_index( &self ) -> usize {
    self.0
  }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Name {
  Free( FreeName ),
  Bound( BoundName )
}

impl From< FreeName > for Name {
  fn from( n: FreeName ) -> Self {
    Name::Free( n )
  }
}

impl From< BoundName > for Name {
  fn from( n: BoundName ) -> Self {
    Name::Bound( n )
  }
}

/// An environment supporting fresh names
pub trait FreshVar {
  fn fresh_var( &mut self ) -> FreeName;
}

/// De Bruijn level
/// 
/// # Decision: Private field
/// 
/// We keep the field private to ensure external parties don't modify it.
/// Instead, only `Bind`'s methods modify it.
#[derive(Copy, Clone, Debug)]
pub struct Level( usize );

impl Level {
  pub fn to_usize( &self ) -> usize {
    self.0
  }

  pub fn to_name( &self ) -> BoundName {
    BoundName( self.0 )
  }
}

/// A trait for *locally nameless* terms
pub trait LocallyNameless {
  // "open" a term. a bound variable, becomes free.
  fn open( self, level: Level, new: &FreeName ) -> Self;

  // "close" a term. a free variable, becomes bound.
  fn close( self, level: Level, old: &FreeName ) -> Self;
}

pub trait Subst< T > {
  fn subst( self, x: &Name, t: T ) -> Self;
}

impl< T: LocallyNameless > LocallyNameless for Box< T > {
  fn open( mut self, level: Level, new: &FreeName ) -> Self {
    // This avoids cloning
    unsafe {
      let ptr: &mut T = &mut *self;
      let mut x = std::ptr::read( ptr );
      x = x.open( level, new );
      std::ptr::write( ptr, x );
    }
    self
  }

  // "close" a term. a free variable, becomes bound.
  fn close( mut self, level: Level, old: &FreeName ) -> Self {
    // This avoids cloning
    unsafe {
      let ptr: &mut T = &mut *self;
      let mut x = std::ptr::read( ptr );
      x = x.close( level, old );
      std::ptr::write( ptr, x );
    }
    self
  }
}

/// Note that we don't need to store a "name" here.
/// Bound variables are referenced by DeBruijn indices.
#[derive(Debug, Clone)]
pub struct Bind< T >( T );

impl< T > Bind< T > {
  /// A getter for the Bind's contained Term. Specifically, this is read-only.
  pub fn term( &self ) -> &T {
    &self.0
  }
}

impl< T1, T2: Subst< T1 > > Subst< T1 > for Bind< T2 > {
  fn subst( self, n: &Name, t: T1 ) -> Bind< T2 > {
    match n {
      Name::Bound( BoundName( de_bruijn_index ) ) =>
        Bind( self.0.subst( &Name::Bound( BoundName( de_bruijn_index + 1 ) ), t ) ),
      Name::Free( _ ) =>
        Bind( self.0.subst( n, t ) )
    }
  }
}

impl< T: LocallyNameless > LocallyNameless for Bind< T > {
  fn open( self, level: Level, new: &FreeName ) -> Self {
    let new_term = self.0.open( Level( level.0 + 1 ), new );
    Bind( new_term )
  }

  fn close( self, level: Level, old: &FreeName ) -> Self {
    let new_term = self.0.close( Level( level.0 + 1 ), old );
    Bind( new_term )
  }
}

impl< T: LocallyNameless > Bind< T > {
  pub fn bind( v: &FreeName, t: T ) -> Bind< T > {
    let new_t = t.close( Level( 0 ), v );
    Bind( new_t )
  }

  /// Bind with a name that was never explicit
  /// (e.g., the pi-type of "A -> B", where "B" does not depend on "A's value")
  pub fn nameless_bind( t: T ) -> Bind< T > {
    Bind( t )
  }

  pub fn unbind< F: FreshVar >( self, env: &mut F ) -> (FreeName, T) {
    let new_name = env.fresh_var( );
    let new_term = self.0.open( Level( 0 ), &new_name );
    (new_name, new_term)
  }

  // Unbind two terms *with the same fresh name*.
  pub fn unbind2< F: FreshVar >( env: &mut F, t0: Bind< T >, t1: Bind< T > ) -> (FreeName, T, T) {
    let new_name = env.fresh_var( );
    let t0_new: T = t0.0.open( Level( 0 ), &new_name );
    let t1_new: T = t1.0.open( Level( 0 ), &new_name );
    (new_name, t0_new, t1_new)
  }

  pub fn instantiate< T2 >( self, t: T2 ) -> T
    where T: Subst< T2 > {
    self.0.subst( &Name::Bound( BoundName( 0 ) ), t )
  }

  // /// This is generally a bad idea.
  // pub fn coerce< T2: LocallyNameless, F: FnOnce( T ) -> T2 >( self, f: F ) -> Bind< T2 > {
  //   Bind( f( self.0 ) )
  // }
}

impl< T: LocallyNameless > Bind< Box< T > > {
  pub fn unbox( self ) -> Bind< T > {
    Bind( *self.0 )
  }
}
