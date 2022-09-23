
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
  TyUnit,
  ///
  LitUnit,
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
      Term::TyUnit => f( &self, v ),
      Term::LitUnit => f( &self, v ),
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
        Term::TyUnit => false,
        Term::LitUnit => false,
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
      let x = std::ptr::read( ptr ).subst( n, t );
      let x = x.subst( n, t );
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
      Term::TyUnit => self,
      Term::LitUnit => self,
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
      Term::TyUnit => self,
      Term::LitUnit => self,
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
      Term::TyUnit => self,
      Term::LitUnit => self,
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
      (Term::TyUnit, Term::TyUnit) => true,
      (Term::LitUnit, Term::LitUnit) => true,
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
      Term::TyUnit => Prec::Atom,
      Term::LitUnit => Prec::Atom,
      Term::If( _, _, _ ) => Prec::IfThenElse,
      Term::Sigma( _, _ ) => Prec::Atom,
      Term::Prod( _, _ ) => Prec::Atom,
      Term::LetPair( _, _ ) => Prec::IfThenElse
    }
  }
}

pub enum Prec {
  Colon, // weakest
  Lambda,
  Arrow,
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
      Prec::Colon => Prec::Lambda,
      Prec::Lambda => Prec::Arrow,
      Prec::Arrow => Prec::IfThenElse,
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
      Prec::Lambda     => 1,
      Prec::Arrow      => 2,
      Prec::IfThenElse => 3,
      Prec::App        => 4,
      Prec::Atom       => 5
    }
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

  pub fn name( &self ) -> &N {
    match self {
      Decl::Def( n, _ ) => n,
      Decl::TypeSig( n, _ ) => n
    }
  }

  pub fn def( &self ) -> Option< (&N, &Term) > {
    if let Decl::Def( n, t ) = self {
      Some( (n, t) )
    } else {
      None
    }
  }

  pub fn type_sig( &self ) -> Option< (&N, &Term) > {
    if let Decl::TypeSig( n, t ) = self {
      Some( (n, t) )
    } else {
      None
    }
  }
}

#[derive(Debug)]
pub struct Module {
  pub name : String,
  pub entries : Vec< Decl< String > >
}
