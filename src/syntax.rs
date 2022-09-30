
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
  Lam( Epsilon, Bind< Box< Term > > ),
  /// Function application
  App( Box< Term >, Box< Arg > ),
  /// A Pi-type, being a dependent function type: (x: A) -> B
  Pi( Epsilon, Box< Type >, Bind< Box< Type > > ),
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
  LetPair( Box< Term >, Bind< Bind< Box< Term > > > ),
  /// Equality type `a = b`
  TyEq( Box< Term >, Box< Term > ),
  /// Equality proof
  Refl,
  /// subst a by pf
  Subst( Box< Term >, Box< Term > ),
  /// equality contradiction
  Contra( Box< Term > ),
  /// 
  Case( Box< Term >, Vec< Match > )
}

impl Term {
  pub fn visit_preorder< T, F >( &self, mut f: F, v: T ) -> T
    where F: FnMut( &Term, T ) -> T + Copy
  {
    match self {
      Term::Type => f( &self, v ),
      Term::Var( _ ) => f( &self, v ),
      Term::Lam( _, x ) => {
        let v = f( &self, v );
        x.term( ).visit_preorder( f, v )
      },
      Term::App( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.term.visit_preorder( f, v )
      },
      Term::Pi( _, x, y ) => {
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
      },
      Term::TyEq( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::Refl => f( &self, v ),
      Term::Subst( x, y ) => {
        let v = f( &self, v );
        let v = x.visit_preorder( f, v );
        y.visit_preorder( f, v )
      },
      Term::Contra( x ) => {
        let v = f( &self, v );
        x.visit_preorder( f, v )
      },
      Term::Case( _, matches ) => {
        let v = f( &self, v );
        matches.iter( ).fold( v, |acc,m| m.term.term( ).visit_preorder( f, acc ) )
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
        Term::Lam( _, x ) => rec( level + 1, x.term( ) ),
        Term::App( x, y ) =>
          rec( level, x ) || rec( level, &y.term ),
        Term::Pi( _, x, y ) => rec( level, x ) || rec( level + 1, y.term( ) ),
        Term::Ann( x, y ) => rec( level, x ) || rec( level, y ),
        Term::TyUnit => false,
        Term::LitUnit => false,
        Term::TyBool => false,
        Term::LitBool( _ ) => false,
        Term::If( cond, x, y ) => rec( level, cond ) || rec( level, x ) || rec( level, y ),
        Term::Sigma( x, bnd ) => rec( level, x ) || rec( level + 1, bnd.term( ) ),
        Term::Prod( x, y ) => rec( level, x ) || rec( level, y ),
        Term::LetPair( x, bnd ) => rec( level, x ) || rec( level + 2, bnd.term( ).term( ) ),
        Term::TyEq( x, y ) => rec( level, x ) || rec( level, y ),
        Term::Refl => false,
        Term::Subst( x, y ) => rec( level, x ) || rec( level, y ),
        Term::Contra( x ) => rec( level, x ),
        Term::Case( t, xs ) =>
          rec( level, t ) ||
            xs.iter( )
              .any( |x| rec( level + x.pattern.num_vars( ), x.term.term( ) ) )
      }
    }

    rec( 0, self )
  }
}

impl< T1, T2: Subst< T1 > > Subst< T1 > for Box< T2 > {
  fn subst( mut self, n: &Name, t: T1 ) -> Box< T2 > {
    // This avoids cloning
    unsafe {
      let ptr: &mut T2 = &mut *self;
      let x = std::ptr::read( ptr );
      let x = x.subst( n, t );
      std::ptr::write( ptr, x );
    }
    self
  }
}

impl Subst< &Term > for ManyBind< Term > {
  fn subst( self, name: &Name, t: &Term ) -> ManyBind< Term > {
    match self {
      ManyBind::Base( x ) => ManyBind::Base( x.subst( name, t ) ),
      ManyBind::Bind1( x ) => ManyBind::Bind1( x.subst( name, t ) )
    }
  }
}

impl Subst< &Term > for Match {
  fn subst( self, name: &Name, t: &Term ) -> Match {
    Match { pattern: self.pattern, term: self.term.subst( name, t ) }
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
      Term::Lam( eps, bnd ) => Term::Lam( eps, bnd.subst( name, t ) ),
      Term::App( x, y ) => Term::App( x.subst( name, t ), y.subst( name, t ) ),
      Term::Pi( eps, x, y ) => Term::Pi( eps, x.subst( name, t ), y.subst( name, t ) ),
      Term::Ann( x, x_type ) => Term::Ann( x.subst( name, t ), x_type.subst( name, t ) ),
      Term::TyUnit => self,
      Term::LitUnit => self,
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.subst( name, t ), x.subst( name, t ), y.subst( name, t ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.subst( name, t ), bnd.subst( name, t ) ),
      Term::Prod( x, y ) => Term::Prod( x.subst( name, t ), y.subst( name, t ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.subst( name, t ), bnd.subst( name, t ) ),
      Term::TyEq( x, y ) => Term::TyEq( x.subst( name, t ), y.subst( name, t ) ),
      Term::Refl => self,
      Term::Subst( x, y ) => Term::Subst( x.subst( name, t ), y.subst( name, t ) ),
      Term::Contra( x ) => Term::Contra( x.subst( name, t ) ),
      Term::Case( x, xs ) =>
        Term::Case(
          x.subst( name, t ),
          xs.into_iter( ).map( |x| x.subst( name, t ) ).collect( )
        )
    }
  }
}

impl< T: LocallyNameless > LocallyNameless for ManyBind< T > {
  fn open( self, level: Level, new: &FreeName ) -> Self {
    match self {
      ManyBind::Base( x ) => ManyBind::Base( x.open( level, new ) ),
      ManyBind::Bind1( x ) => ManyBind::Bind1( x.open( level, new ) )
    }
  }

  fn close( self, level: Level, old: &FreeName ) -> Self {
    match self {
      ManyBind::Base( x ) => ManyBind::Base( x.close( level, old ) ),
      ManyBind::Bind1( x ) => ManyBind::Bind1( x.close( level, old ) )
    }
  }
}

impl LocallyNameless for Match {
  fn open( self, level: Level, new: &FreeName ) -> Self {
    Match { pattern: self.pattern, term: self.term.open( level, new ) }
  }

  fn close( self, level: Level, old: &FreeName ) -> Self {
    Match { pattern: self.pattern, term: self.term.open( level, old ) }
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
      Term::Lam( eps, b ) => Term::Lam( eps, b.open( level, new ) ),
      Term::App( x, y ) => Term::App( x.open( level, new ), y.open( level, new ) ),
      Term::Pi( eps, a, f ) => Term::Pi( eps, a.open( level, new ), f.open( level, new ) ),
      Term::Ann( x, y ) => Term::Ann( x.open( level, new ), y.open( level, new ) ),
      Term::TyUnit => self,
      Term::LitUnit => self,
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.open( level, new ), x.open( level, new ), y.open( level, new ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.open( level, new ), bnd.open( level, new ) ),
      Term::Prod( x, y ) => Term::Prod( x.open( level, new ), y.open( level, new ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.open( level, new ), bnd.open( level, new ) ),
      Term::TyEq( x, y ) => Term::TyEq( x.open( level, new ), y.open( level, new ) ),
      Term::Refl => self,
      Term::Subst( x, y ) => Term::Subst( x.open( level, new ), y.open( level, new ) ),
      Term::Contra( x ) => Term::Contra( x.open( level, new ) ),
      Term::Case( x, xs ) =>
        Term::Case(
          x.open( level, new ),
          xs.into_iter( ).map( |x| x.open( level, new ) ).collect( )
        )
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
      Term::Lam( eps, b ) => Term::Lam( eps, b.close( level, old ) ),
      Term::App( x, y ) => Term::App( x.close( level, old ), y.close( level, old ) ),
      Term::Pi( eps, a, f ) => Term::Pi( eps, a.close( level, old ), f.close( level, old ) ),
      Term::Ann( x, y ) => Term::Ann( x.close( level, old ), y.close( level, old ) ),
      Term::TyUnit => self,
      Term::LitUnit => self,
      Term::TyBool => self,
      Term::LitBool( _ ) => self,
      Term::If( cond, x, y ) => Term::If( cond.close( level, old ), x.close( level, old ), y.close( level, old ) ),
      Term::Sigma( x, bnd ) => Term::Sigma( x.close( level, old ), bnd.close( level, old ) ),
      Term::Prod( x, y ) => Term::Prod( x.close( level, old ), y.close( level, old ) ),
      Term::LetPair( x, bnd ) => Term::LetPair( x.close( level, old ), bnd.close( level, old ) ),
      Term::TyEq( x, y ) => Term::TyEq( x.close( level, old ), y.close( level, old ) ),
      Term::Refl => self,
      Term::Subst( x, y ) => Term::Subst( x.close( level, old ), y.close( level, old ) ),
      Term::Contra( x ) => Term::Contra( x.close( level, old ) ),
      Term::Case( x, xs ) =>
        Term::Case(
          x.close( level, old ),
          xs.into_iter( ).map( |x| x.close( level, old ) ).collect( )
        )
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
      (Term::Lam( eps0, x ), Term::Lam( eps1, y )) =>
        eps0 == eps1 && x.term( ).aeq( y.term( ) ),
      (Term::App( x0, y0 ), Term::App( x1, y1 )) =>
        x0.aeq( x1 ) && y0.aeq( y1 ),
      (Term::Pi( eps0, x0, y0 ), Term::Pi( eps1, x1, y1 ) ) =>
        eps0 == eps1 && x0.aeq( x1 ) && y0.term( ).aeq( y1.term( ) ),
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
      (Term::TyEq( x1, y1 ), Term::TyEq( x2, y2 ) ) =>
        x1.aeq( x2 ) && y1.aeq( y2 ),
      (Term::Refl, Term::Refl) => true,
      (Term::Subst( x1, y1 ), Term::Subst( x2, y2 ) ) =>
        x1.aeq( x2 ) && y1.aeq( y2 ),
      (Term::Contra( x1 ), Term::Contra( x2 )) =>
        x1.aeq( x2 ),
      (Term::Case( x1, xs1 ), Term::Case( x2, xs2 ) ) => {
        x1.aeq( x2 ) &&
          xs1.iter( )
             .zip( xs2.iter( ) )
             .all( |(x,y)| x.term.term( ).aeq( y.term.term( ) )
          )
      },
      (_, _) => false
    }
  }

  pub fn prec( &self ) -> Prec {
    match self {
      Term::Type => Prec::Atom,
      Term::Var( _ ) => Prec::Atom,
      Term::Lam( _, _ ) => Prec::Lambda,
      Term::App( _, _ ) => Prec::App,
      Term::Pi( _, _, _ ) => Prec::Arrow,
      Term::Ann( _, _ ) => Prec::Colon,
      Term::TyBool => Prec::Atom,
      Term::LitBool( _ ) => Prec::Atom,
      Term::TyUnit => Prec::Atom,
      Term::LitUnit => Prec::Atom,
      Term::If( _, _, _ ) => Prec::IfThenElse,
      Term::Sigma( _, _ ) => Prec::Atom,
      Term::Prod( _, _ ) => Prec::Atom,
      Term::LetPair( _, _ ) => Prec::IfThenElse,
      Term::TyEq( _, _ ) => Prec::Equality,
      Term::Refl => Prec::Atom,
      Term::Subst( _, _ ) => Prec::IfThenElse,
      Term::Contra( _ ) => Prec::Atom,
      Term::Case( _, _ ) => Prec::IfThenElse
    }
  }
}

#[derive(Debug, Clone)]
pub struct Arg {
  pub eps  : Epsilon,
  pub term : Term
}

impl Arg {
  pub fn new( eps: Epsilon, term: Term ) -> Arg {
    Arg { eps, term }
  }

  pub fn aeq( &self, y: &Arg ) -> bool {
    self.eps == y.eps && self.term.aeq( &y.term )
  }
}

impl LocallyNameless for Arg {
  fn open( self, level: Level, new: &FreeName ) -> Self {
    Arg::new( self.eps, self.term.open( level, new ) )
  }

  fn close( self, level: Level, old: &FreeName ) -> Self {
    Arg::new( self.eps, self.term.close( level, old ) )
  }
}

impl Subst< &Term > for Arg {
  fn subst( self, x: &Name, t: &Term ) -> Self {
    Arg::new( self.eps, self.term.subst( x, t ) )
  }
}

///
/// The (implicit) order on this enum is: Rel < Irr
#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Epsilon {
  /// Relevant
  Rel,
  /// Irrelevant
  Irr
}

#[derive(Debug, Clone)]
pub enum Pattern {
  Con( String, Vec< (Pattern, Epsilon) > ),
  Var
}

impl Pattern {
  /// The numbers of variables bound by the pattern
  pub fn num_vars( &self ) -> usize {
    match self {
      Pattern::Var => 1,
      Pattern::Con( _, xs ) =>
        xs.iter( ).map( |(x,_)| x.num_vars( ) ).sum( )
    }
  }
}

#[derive(Debug, Clone)]
pub enum ManyBind< T > {
  Base( T ),
  Bind1( Bind< Box< ManyBind< T > > > )
}

impl< T > ManyBind< T > {
  pub fn term( &self ) -> &T {
    match self {
      ManyBind::Base( x ) => x,
      ManyBind::Bind1( b ) => b.term( ).term( )
    }
  }
}

/// pattern matching that shows up in function definitions, e.g.:
/// f (Left (Right x)) = x * 2
#[derive(Debug, Clone)]
pub struct Match {
  pub pattern: Pattern,
  pub term:    ManyBind< Term >
}

impl Match {
  pub fn new( pattern: Pattern, term: ManyBind< Term > ) -> Match {
    Match { pattern, term }
  }
}

#[derive(Debug)]
pub enum Prec {
  Colon, // weakest
  Lambda,
  Arrow,
  Equality,
  IfThenElse, // also let-binding, subst
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
      Prec::Arrow => Prec::Equality,
      Prec::Equality => Prec::IfThenElse,
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
      Prec::Equality   => 3,
      Prec::IfThenElse => 4,
      Prec::App        => 5,
      Prec::Atom       => 6
    }
  }
}

#[derive(Debug, Clone)]
pub struct Sig< N > {
  pub name  : N,
  pub eps   : Epsilon,
  pub ttype : Type
}

impl< N > Sig< N > {
  pub fn new( name: N, eps: Epsilon, ttype: Type ) -> Sig< N > {
    Sig { name, eps, ttype }
  }

  /// Make the definition *relevant*
  pub fn demote( &mut self ) {
    self.eps = Epsilon::Rel;
  }
}

// Parameterised over names
#[derive(Debug, Clone)]
pub enum Decl< N = String > {
  /// Type signature
  /// 
  /// Example:
  /// id : (x : Type) -> (y : x) -> x
  TypeSig( Sig< N > ),
  /// Definition of some name. Must already have a type declaration.
  /// 
  /// Example:
  /// id = \x y . y
  Def( N, Term )
}

impl< N > Decl< N > {
  pub fn new_sig( n: N, rel: Epsilon, t: Type ) -> Decl< N > {
    Decl::TypeSig( Sig::new( n, rel, t ) )
  }

  pub fn is_def( &self ) -> bool {
    match self {
      Decl::Def( _, _ ) => true,
      _ => false
    }
  }

  pub fn name( &self ) -> &N {
    match self {
      Decl::Def( n, _ ) => n,
      Decl::TypeSig( sig ) => &sig.name
    }
  }

  pub fn def( &self ) -> Option< (&N, &Term) > {
    if let Decl::Def( n, t ) = self {
      Some( (n, t) )
    } else {
      None
    }
  }

  pub fn type_sig( &self ) -> Option< &Sig< N > > {
    if let Decl::TypeSig( sig ) = self {
      Some( sig )
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
