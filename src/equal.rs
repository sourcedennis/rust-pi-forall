
// local imports
use crate::syntax::Term;
use crate::environment::Env;
use crate::unbound::{Name, Bind, FreshVar};


type ErrMsg = String;

pub fn equate< F: FreshVar >( fresh_env: &mut F, env: &Env, x: &Term, y: &Term ) -> Result< (), ErrMsg > {
  if x.aeq( y ) {
    Ok( () )
  } else {
    let x = whnf( env, x.clone( ) );
    let y = whnf( env, y.clone( ) );

    match (x, y) {
      (Term::Type, Term::Type) => Ok( () ),
      (Term::Var( x ), Term::Var( y ) ) =>
        if x == y {
          Ok( () )
        } else {
          Err( format!( "{:?} != {:?}", x, y ) )
        },
      (Term::Lam( bnd1 ), Term::Lam( bnd2 ) ) => {
        let (_, body1, body2) = Bind::unbind2( fresh_env, bnd1, bnd2 );
        equate( fresh_env, env, &body1, &body2 )
      },
      (Term::App( x1, y1 ), Term::App( x2, y2 ) ) => {
        equate( fresh_env, env, &x1, &x2 )?;
        equate( fresh_env, env, &y1, &y2 )
      },
      (Term::Pi( x1, bnd1 ), Term::Pi( y1, bnd2 ) ) => {
        equate( fresh_env, env, &x1, &y1 )?;
        equate( fresh_env, env, &bnd1.term( ), &bnd2.term( ) )
      },
      (Term::TyBool, Term::TyBool) => Ok( () ),
      (Term::LitBool( b1 ), Term::LitBool( b2 )) =>
        if b1 == b2 {
          Ok( () )
        } else {
          Err( format!( "{} != {}", b1, b2 ) )
        },
      (Term::If( c1, x1, y1 ), Term::If( c2, x2, y2 ) ) => {
        equate( fresh_env, env, &c1, &c2 )?;
        equate( fresh_env, env, &x1, &x2 )?;
        equate( fresh_env, env, &y1, &y2 )
      },
      (Term::Sigma( x1_ty, bnd1 ), Term::Sigma( x2_ty, bnd2 )) => {
        let (_, y1_ty, y2_ty) = Bind::unbind2( fresh_env, bnd1, bnd2 );
        equate( fresh_env, env, &x1_ty, &x2_ty )?;
        equate( fresh_env, env, &y1_ty, &y2_ty )
      },
      (Term::Prod( x1, y1 ), Term::Prod( x2, y2 ) ) => {
        equate( fresh_env, env, &x1, &x2 )?;
        equate( fresh_env, env, &y1, &y2 )
      },
      (Term::LetPair( _, bnd1 ), Term::LetPair( _, bnd2 ) ) => {
        let (_, bnd1, bnd2) = Bind::unbind2( fresh_env, bnd1, bnd2 );
        let (_, body1, body2) = Bind::unbind2( fresh_env, bnd1, bnd2 );
        equate( fresh_env, env, &body1, &body2 )
      },
      (x, y) => Err( format!( "{:?} != {:?}", x, y ) )
    }
  }
}

pub fn whnf( env: &Env, t: Term ) -> Term {
  match t {
    Term::Var( Name::Free( n ) ) =>
      if let Some( v ) = env.lookup_def( &n ) {
        whnf( env, v.clone( ) )
      } else {
        Term::Var( Name::Free( n ) )
      },
    Term::App( x, y ) => {
      let x = whnf( env, *x );
      if let Term::Lam( bnd ) = x {
        whnf( env, *bnd.instantiate( &y ) )
      } else {
        Term::App( Box::new( x ), y )
      }
    },
    Term::Ann( x, _ ) => whnf( env, *x ),
    Term::If( c, x, y ) => {
      let c = whnf( env, *c );
      if let Term::LitBool( b ) = c {
        whnf( env, if b { *x } else { *y } )
      } else {
        Term::If( Box::new( c ), x, y )
      }
    },
    Term::LetPair( x, bnd ) => {
      let x = whnf( env, *x );
      if let Term::Prod( x1, x2 ) = x {
        let body = bnd.instantiate( &x1 ).instantiate( &x2 );
        whnf( env, *body )
      } else {
        Term::LetPair( Box::new( x ), bnd )
      }
    },
    // Keep these in here explicit (as opposed to "_") to get notified whenever
    // a case is missing after extending the syntax.
    Term::Type => t,
    Term::Var( Name::Bound( _ ) ) => t,
    Term::Lam( _ ) => t,
    Term::Pi( _, _ ) => t,
    Term::TyBool => t,
    Term::LitBool( _ ) => t,
    Term::Sigma( _, _ ) => t,
    Term::Prod( _, _ ) => t,
  }
}
