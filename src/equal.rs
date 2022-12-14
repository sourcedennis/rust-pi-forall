
// local imports
use crate::syntax::{Term, Arg, Epsilon};
use crate::environment::{Env, ErrMsg, assert_res};
use crate::unbound::{Name, Bind, FreshVar};


pub fn equate_arg< F: FreshVar >(
  fresh_env: &mut F,
  env: &Env,
  x: &Arg,
  y: &Arg
) -> Result< (), ErrMsg > {
  if x.eps == Epsilon::Rel && y.eps == Epsilon::Rel {
    equate( fresh_env, env, &x.term, &y.term )
  } else if x.eps == Epsilon::Irr && y.eps == Epsilon::Irr {
    Ok( () )
  } else {
    Err( "Relevance mismatch".to_owned( ) )
  }
}

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
      (Term::Lam( eps1, bnd1 ), Term::Lam( eps2, bnd2 ) ) => {
        assert_res( eps1 == eps2, format!( "{:?} != {:?}", eps1, eps2 ) )?;
        let (_, body1, body2) = Bind::unbind2( fresh_env, bnd1, bnd2 );
        equate( fresh_env, env, &body1, &body2 )
      },
      (Term::App( x1, y1 ), Term::App( x2, y2 ) ) => {
        equate( fresh_env, env, &x1, &x2 )?;
        equate_arg( fresh_env, env, &y1, &y2 )
      },
      (Term::Pi( eps1, x1, bnd1 ), Term::Pi( eps2, x2, bnd2 ) ) => {
        assert_res( eps1 == eps2, format!( "{:?} != {:?}", eps1, eps2 ) )?;
        equate( fresh_env, env, &x1, &x2 )?;
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
      (Term::TyEq( x1, y1 ), Term::TyEq( x2, y2 )) => {
        equate( fresh_env, env, &x1, &x2 )?;
        equate( fresh_env, env, &y1, &y2 )
      },
      (Term::Refl, Term::Refl) => {
        Ok( () )
      },
      (Term::Subst( x1, y1 ), Term::Subst( x2, y2 )) => {
        equate( fresh_env, env, &x1, &x2 )?;
        equate( fresh_env, env, &y1, &y2 )
      },
      (Term::Contra( x1 ), Term::Contra( x2 )) => {
        equate( fresh_env, env, &x1, &x2 )
      },
      (Term::Case( _, _ ), Term::Case( _, _ )) => {
        unimplemented!( )
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
      if let Term::Lam( _, bnd ) = x {
        whnf( env, *bnd.instantiate( &y.term ) )
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
    Term::Subst( tm, pf ) => {
      let pf = whnf( env, *pf );
      match pf {
        Term::Refl => whnf( env, *tm ),
        _ => Term::Subst( tm, Box::new( pf ) )
      }
    },
    Term::Case( _, _ ) => {
      unimplemented!() // TODO
    },
    // Keep these in here explicit (as opposed to "_") to get notified whenever
    // a case is missing after extending the syntax.
    Term::Type => t,
    Term::Var( Name::Bound( _ ) ) => t,
    Term::Lam( _, _ ) => t,
    Term::Pi( _, _, _ ) => t,
    Term::TyBool => t,
    Term::LitBool( _ ) => t,
    Term::TyUnit => t,
    Term::LitUnit => t,
    Term::Sigma( _, _ ) => t,
    Term::Prod( _, _ ) => t,
    Term::TyEq( _, _ ) => t,
    Term::Refl => t,
    Term::Contra( _ ) => t,
  }
}
