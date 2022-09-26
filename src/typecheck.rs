
// local imports
use crate::unbound::{FreshVar, Name, FreeName, Bind};
use crate::syntax::{Term, Type, Module, Decl};
use crate::environment::{Env, Ctx};
use crate::equal::{whnf, equate};


type ErrorMsg = String;

pub fn tc_module< F : FreshVar >( fresh_env: &mut F, m: &Module ) -> Result< Ctx, ErrorMsg > {
  let mut env = Env::new( );

  for d in &m.entries {
    match d {
      Decl::TypeSig( name, ttype ) => {
        tc_type( fresh_env, &env, &ttype )?;
        env.add_hint( FreeName::Text( name.clone( ) ), ttype.clone( ) );
      },
      Decl::Def( name, term ) => {
        let fname = FreeName::Text( name.clone( ) );

        if env.lookup_def( &fname ).is_some( ) {
          return Err( format!( "Multiple definitions of {}", name ) );
        } else if let Some( ty_hint ) = env.lookup_hint( &fname ) {
          let mut env2 = env.clone( );
          env2.extend( Decl::TypeSig( fname.clone( ), ty_hint.clone( ) ) );
          check_type( fresh_env, &env2, &term, ty_hint.clone( ) )?;

          env.extend( Decl::TypeSig( fname.clone( ), ty_hint.clone( ) ) );
          env.extend( Decl::Def( fname, term.clone( ) ) );
        } else {
          let term_type = tc_term( fresh_env, &env, &term, None )?;
          env.extend( Decl::TypeSig( fname.clone( ), term_type ) );
          env.extend( Decl::Def( fname, term.clone( ) ) );
        }
      }
    }
  }

  Ok( env.into( ) )
}

fn ensure_pi( env: &Env, t: Term ) -> Result< (Term, Bind<Term>), ErrorMsg > {
  match whnf( env, t ) {
    Term::Pi( ty_a, bnd ) => Ok( ( *ty_a, bnd.unbox() ) ),
    Term::Ann( t , _ ) => ensure_pi( env, *t ),
    t => Err( format!( "Expected a function type but found {:?}", t ) )
  }
}

fn ensure_tyeq( env: &Env, t: Term ) -> Result< (Term, Term), ErrorMsg > {
  match whnf( env, t ) {
    Term::TyEq( x, y ) => Ok( ( *x, *y ) ),
    t => Err( format!( "Expected an equality type but found {:?}", t ) )
  }
}

fn check_type< Fresh: FreshVar >(
  fresh_env: &mut Fresh,
  env: &Env,
  t: &Term,
  t_type: Type
) -> Result< (), ErrorMsg > {
  // Convert the type to WHNF. Consider:
  // f : Bool -> Type
  // g : f True
  // g = \x . ...
  // The lambda must have a pi-type, which it doesn't, unless we whnf `f True`.
  tc_term( fresh_env, env, t, Some( whnf( env, t_type.clone( ) ) ) )?;
  Ok( () )
}

fn infer_type< Fresh: FreshVar >(
  fresh_env: &mut Fresh,
  env: &Env,
  t: &Term
) -> Result< Type, ErrorMsg > {
  tc_term( fresh_env, env, t, None )
}

fn tc_type< Fresh: FreshVar >(
  fresh_env: &mut Fresh,
  env: &Env,
  t: &Term
) -> Result< (), ErrorMsg > {
  check_type( fresh_env, env, t, Term::Type )
}

/// Either typecheck (if `t_type.is_some()`) or perform type inference (when
/// `t_type.is_none()`).
fn tc_term< Fresh: FreshVar >(
  fresh_env: &mut Fresh,
  env: &Env,
  t: &Term,
  t_type: Option< Type >
) -> Result< Type, ErrorMsg > {
  match (t, t_type) {
    (Term::Var( Name::Bound( _ ) ), None) =>
      // It makes no sense to encounter "bound" variables inside a term. We
      // always open terms before entering them, which means that leaves (e.g.,
      // `Term::Var`) are only encountered after opening all bindings. This is
      // only possible if somebody constructed an invalid `Term`.
      Err( "AST error".to_string( ) ),
    (Term::Var( Name::Free( n ) ), None) =>
      if let Some( n_type ) = env.lookup_type( n ) {
        Ok( n_type.clone( ) )
      } else {
        Err( format!( "unknown variable \"{:?}\"", n ) )
      },
    (Term::Type, None) => Ok( Term::Type ), // type-in-type
    (Term::Pi(ty_a, bnd), None) => {
      // (x : A) -> B
      let (x, ty_b) = bnd.clone( ).unbind( fresh_env );
      tc_type( fresh_env, env, ty_a )?; // Check: Γ ⊢ A : Type
      
      let mut env2: Env = env.clone( );
      env2.extend( Decl::TypeSig( x, *ty_a.clone( ) ) );
      tc_type( fresh_env, &env2, &ty_b )?; // Check: Γ,(x:A) ⊢ B : Type

      Ok( Term::Type ) // Then: Γ ⊢ (x : A) -> B : Type
    },
    (Term::Lam(bnd), Some( Term::Pi( ty_a, bnd2 ))) => {
      let (x, body, ty_b) = Bind::unbind2( fresh_env, bnd.clone( ), bnd2.clone( ) );

      // Check: Γ,(x:A) ⊢ body : B
      let mut env2 = env.clone( );
      env2.extend( Decl::TypeSig( x, *ty_a.clone( ) ) );
      check_type( fresh_env, &env2, &body, *ty_b )?;

      Ok( Term::Pi( ty_a.clone( ), bnd2 ) )
    },
    (Term::Lam( _ ), Some( ttype ) ) => Err( format!( "A lambda expression should have a function type, not {:?}", ttype ) ),
    (Term::App(t1, t2), None) => {
      // Infer:  Γ ⊢ t1 : (x : A) -> B
      let ty1 = tc_term( fresh_env, env, t1, None )?;
      let (ty_a, bnd) = ensure_pi( env, ty1 )?;
      // Check:  Γ ⊢ t2 : A
      check_type( fresh_env, env, t2, ty_a )?;

      Ok( bnd.instantiate( t2 ) )
    },
    (Term::Ann( tm, ty ), None) => {
      tc_type( fresh_env, env, ty )?;
      check_type( fresh_env, env, tm, *ty.clone( ) )?;
      Ok( *ty.clone( ) )
    },
    (Term::TyUnit, None) => Ok( Term::Type ),
    (Term::LitUnit, None) => Ok( Term::TyUnit ),
    (Term::TyBool, None) => Ok( Term::Type ),
    (Term::LitBool( _ ), None) => Ok( Term::TyBool ),
    (Term::If( cond, x, y ), Some( ty )) => {
      check_type( fresh_env, env, cond, Term::TyBool )?;

      if let Some( dtrue ) = def( env, *cond.clone( ), Term::LitBool( true ) ) {
        // Context-sensitive checking true branch
        let mut env2 = env.clone( );
        env2.extend( dtrue );
        check_type( fresh_env, &env2, x, ty.clone( ) )?;
      } else {
        check_type( fresh_env, env, x, ty.clone( ) )?;
      }

      if let Some( dfalse ) = def( env, *cond.clone( ), Term::LitBool( false ) ) {
        // Context-sensitive checking false branch
        let mut env2 = env.clone( );
        env2.extend( dfalse );
        check_type( fresh_env, &env2, y, ty.clone( ) )?;
      } else {
        check_type( fresh_env, env, y, ty.clone( ) )?;
      }

      Ok( ty )
    },
    (Term::If( cond, x, y ), None) => {
      check_type( fresh_env, env, cond, Term::TyBool )?;
      let x_ty = tc_term( fresh_env, env, x, None )?; // infer
      check_type( fresh_env, env, y, x_ty.clone( ) )?; // check
      Ok( x_ty )
    },
    (Term::Sigma( x_ty, bnd ), None) => {
      // Check:  Γ ⊢ x_ty : Type
      tc_type( fresh_env, env, x_ty )?;

      let (x, y_ty) = bnd.clone( ).unbind( fresh_env );

      let mut env2 = env.clone( );
      env2.extend( Decl::TypeSig( x, *x_ty.clone( ) ) );
      // Check:  Γ,(x:x_ty) ⊢ y_ty : Type
      tc_type( fresh_env, &env2, &y_ty )?;

      Ok( Term::Type )
    },
    // This requires *checking*
    (Term::Prod( x, y ), Some( Term::Sigma( x_ty, bnd ) ) ) => {
      let (x_name, y_ty) = bnd.unbind( fresh_env );

      check_type( fresh_env, env, x, *x_ty.clone( ) )?;

      let mut env2 = env.clone( );
      env2.extend( Decl::TypeSig( x_name.clone( ), *x_ty.clone( ) ) );
      env2.extend( Decl::Def( x_name.clone( ), *x.clone( ) ) );
      check_type( fresh_env, &env2, y, *y_ty.clone( ) )?;
      
      Ok( Term::Sigma( x_ty, Bind::bind( &x_name, y_ty ) ) )
    },
    (Term::LetPair( p, bnd2 ), Some( ty )) => {
      // "x" is the outer-most name. "y" is innermost
      // let (x,y) = ? in ?
      let (x_name, bnd1) = bnd2.clone( ).unbind( fresh_env );
      let (y_name, body) = bnd1.unbind( fresh_env );

      let p_ty = tc_term( fresh_env, env, p, None )?;
      let p_ty = whnf( env, p_ty );

      match p_ty {
        Term::Sigma( x_ty, s_bnd ) => {
          let y_ty = s_bnd.instantiate( &Term::Var( Name::Free( x_name.clone( ) ) ) );
          let decl = def( env, *p.clone( ),
            Term::Prod(
              Box::new( Term::Var( Name::Free( x_name.clone( ) ) ) ),
              Box::new( Term::Var( Name::Free( y_name.clone( ) ) ) ) ) );
          
          let mut env2 = env.clone( );
          env2.extend( Decl::TypeSig( x_name, *x_ty ) );
          env2.extend( Decl::TypeSig( y_name, *y_ty ) );
          if let Some( decl ) = decl {
            env2.extend( decl );
          }
          check_type( fresh_env, &env2, &body, ty.clone( ) )?; // Why is this checked? Can't we infer it?

          Ok( ty )
        },
        _ => Err( "Scrutinee must have a Sigma type".to_owned( ) )
      }
    },
    (Term::Prod( _, _ ), Some( ty ) ) =>
      Err( format!( "Products must have a Sigma Type, not {:?}", ty ) ),
    (Term::TyEq( x, y ), None) => {
      let x_ty = infer_type( fresh_env, env, x )?;
      check_type( fresh_env, env, y, x_ty )?;
      Ok( Term::Type )
    },
    (Term::Refl, Some( Term::TyEq( x_ty, y_ty ) ) ) => {
      equate( fresh_env, env, &x_ty, &y_ty )?;
      Ok( Term::TyEq( x_ty, y_ty ) )
    },
    // subst x by y : A
    // where y : m = n
    (Term::Subst( x, y ), Some( ty )) => {
      let y_ty = infer_type( fresh_env, env, y )?;
      let (m, n) = ensure_tyeq( env, y_ty )?;

      let m_decl1 = def( env, m, n );
      let m_decl2 = def( env, *y.clone( ), Term::Refl );

      let mut env2: Env = env.clone( );
      if let Some( decl1 ) = m_decl1 {
        env2.extend( decl1 );
      }
      if let Some( decl2 ) = m_decl2 {
        env2.extend( decl2 );
      }

      check_type( fresh_env, &env2, x, ty.clone( ) )?;
      Ok( ty )
    },
    (Term::Contra( p ), Some( ty )) => {
      let p_ty = infer_type( fresh_env, env, p )?;
      let (x, y) = ensure_tyeq( env, p_ty )?;
      let x = whnf( env, x );
      let y = whnf( env, y );
      
      match (whnf( env, x ), whnf( env, y )) {
        (Term::LitBool( b1 ), Term::LitBool( b2 ) ) => {
          if b1 != b2 {
            Ok( ty )
          } else {
            Err( "Not contradictory".to_owned( ) )
          }
        }
        _ => Err( "Not contradictory".to_owned( ) )
      }
    },
    (tm, Some( ty ) ) => {
      let ty2 = tc_term( fresh_env, env, tm, None )?;
      equate( fresh_env, env, &ty, &ty2 )?;
      Ok( ty )
    },
    (Term::Refl, None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::Subst( _, _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::Lam( _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::Prod( _, _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::LetPair( _, _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::Contra( _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
  }
}

fn def( env: &Env, x: Term, y: Term ) -> Option< Decl< FreeName > > {
  let x = whnf( env, x );
  let y = whnf( env, y );

  match (x, y) {
    (Term::Var( Name::Free( xn ) ), Term::Var( Name::Free( yn ) )) =>
      if xn == yn {
        None
      } else {
        Some( Decl::Def( xn, Term::Var( Name::Free( yn ) ) ) )
      },
    (Term::Var( Name::Free( xn ) ), y) =>
      Some( Decl::Def( xn, y ) ),
    (x, Term::Var( Name::Free( yn ) ) ) =>
      Some( Decl::Def( yn, x ) ),
    _ => None
  }
}
