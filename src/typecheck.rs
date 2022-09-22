
// local imports
use crate::unbound::{FreshVar, Name, FreeName, Bind};
use crate::syntax::{Term, Type, Module, Decl};
use crate::environment::{Env, Ctx};
use crate::equal::{whnf};


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
          env2.extend_type( fname.clone( ), ty_hint.clone( ) );
          let term_type = tc_term( fresh_env, &env2, &term, Some( ty_hint.clone( ) ) )?;

          env.extend( fname, term.clone( ), term_type );
        } else {
          let term_type = tc_term( fresh_env, &env, &term, None )?;
          env.extend( fname, term.clone( ), term_type );
        }
      }
    }
  }

  Ok( env.into( ) )
}

fn tc_type< Fresh: FreshVar >(
  fresh_env: &mut Fresh,
  env: &Env,
  t: &Term
) -> Result< (), ErrorMsg > {
  tc_term( fresh_env, env, t, Some( Term::Type ) )?;
  Ok( () )
}

fn ensure_pi( t: Term ) -> Result< (Term, Bind<Term>), ErrorMsg > {
  match t {
    Term::Pi( ty_a, bnd ) => Ok( ( *ty_a, bnd.unbox() ) ),
    Term::Ann( t , _ ) => ensure_pi( *t ),
    _ => Err( format!( "Expected a function type but found {:?}", t ) )
  }
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
      env2.extend_type( x, *ty_a.clone( ) );
      tc_type( fresh_env, &env2, &ty_b )?; // Check: Γ,(x:A) ⊢ B : Type

      Ok( Term::Type ) // Then: Γ ⊢ (x : A) -> B : Type
    },
    (Term::Lam(bnd), Some( Term::Pi( ty_a, bnd2 ))) => {
      let (x, body, ty_b) = Bind::unbind2( fresh_env, bnd.clone( ), bnd2.clone( ) );

      // Check: Γ,(x:A) ⊢ body : B
      let mut env2 = env.clone( );
      env2.extend_type( x, *ty_a.clone( ) );
      tc_term( fresh_env, &env2, &body, Some( *ty_b ) )?;

      Ok( Term::Pi( ty_a.clone( ), bnd2 ) )
    },
    (Term::Lam( _ ), Some( ttype ) ) => Err( format!( "A lambda expression should have a function type, not {:?}", ttype ) ),
    (Term::App(t1, t2), None) => {
      // Infer:  Γ ⊢ t1 : (x : A) -> B
      let ty1 = tc_term( fresh_env, env, t1, None )?;
      let (ty_a, bnd) = ensure_pi( ty1 )?;
      // Check:  Γ ⊢ t2 : A
      tc_term( fresh_env, env, t2, Some( ty_a ) )?;

      Ok( bnd.instantiate( t2 ) )
    },
    (Term::Ann( tm, ty ), None) => {
      tc_type( fresh_env, env, ty )?;
      tc_term( fresh_env, env, tm, Some( *ty.clone( ) ) )?;
      Ok( *ty.clone( ) )
    },
    (Term::TyBool, None) => Ok( Term::Type ),
    (Term::LitBool( _ ), None) => Ok( Term::TyBool ),
    (Term::If( cond, x, y ), None) => {
      tc_term( fresh_env, env, cond, Some( Term::TyBool ) )?;
      let x_ty = tc_term( fresh_env, env, x, None )?; // infer
      let y_ty = tc_term( fresh_env, env, y, Some( x_ty ) )?; // check
      Ok( y_ty )
    },
    (Term::Sigma( x_ty, bnd ), None) => {
      // Check:  Γ ⊢ x_ty : Type
      tc_type( fresh_env, env, x_ty )?;

      let (x, y_ty) = bnd.clone( ).unbind( fresh_env );

      let mut env2 = env.clone( );
      env2.extend_type( x, *x_ty.clone( ) );
      // Check:  Γ,(x:x_ty) ⊢ y_ty : Type
      tc_type( fresh_env, &env2, &y_ty )?;

      Ok( Term::Type )
    },
    // This requires *checking*
    (Term::Prod( x, y ), Some( Term::Sigma( x_ty, bnd ) ) ) => {
      let (x_name, y_ty) = bnd.unbind( fresh_env );

      tc_term( fresh_env, env, x, Some( *x_ty.clone( ) ) )?;

      let mut env2 = env.clone( );
      env2.extend( x_name.clone( ), *x.clone( ), *x_ty.clone( ) );
      tc_term( fresh_env, &env2, y, Some( *y_ty.clone( ) ) )?;
      
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
          // TODO: Maybe, (x_name, y_name) ~ p
          
          let mut env2 = env.clone( );
          env2.extend_type( x_name, *x_ty );
          env2.extend_type( y_name, *y_ty );
          let ty = tc_term( fresh_env, &env2, &body, Some( ty ) )?; // Why is this checked? Can't we infer it?

          Ok( ty )
        },
        _ => Err( "Scrutinee must have a Sigma type".to_owned( ) )
      }
    },
    (Term::Prod( _, _ ), Some( ty ) ) =>
      Err( format!( "Products must have a Sigma Type, not {:?}", ty ) ),
    (tm, Some( ty ) ) => {
      let ty2 = tc_term( fresh_env, env, tm, None )?;
      if !ty.aeq( &ty2 ) {
        Err( format!( "Types don't match \"{:?}\" and \"{:?}\"", ty, ty2 ) )
      } else {
        Ok( ty )
      }
    },
    (Term::Lam( _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::Prod( _, _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
    (Term::LetPair( _, _ ), None) =>
      Err( format!( "Must have a type annotation to check {:?}", t ) ),
  }
}
