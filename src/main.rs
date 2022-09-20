mod unbound;
mod syntax;
mod parser;
mod typecheck;

// stdlib imports
use std::env;
use std::process::ExitCode;
use std::fs;
// external library imports
use nom_locate::LocatedSpan;
use unbound::{FreshVar, FreeName};
// local imports
use crate::{parser::{p_module, is_lex_end}, typecheck::tc_module};


type Span< 'a > = LocatedSpan< &'a str >;

struct FreshVarEnv( usize );

impl FreshVarEnv {
  pub fn new( ) -> FreshVarEnv {
    FreshVarEnv( 0 )
  }
}

impl FreshVar for FreshVarEnv {
  fn fresh_var( &mut self ) -> FreeName {
    let var = FreeName::Num( self.0 );
    self.0 += 1;
    var
  }
}

fn run( filename: &str, content: &str ) -> bool {
  // # Parse the file
  println!( "Parsing \"{}\"", filename );
  let m =
    if let Ok( (rem_content, m2) ) = p_module( Span::new( content ) ) {
      assert!( is_lex_end( rem_content ) );
      m2
    } else {
      println!( "Failed to parse module" );
      return false;
    };
  // # Type Check the file
  println!( "Typechecking \"{}\"", filename );
  let mut fresh_env = FreshVarEnv::new( );
  let ctx = 
    match tc_module( &mut fresh_env, &m ) {
      Ok( ctx ) => ctx,
      Err( err ) => {
        println!( "Failed to typecheck" );
        println!( "{}", err );
        return false;
      }
    };
  println!( "{}", ctx );
  println!( "Completed \"{}\"", filename );

  true
}

fn main( ) -> ExitCode {
  let args: Vec< String > = env::args( ).collect( );

  // `args[ 0 ]` is the executable path
  
  if args.len( ) < 2 {
    println!( "Insufficient arguments. Use: cargo run -- [filename]" );
    ExitCode::FAILURE
  } else if args.len( ) > 2 {
    println!( "Too many arguments. Unclear. Use: cargo run -- [filename]" );
    ExitCode::FAILURE
  } else {
    let filename = &args[ 1 ];
    
    if let Ok( content ) = fs::read_to_string( &filename ) {
      if run( filename, &content ) {
        ExitCode::SUCCESS
      } else {
        ExitCode::FAILURE
      }
    } else {
      println!( "Failed to read file \"{}\"", filename );
      ExitCode::FAILURE
    }
  }
}
