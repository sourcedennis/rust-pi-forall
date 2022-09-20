# Rust pi-forall

An implementation of [pi-forall](https://github.com/sweirich/pi-forall) in [Rust](https://www.rust-lang.org).

## Motivation

pi-forall is a demo dependently-typed programming language. Its reference implementation is written in [Haskell](https://www.haskell.org), which is accompanied by lecture notes. In this repository, I replicate that work in Rust.

I replicate the `full/` variant of pi-forall presented at OPLSS [2022](https://github.com/sweirich/pi-forall/tree/2022). Though, I only reimplemented *a subset* of features that I consider interesting. Also keep in mind that idiomatic Rust has a vastly different structure from idiomatic Haskell; No monads, nor its transformers.

## Running

First, [install Rust](https://www.rust-lang.org/tools/install). Then, run (in this directory):

```sh
cargo run --release -- Nat.pi
```

That typechecks `Nat.pi` in the `pi/` directory.
