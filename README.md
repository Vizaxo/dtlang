# dtlang

This is a simple dependently-typed language, intended to be suitable as a core for more expressive dependently-typed languages to compile into. In that spirit it has no type inference, implicit arguments, or typeclasses.


## Types

The language is based on a simple dependently-typed lambda calculus, extended with generalised algebraic datatypes and a case construct for deconstructing these datatypes.

There is a hierarchy of universe levels (a universe at level n is denoted by `Type n`), with the property `Type n : Type (n+1)`. Note that currently these are not cumulative (i.e. `a : Type n` means that `a` does not have type `Type (n+1)`), and there is no universe polymorphism.


## Syntax

The user-facing syntax currently uses a syntax similar to s-expressions to facilitate easy parsing.

For example, here is the identity function (at type universe 0, with the type of the argument explicitly provided):
```
(lambda (A (Type 0)) (lambda (x A) x))
```
```
>>> (lambda (A (Type 0)) (lambda (x A) x)) : (Pi (A (Type 0)) (Pi (x A) A))
```

Function application is denoted by enclosing the function and the argument in parentheses:
```
(((lambda (A (Type 0)) (lambda (x A) x)) Nat) Zero)
```
```
>>> Zero : Nat
```

Datatypes can be defined by providing the name, type, and each of the constructors. Each constructor has a name and a type.
```
(data Nat (Type 0)
  (Zero Nat)
  (Succ (Pi (n Nat) Nat)))
```

The case construct scrutinises an expression, mapping each constructor (possibly binding a variable) to an expression.
```
(case (Succ Zero)
  ((Zero) Zero)
  ((Succ (n Nat)) (Succ (Succ n))))
```
```
>>> (Succ (Succ Zero)) : Nat
```

## Running

To build:
```sh
stack build
```

The repl can be run with:
```sh
stack exec dtlang-repl
```
