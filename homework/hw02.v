From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.


(** * Arithmetic expression language *)


(** NOTE: If you don't need this homework graded for you university,
          please, do _not_ submit it through the CS club website. *)

(** NOTE: In a later homework we are going to prove some properties of the
functions this homework asks you to implement. Please keep your code so you can
reuse it later. *)


(** Define is a simple language of arithmetic expressions consisting of
constants (natural numbers) and arbitrarily nested additions, subtractions and
multiplications *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr  & expr
| Mult of expr & expr
.

(** Let us define a special notation for our language.
    We reuse the standard arithmetic notations here, but only inside
    double square brackets (see examples below) *)

(* This means we declare `expr` as an identifier referring to a 'notation
entry' *)
Declare Custom Entry expr.
(* And we let the parser know `expr` is associated with double brackets, so
inside double brackets the parser will use notations associated with custom
`expr` entries *)
Notation "'[[' e ']]'" := e (e custom expr at level 0).

(* Numerals can be used without wrapping those in the `Const` constructor *)
Notation "x" :=
  (Const x)
    (in custom expr at level 0, x bigint).

Notation "( x )" := x (in custom expr, x at level 2).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).

(* Define notations for subtraction and multiplication.
   Hint: lower level means higher priority.
   Your notations should start with `in custom expr` as above. *)
Notation "x - y" := (Minus x y) (in custom expr at level 2, left associativity).
Notation "x * y" := (Mult x y) (in custom expr at level 1, left associativity).

(** Here is how we write Plus (Const 0) (Plus (Const 1) (Const 2)) *)
Check [[
          0 + (1 + 2)
      ]].
(** And this is Plus (Plus (Const 0) (Const 1)) (Const 2) *)
Check [[
          (0 + 1) + 2
      ]].

(* Make sure the following are parsed as expected.
   What query can you use to do that? *)
Unset Printing Notations.
Check [[
          ((0 + 1) + 2) + 3
      ]].
Check [[
          0 + (1 + (2 + 3))
      ]].
Check [[
          0 * 1 + 2
      ]].
Check [[
          0 + 1 * 2
      ]].
Set Printing Notations.

(** Write an evaluator for the expression language which fixes its semantics.
Basically, the semantics of the expression language should be the same as
the corresponding Coq functions `addn`, `subn`, `muln`. *)
Fixpoint eval (e : expr) : nat :=
  match e with
  | Const c => c
  | Plus a b => (eval a) + (eval b)
  | Minus a b => (eval a) - (eval b)
  | Mult a b => (eval a) * (eval b)
  end.

(** Some unit tests *)
(** We haven't discussed in depth what `erefl` means yet.
    But for now, let's just assume if the following lines
    typecheck then the equalities below hold *)
Check erefl : eval [[ 0 ]] = 0.
Check erefl : eval [[ 1 ]] = 1.
Check erefl : eval [[ 1 + 2 ]] = 3.
Check erefl : eval [[ 2 - 1 ]] = 1.
Check erefl : eval [[ 0 - 4 ]] = 0.
Check erefl : eval [[ 0 + (2 - 1) ]] = 1.
Check erefl : eval [[ (0 + 1) + 2 ]] = 3.
Check erefl : eval [[ 2 + 2 * 2 ]] = 6.
Check erefl : eval [[ (2 + 2) * 2 ]] = 8.



(** * Compiling arithmetic expressions to a stack language *)

(** Here is a "low-level" stack language which can serve as the target language
for a compiler from the arithmetic expression language above.
See, for instance, this page for more detail:
https://en.wikipedia.org/wiki/Stack-oriented_programming.

A program in this language is a list of instructions, each of which manipulates
a stack of natural numbers. There are instructions for pushing constants onto
the stack and for adding/subtracting/muliplying the top two elements of the
stack, popping them off the stack, and pushing the result onto the stack. *)

Inductive instr := Push (n : nat) | Add | Sub | Mul.

(*
Feel free to define your own notations for the stack operations
to make it easier writing unit tests
For example, this is one possible way to start:

Notation " << n >> " := (Push n) (at level 0, n constr).
*)


Notation " << n >> " := (Push n) (at level 0, n constr).
Notation " +++ " := (Add) (at level 0).
Notation " --- " := (Sub) (at level 0).
Notation " *** " := (Mul) (at level 0).


(* Feel free to either define your own datatype to represent lists or reuse the
`seq` datatype provided by Mathcomp (this is why this file imports the `seq`
module at the beginning). Btw, `seq` is just a notation for the standard `list`
datatype.

    Inductive list (A : Type) : Type :=
      | nil
      | cons of A & list A.

You can construct new lists (sequences) like so:
  - [::]           --  notation for the `nil` constructor;
  - x :: xs        --  notation for the `cons` constructor;
  - [:: 1; 2; 3]   --  notation for a sequence of three elements 1, 2 and 3.

Using `seq`, we can define the type of programs as follows:

    Definition prog := seq instr.

And the type of stacks like so:

    Definition stack := seq nat.
*)

Definition prog := seq instr.
Definition stack := seq nat.

Check [:: << 3 >>; << 4 >>; +++] : prog.

(** The [run] function is an interpreter for the stack language. It takes a
 program (list of instructions) and the current stack, and processes the program
 instruction-by-instruction, returning the final stack. *)
Fixpoint run (p : prog) (s : stack) {struct p}: stack :=
  let op f := if s is a :: b :: xs then (f b a) :: xs else s
  in
  match p with
  | nil => s
  | Push n :: p' => run p' (n :: s)
  | Add :: p' => run p' (op addn)
  | Sub :: p' => run p' (op subn)
  | Mul :: p' => run p' (op muln)
  end.

(** Unit tests: *)
Check erefl :
  run [:: << 3 >>; << 4 >>; +++] [::] = [:: 7].
Check erefl :
  run [:: << 3 >>; << 4 >>; ***] [:: 15] = [:: 12; 15].
Check erefl :
  run [:: ***] [:: ] = [:: ].
Compute run [:: << 4 >>; << 2 >>; ---] [:: 15] .
Check erefl :
  run [:: << 4 >>; << 2 >>; ---] [:: 15] = [:: 2; 15].


(** Now, implement a compiler from "high-level" expressions to "low-level" stack
programs and do some unit tests. *)
Fixpoint compile (e : expr) : prog :=
  match e with
  | Const c => [:: << c >>]
  | Plus a b => (compile a) ++ (compile b) ++ [:: +++]
  | Minus a b => (compile a) ++ (compile b) ++ [:: ---]
  | Mult a b => (compile a) ++ (compile b) ++ [:: ***]
  end.

(** Do some unit tests *)


Check erefl :
  compile [[ (2 + 2) * 2 ]] = [:: << 2 >>; << 2 >>; +++; << 2 >>; *** ].

Check erefl :
  compile [[ 2 + 2 * 2 ]]  = [:: << 2 >>; << 2 >>; << 2 >>; ***; +++ ].
Check erefl :
  compile [[ 4 - 2 ]] = [:: << 4 >>; << 2 >>; --- ].
Check erefl :
  run (compile [[ 4 - 2 ]]) [::] = [:: 2].



Variables a b c : nat.
Variables e1 e2 : expr.
Check erefl : run (compile (Const c)) [::] = [:: eval (Const c)].
Fail Check erefl : run (compile (Plus (Const a) (e2))) [::] = [:: eval (Plus (Const a) (e2))].


...
(* Some ideas for unit tests:
  - check that `run (compile e) [::] = [:: eval e]`, where `e` is an arbitrary expression;
  - check that `compile` is an injective function
*)


(** Optional exercise: decompiler *)

(** Implement a decompiler turning a stack program into the corresponding
expression *)
(* Hint: you might want to introduce a recursive helper function `decompile'` to
 reuse it for `decompile`. *)
Definition decompile (p : prog) : option expr :=
  ...

(** Unit tests *)
Check erefl :
  decompile [:: ... stack-program ] = some [[ expression ]].
...

(* Some ideas for unit tests:
  - check that `decompile (compile e) = Some e`, where `e` is an arbitrary expression
*)
