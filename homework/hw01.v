From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool := if b is true then true else c.

Compute orb true true.
Compute orb false false.
Compute orb true false.
Compute orb false true.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool := ...

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool := ...

Compute eqb ...
...
Compute eqb ...


(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat := ...

Compute dec2 ...
...
Compute dec2 ...


(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) : nat := ...

Compute subn ...
...
Compute subn ...

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint muln (m n : nat) : nat := ...

Compute muln ...
...
Compute muln ...

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool := ...

Compute eqn ...
...
Compute eqn ...

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq (m n : nat) : bool := ...

Compute leq ...
...
Compute leq ...


(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

(* n = q * m + r *)
(* n = 0 * m + r *)
Fixpoint divn_my_rec (m q r: nat) {struct r}: nat :=
  match (r - m) with
  | O => q
  | S r' => divn_my_rec m (S q) r'
  end.

Fixpoint divn (n m : nat) : nat :=
  if m is S m' then divn_my_rec m' 0 n else O.


(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)

End My.
