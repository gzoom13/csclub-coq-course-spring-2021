From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.



(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= conj
    (fun '(ex_intro x bx) => conj x bx)
    (fun '(conj a b) => ex_intro (fun _ => B) a b).



(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun eq => match eq in (_ = p2) return ((a1 = p2.1) /\ (b1 = p2.2)) with
| erefl => conj erefl erefl
end.

Print pair_inj.
Print eq.
Print erefl.


(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= fun _ P p_refl x _ p => match p as p0 in (_ = a) return (P x a p0) with erefl =>  p_refl x end.

Print J.


(** * Exercise *)
Definition false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False
:= fun n eq => match eq in (_ = b) return (if b is 0 then False else True) with erefl => I end.

Print false_eq_true_implies_False.

Print nat_rect.
Print nat_ind.

Definition addn0' :
  forall n : nat, n + 0 = n
:= @nat_ind
     (fun n => n + 0 = n)
     (erefl 0)
     (fun _ IHn => congr1 S IHn).

Print nat_ind.

Variable m: nat.

Compute (fun n : nat => m + n.+1 = (m + n).+1) 0.

Print eq_trans.
Print addn0'.
Print addn1.



(** * Exercise *)
Definition addnS :
  forall m n, m + n.+1 = (m + n).+1
:= fun m n =>
  let init : m + 0.+1 = (m + 0).+1 :=
    match addn0' m in (_ = m0) return (m0 + 1 = (m + 0).+1) with
    | erefl => addn1 m
    end
  in
  (@nat_ind
    (fun n => (m + n.+1 = (m + n).+1))
    (init)
    (_)) n.


(** * Exercise *)
Definition addA : associative addn
:= replace_with_your_solution_here.


(** * Exercise: *)
Definition addnCA : left_commutative addn
:= replace_with_your_solution_here.


(** * Exercise (optional): *)
Definition addnC : commutative addn
:= replace_with_your_solution_here.


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)


(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.

