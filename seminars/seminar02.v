Section PropositionalLogic.


From mathcomp Require Import ssreflect ssrfun.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:= fun '(conj a _) => a.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:= fun ab bc => bc \o ab.

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:= fun abc ab a => abc a (ab a).

Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
:=
  fun triple_negated_A =>
    fun a =>
      triple_negated_A (fun not_A => not_A a).

Locate "\/".
Print or.

Definition or_comm :
  A \/ B -> B \/ A
:=
  fun A_or_B =>
    match A_or_B with
    | or_introl a => or_intror a
    | or_intror b => or_introl b
    end.

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.
Locate "/\".
Print and.
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:=
  let and_comm_one_way {P Q : T -> Prop}: (forall x, P x /\ Q x) -> (forall x, Q x /\ P x) :=
    fun x_Px_Qx x =>
      match x_Px_Qx x with | conj Px Qx => conj Qx Px end
  in
  conj
    and_comm_one_way
    and_comm_one_way.

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:=
  let or_comm_one_way {P Q : T -> Prop} : (forall x, P x \/ Q x) -> (forall x, Q x \/ P x) :=
    fun x_Px_Qx x =>
      match x_Px_Qx x with
      | or_introl Px => or_intror Px
      | or_intror Qx => or_introl Qx
      end
  in
  conj
    or_comm_one_way
    or_comm_one_way.

Locate "exists".
Print ex.
Print ex_intro.

Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:= fun not_ex_x_Px x Px => not_ex_x_Px (ex_intro P x Px: exists x, P x).

Definition exists_forall_not_ :
(exists x, A -> P x) -> (forall x, ~P x) -> ~A := 
  fun '(ex_intro x aPx) x_implies_not_Px a =>
    x_implies_not_Px x (aPx a).

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).


Print conj.
Locate "\/".
Print or.
Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:=
  let LEM_implies_Frobenius2: LEM -> Frobenius2 :=
    fun LEM => fun A P Q =>
      let LEM_implies_Frobenius2_left_to_right : (forall x, Q \/ P x) -> (Q \/ forall x, P x) :=
        fun x_implies_Q_or_Px =>
          match LEM Q with
          | or_introl q => or_introl q
          | or_intror not_q => or_intror ((fun (x: A) => match x_implies_Q_or_Px x with
            | or_introl q => match not_q q with end
            | or_intror Px => Px
            end): forall x, P x)
          end
      in
      let LEM_implies_Frobenius2_right_to_left: (Q \/ forall x, P x) -> (forall x, Q \/ P x) :=
        fun Q_or_allxPx x => match Q_or_allxPx with
          | or_introl q => or_introl q
          | or_intror allxPx => or_intror (allxPx x)
        end
      in
      conj
        LEM_implies_Frobenius2_left_to_right
        LEM_implies_Frobenius2_right_to_left
  in
  let Frobenius2_implies_LEM: Frobenius2 -> LEM := fun Frobenius2 Q =>
    match Frobenius2 Q (fun q => False) Q with conj id_implies_lem _ => id_implies_lem (fun q => or_introl q) end
  in
  conj
    LEM_implies_Frobenius2
    Frobenius2_implies_LEM.

End Quantifiers.





Section Equality.

Locate "=".
Print eq.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:=
  fun x_eq_y =>
  match x_eq_y in (_ = b) return (f x = f b) with
  | eq_refl => eq_refl (f x)
  end.

Print f_congr.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=
  fun fg xy =>
    match fg in (_ = w) return (f x = w y) with
    | eq_refl => match xy in (_ = b) return (f x = f b) with
    | eq_refl => eq_refl
    end
    end.

(** extra exercise
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p := _. *)

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=
  fun eq =>
    match eq in (_ = (a2', b2')) return ((a1 = a2') /\ (b1 = b2')) with
    | eq_refl => conj eq_refl eq_refl
    end.

Print pair_inj.

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Locate "\o".
Print comp.

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= eq_refl.

Print compA.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)

Locate "=1".
Print eqfun.


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f x => eq_refl.

Print eqext_refl.

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f g eqf x => match eqf x in (_ = b) return (b = f x) with eq_refl => eq_refl end.

Print eqext_sym.
Print eq_refl.

Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
:=
  fun pf_xy : x = y =>
    match
      pf_xy in (_ = b)
      return (b = z -> x = z)
    with
    | eq_refl => fun (pf_xz : x = z) => pf_xz
    end.

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h f_eq_g g_eq_h x => eq_trans B (f x) (g x) (h x) (f_eq_g x ) (g_eq_h x).


Definition eqext_trans2 :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h f_eq_g g_eq_h x =>
    match f_eq_g x in (_ = b) return (b = h x -> f x = h x) with
    | erefl => id
    end (g_eq_h x).

Print eqext_trans2.


Print erefl.
Print eq_refl.
Print eqfun.


(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:= fun f g h f_eqf_g x => match f_eqf_g x in (_ = b) return ((h \o f) x = h b) with erefl => erefl end.

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:= fun f g h f_eqf_g a => match f_eqf_g (h a) in (_ = w) return ((f \o h) a = w) with erefl => erefl end.

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Locate "==>".
Print implb.
Locate "==".
Print eq_op.
Locate "eqType".
Print Equality.op.
Print Equality.class.
Print Equality.mixin_of.
Print Equality.axiom.
Print Bool.reflect.
Print "&&".
Print "=".
Print implb.

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= fun a b  => match a, b with
| true, true => erefl
| false, true => erefl
| true, false => erefl
| false, false => erefl
end.

Print iff_is_if_and_only_if.

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:=
