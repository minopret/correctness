(* Revision of my Documents/2012/divalg.v
   Aaron Mansheim
   2013-05-30
   2013-08-22
*)

(*
(* The following commented-out code shows
   how to recreate the standard definitions
   that we use. *)

(* Just enough theory of functions. *)
(* The standard name for this is [f_equal]. *)
Theorem functionality :
  forall {X Y: Type} (f : X -> Y) (x1 x2 : X),
  x1 = x2 -> f x1 = f x2.
Proof. intros X Y f x1 x2 H. rewrite H. reflexivity.
Qed.

(* Just enough propositional logic. *)
Inductive False : Prop := .
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).
Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Notation "P \/ Q" := (or P Q) : type_scope.


(* Just enough digital logic. *)
Inductive bool : Type :=
| true : bool
| false : bool.

Definition andb (a b : bool) : bool :=
if a then if b then true else false else false.

Definition negb (a : bool) : bool :=
if a then false else true.
*)

(*
(* "God made the integers. All the rest is the
work of Man." *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
*)

(* Just enough order theory. *)
Fixpoint ble_nat (n m : nat) : bool :=
match n with
| O => true
| S n' => match m with
  | O => false
  | S m' => ble_nat n' m'
  end
end.

Definition beq_nat (n m : nat) : bool :=
andb (ble_nat n m) (ble_nat m n).

Theorem beq_nat__eq : forall (n m : nat),
true = beq_nat n m -> n = m.
Proof. intros n. induction n as [|n'].
(* Case n = O. *) intros m. destruct m.
  (* Case m = O. *) intros H. reflexivity.
  (* Case m = S m'. *) intros H. inversion H.
(* Case n = S n'. *) intros m. induction m as [|m'].
  (* Case m = O. *) intros H. inversion H.
  (* Case m = S m'. *) simpl. intros H.
    apply (f_equal S).
    apply (IHn' m'). unfold beq_nat in H.
    simpl in H. unfold beq_nat.
    apply H. Qed.


Fixpoint blt_nat (n m : nat) : bool :=
andb (ble_nat n m) (negb (ble_nat m n)).


(*
(* Just enough arithmetic. *)

Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

(* Notation "n + m" := (plus n m) : type_scope. *)

Theorem plus_0_r : forall n : nat,
plus n O = n.
Proof. intros n. induction n as [|n'].
(* Case n = O. *) reflexivity.
(* Case n = S n'. *) simpl. rewrite IHn'.
  reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
S (plus n m) = plus n (S m).
Proof. intros n. induction n as [|n'].
(* Case n = O. *) reflexivity.
(* Case n = S n'. *) simpl. intros m.
  rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
plus n m = plus m n.
Proof. intros n. induction n as [|n'].
(* Case n = O. *) intros m. rewrite plus_0_r.
  reflexivity.
(* Case n = S n'. *) intros m. simpl.
  rewrite <- plus_n_Sm. rewrite IHn'.
  reflexivity. Qed.

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

(* Notation "n * m" := (mult n m) : type_scope. *)
*)

Require Import Coq.Arith.Plus.

(* Division. Hooray! *)
Theorem divalg : forall m n : nat, exists q : nat,
  exists r : nat, n = plus (mult q m) r.
Proof. intros m. destruct m as [|m'].
(* Case m = O. *) intros n. exists O. exists n.
  reflexivity.
(* Case m = S m'. *) intros n. induction n as [|n'].
  (* Case n = O. *) exists O. exists O. reflexivity.
  (* Case n = S n'. *) inversion IHn' as [q' Hq'].
    inversion Hq' as [r' Hr'].
    remember (beq_nat r' m') as K.
    destruct K.
    (* Case r' = m'. *) exists (S q'). exists O.
      simpl. rewrite plus_0_r. rewrite plus_comm.
      apply beq_nat__eq in HeqK.
      rewrite HeqK in Hr'. rewrite <- Hr'.
      reflexivity.
    (* Case r' != m'. *) exists q'. exists (S r').
      rewrite <- plus_n_Sm. rewrite <- Hr'.
      reflexivity.
Qed.

Theorem divalgT : forall m n : nat,
(*  {q : nat & {r : nat & n = plus (mult q m) r}}. *)
  {p : nat * nat & n = plus (mult (fst p) m) (snd p)}.
Proof. intros m. destruct m as [|m'].
(* Case m = O. *) intros n. exists (O, n). reflexivity.
(* Case m = S m'. *) intros n. induction n as [|n'].
  (* Case n = O. *) exists (O, O). reflexivity.
  (* Case n = S n'. *) inversion IHn' as [p' Hp'].
    remember (beq_nat (snd p') m') as K.
    destruct K.
    (* Case r' = m'. *) exists (S (fst p'), O).
      simpl. rewrite plus_0_r. rewrite plus_comm.
      apply beq_nat__eq in HeqK.
      rewrite HeqK in Hp'. rewrite <- Hp'.
      reflexivity.
    (* Case r' != m'. *) exists (fst p', S (snd p')). simpl.
      rewrite <- plus_n_Sm. rewrite <- Hp'.
      reflexivity.
Qed.


Extraction Language Haskell.
Set Extraction AccessOpaque. (* Extraneous before or after Coq 8.4pl2 *)
(*
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
*)
Extraction "/Users/aaron/divalgT.hs" divalgT.
