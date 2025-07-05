Require Import List.
Require Import Arith.

Fixpoint inb {A} (dec : forall a b : A, {a=b}+{a<>b}) x l : bool :=
  match l with
    | nil => false
    | h::t => if dec x h
              then true
              else inb dec x t
  end.

Lemma UIBP :
  forall A (dec : forall a b : A, {a=b}+{a<>b}) x l (p1 p2 : inb dec x l = true),
    p1 = p2.
Proof.
  intros. apply Eqdep_dec.UIP_dec. clear. intros. destruct x, y; auto. right. intro. discriminate.
Qed.

Lemma inbeqIn :
  forall A dec (x : A) l,
    inb dec x l = true <-> In x l.
Proof.
  intros. split; [ intro inbl | intro Inl ].
  - revert x inbl. induction l.
    + simpl. intros. discriminate.
    + simpl. intros. destruct (dec x a) as [ xeqa | xnea ].
      * left. rewrite xeqa. reflexivity.
      * right. apply IHl. assumption.
  - revert x Inl. induction l.
    + simpl. intros. contradiction.
    + simpl. intros. destruct Inl as [ aeqx | Inl ].
      * rewrite aeqx in *. clear aeqx a.
        destruct (dec x x); auto.
      * destruct (dec x a); auto.
Qed.

Lemma inbeqInnot :
  forall A dec (x : A) l,
    inb dec x l = false <-> ~In x l.
Proof.
  intros.
  split; intro.
  - intro. rewrite <- (inbeqIn _ dec) in H0. rewrite H in H0. discriminate.
  - rewrite <- (inbeqIn _ dec) in H. destruct (inb dec x l). elim H. reflexivity.
    reflexivity.
Qed.
