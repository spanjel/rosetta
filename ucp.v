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
  intros. apply Eqdep_dec.UIP_dec. clear. intros. destruct x, y; firstorder; right; intro; discriminate.
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

Fixpoint is_set {A} (dec : forall a b : A, {a=b}+{a<>b}) l :=
  match l with
    | nil => true
    | h::t => if inb dec h t
              then false
              else is_set dec t
  end.

Lemma settail :
  forall A dec l (a : A),
    is_set dec (a::l) = true ->
    is_set dec l = true /\ ~In a l.
Proof.
  intros A dec l a set. split.
  - simpl in set. destruct (inb dec a l). discriminate. assumption.
  - intro inl.
    simpl in set. destruct (inb dec a l) eqn:inaldecres. discriminate.
    rewrite <- (inbeqIn _ dec) in inl.
    rewrite inaldecres in inl. discriminate.
Qed.

Lemma UIP_inp :
  forall A (dec : forall a b : A, {a=b}+{a<>b}) (l : list A) (spf : is_set dec l = true) x (p1 p2 : In x l), p1 = p2.
Proof.
  induction l. simpl. intros. elim p1.
  intros. assert (Hx := settail _ dec _ _ spf). simpl in *. destruct Hx, p1, p2; subst.
  - assert (Hx := Eqdep_dec.UIP_dec dec eq_refl e0). rewrite Hx. reflexivity.
  - elim H0. assumption.
  - elim H0. assumption.
  - assert (Hy := IHl H _ i i0). subst. reflexivity.
Qed.
