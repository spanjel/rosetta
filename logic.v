Require Import List.
Require Export ucp.

Definition compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C := fun a => g (f a).

Lemma PthenQthenFAPthenFAQ : forall A (P Q : A -> Prop) l, (forall a, P a -> Q a) -> Forall P l -> Forall Q l.
Proof.
  intros. induction l. constructor.
  constructor. inversion H0. subst. auto.
  apply IHl. inversion H0. assumption.
Qed.

Lemma forallneqthennotin : forall A dec (a : A) l, Forall (fun x => x <> a) l -> inb dec a l = true -> False.
Proof.
  induction l. simpl. intros. discriminate.
  intros. simpl in *. destruct (dec a a0) eqn:aeqa0.
  - subst. apply IHl.
    + inversion H. assumption.
    + inversion H. elim H3. reflexivity.
  - apply IHl.
    + inversion H. assumption.
    + assumption.
Qed.

Lemma confiff :
  forall A P (l : list A),
    Forall P l ->
    (forall n, P n -> In n l) ->
    (forall n, P n <-> In n l).
Proof.
  intros A P l isP PthenIn.
  split; intro iffc.
  - apply PthenIn. assumption.
  - revert isP iffc. clear. intros.
    induction l.
      simpl in iffc. elim iffc.
    destruct iffc as [ aeqn | nIn ];
        [ subst | apply IHl; [ | assumption ] ];
        inversion isP; assumption.
Qed.

Lemma FAfe :
  forall A (P Q : A -> Prop) l, (forall a, P a -> Q a) -> Forall P l -> Forall Q l.
Proof.
  intros. induction l; auto.
  constructor; inversion H0; auto.
Qed.

Lemma demorgan1 :
  forall P Q, ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
  split; intros.
  split; intro; elim H; [ left | right ]; assumption. 
  intro. destruct H. destruct H0; [ elim H | elim H1 ]; assumption.
Qed.

Lemma if_involutive :
  forall A (pair : A -> A),
    (forall a, a = pair (pair a)) ->
    (forall a b : A, a <> b -> pair a <> b -> a <> pair b).
Proof.
  intros. intro. rewrite H2 in *. rewrite <- H in H1. elim H1. reflexivity.
Qed.

Lemma involutive_if :
  forall A (eq_dec : forall a b : A, {a=b}+{a<>b}) (pair : A -> A),
    (forall a b : A, a <> b -> pair a <> b -> a <> pair b) ->
    (forall a, a = pair (pair a)).
Proof.
  intros. destruct (eq_dec (pair a) a). do 2 rewrite e. reflexivity.
  destruct (eq_dec (pair (pair a)) a). rewrite e. reflexivity.
  exfalso.
  specialize H with (pair a) a.
  apply H. assumption. assumption. reflexivity.
Qed.

Definition constrain
           A
           (f : A -> A)
           (P Q : A -> Prop)
           (pf : forall a, P a -> Q a) :
  {x | P x} -> {x | Q x}.
Proof.
  intro. destruct X. exists x. apply pf. assumption.
Defined.

Lemma iffif :
  forall A
         (P : A -> Prop) (Q : A -> Prop)
         (pdec : forall a, {P a}+{~P a}) (qdec : forall a, {Q a}+{~Q a})
         (pthennq : forall a, P a -> ~Q a)
         (npthenq : forall a, ~P a -> Q a),
    (forall a, P a <-> ~Q a).
Proof.
  intros. split; intro.
  - intro. elim (pthennq _ H). assumption.
  - destruct (pdec a).
    + assumption.
    + elim H. apply npthenq. assumption.
Qed.

Lemma neqflip :
  forall A (a b : A) (pf : a <> b), b <> a.
Proof.
  intros. intro. rewrite H in *. elim pf. reflexivity.
Qed.

Lemma eq_flip : forall A (a b : A) (pf : a = b), b = a. intros. rewrite pf. reflexivity. Qed.
