Require Import List.
Require Import Eqdep_dec.
Require Import Peano_dec.

Require Export prison.
Require Import list_facts.

Definition xorem l ll := map (fun e => xorb (fst e) (snd e)) (zipmin l ll).

Lemma replen :
  forall A (a : A) n,
    length (rep a n) = n.
Proof.
   induction n. simpl. reflexivity.
   simpl. rewrite IHn. reflexivity.
Qed.

Lemma zipmap_comm :
  forall A B (f : A -> A -> B) (_ : forall a aa, f a aa = f aa a) l ll,
    map (fun e => f (fst e) (snd e)) (zipmin l ll) = map (fun e => f (fst e) (snd e)) (zipmin ll l).
Proof.
  induction l. destruct ll; reflexivity.
  destruct ll. reflexivity.
  simpl. rewrite H. apply f_equal2; [ reflexivity | ].
  apply IHl.
Qed.

Lemma zipmap_assoc :
  forall A (f : A -> A -> A) (_ : forall a aa aaa, f a (f aa aaa) = f (f a aa) aaa) l ll lll,
    map (fun e => f (fst e) (snd e)) (zipmin l (map (fun e => f (fst e) (snd e)) (zipmin ll lll))) =
    map (fun e => f (fst e) (snd e)) (zipmin (map (fun e => f (fst e) (snd e)) (zipmin l ll)) lll).
Proof.
  induction l. destruct ll; reflexivity.
  destruct ll. reflexivity.
  intros.
  simpl. destruct lll; simpl; [ reflexivity | ].
  rewrite H. rewrite IHl. reflexivity.
Qed.

Lemma xorem_length :
  forall l ll,
    length l = length ll ->
    length (xorem l ll) = length l.
Proof.
  induction l. simpl. reflexivity.
  intros. simpl. destruct ll. simpl in H. discriminate H.
  simpl. unfold xorem in *. rewrite IHl. reflexivity.
  simpl in H. inversion H. auto.
Qed.

Lemma xorem_comm :
  forall l ll,
    xorem l ll = xorem ll l.
Proof.
  unfold xorem. apply zipmap_comm. destruct a, aa; reflexivity.
Qed.

Lemma xorem_assoc :
  forall l ll lll,
    xorem l (xorem ll lll) = xorem (xorem l ll) lll.
Proof.
  unfold xorem. apply zipmap_assoc. destruct a, aa, aaa; reflexivity.
Qed.

Lemma flipxor :
  forall l n k,
    flip l n k = xorem (flip (rep false (length l)) n k) l.
Proof.
  induction l. simpl. reflexivity.
  intros. unfold xorem in *. simpl.
  destruct k; simpl; apply f_equal2; destruct a; simpl; try reflexivity; rewrite IHl; reflexivity.
Qed.

Lemma flipeachxor :
  forall l n,
    flipeach l n = xorem (flipeach (rep false (length l)) n) l.
Proof.
  unfold flipeach. intros. apply flipxor.
Qed.

Lemma flip_length : forall l n k, length (flip l n k) = length l.
Proof.
  induction l; auto.
  simpl. destruct k.
  - simpl. rewrite IHl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma flipeach_length : forall l n, length (flipeach l n) = length l.
Proof.
  induction l; auto.
  simpl. destruct n;
  simpl; rewrite flip_length; reflexivity.
Qed.

Lemma flipwhile_length :
  forall n l,
    length (flipwhile l n) = length l.
Proof.
  induction n. simpl. intros. rewrite flipeach_length. reflexivity.
  intros. simpl. rewrite IHn. rewrite flipeach_length. reflexivity.
Qed.

Lemma flipwhilexor :
  forall n l,
    flipwhile l n = xorem (flipwhile (rep false (length l)) n) l.
Proof.
  induction n. simpl. intros. apply flipeachxor.
  destruct l.
  -  simpl. rewrite IHn. clear IHn.
     unfold xorem. unfold flipeach. unfold flip.
     simpl. repeat rewrite zipminlnil. reflexivity.
  - simpl. rewrite IHn. rewrite (IHn (flipeach _ _)). rewrite flipeachxor at 2.
    rewrite xorem_assoc.
    apply f_equal2; [ | reflexivity ].
    repeat rewrite flipeach_length.
    simpl. rewrite replen. reflexivity.
Qed.

Lemma flipflip : forall l n1 k1 n2 k2, flip (flip l n1 k1) n2 k2 = flip (flip l n2 k2) n1 k1.
Proof.
  intros.
  rewrite (flipxor (flip l n2 _) n1).
  rewrite (flipxor l n2).
  rewrite (flipxor (flip l _ _)).
  rewrite (flipxor l).
  rewrite xorem_length. rewrite flip_length. rewrite replen.
  rewrite xorem_length. rewrite flip_length. rewrite replen.
  remember (rep _ (length l)).
  remember (flip _ n2 _).
  remember (flip _ n1 _).
  rewrite xorem_assoc. rewrite (xorem_comm l1 l2). rewrite xorem_assoc. reflexivity.
  rewrite flip_length. rewrite replen. reflexivity.
  rewrite flip_length. rewrite replen. reflexivity.
Qed.

Lemma flipeachflipeach : forall l n1 n2, flipeach (flipeach l n1) n2 = flipeach (flipeach l n2) n1.
Proof.
  intros.
  rewrite flipeachxor. rewrite flipeach_length.
  rewrite (flipeachxor _ n1).
  rewrite (flipeachxor l).
  rewrite (flipeachxor (xorem _ _)).
  rewrite xorem_length. rewrite flipeach_length. rewrite replen.
  remember (rep false _).
  remember (flipeach _ n1).
  remember (flipeach _ n2).
  rewrite xorem_assoc. rewrite (xorem_comm l2 l1).
  rewrite xorem_assoc. reflexivity.
  rewrite flipeach_length. rewrite replen. reflexivity.
Qed.

Lemma flipwhileflipwhile : forall n1 n2 l, flipwhile (flipwhile l n1) n2 = flipwhile (flipwhile l n2) n1.
Proof.
  intros.
  rewrite flipwhilexor. rewrite flipwhile_length.
  rewrite (flipwhilexor n1).
  rewrite (flipwhilexor _ l).
  rewrite (flipwhilexor _ (xorem _ _)). rewrite xorem_length. rewrite flipwhile_length. rewrite replen.
  remember (flipwhile _ n2). remember (flipwhile _ n1).
  rewrite xorem_assoc. rewrite (xorem_comm l0 l1). rewrite xorem_assoc. reflexivity.
  rewrite flipwhile_length. rewrite replen. reflexivity.
Qed.

Lemma flipeach0neg :
  forall l,
    flipeach l 0 = map negb l.
Proof.
  induction l. simpl. reflexivity.
  unfold flipeach in *. simpl in *.
  rewrite <- IHl. reflexivity.
Qed.

Lemma flipwhileflipeach :
  forall n1 n2 l,
    flipwhile (flipeach l n1) n2 = flipeach (flipwhile l n2) n1.
Proof.
  intros.
  rewrite flipwhilexor. rewrite flipeach_length.
  rewrite (flipwhilexor n2 l).
  rewrite flipeachxor.
  rewrite (flipeachxor (xorem _ _) n1).
  rewrite xorem_length. rewrite flipwhile_length. rewrite replen.
  remember (flipwhile _ _).
  remember (flipeach _ _).
  rewrite xorem_assoc. rewrite (xorem_comm l0 l1). rewrite xorem_assoc. reflexivity.
  rewrite flipwhile_length. rewrite replen. reflexivity.
Qed.
