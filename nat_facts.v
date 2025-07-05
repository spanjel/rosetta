Require Import Arith.
Require Import List.
Require Export logic.
Require Import Lia.

Lemma Olen : forall n, 0 <= n. intro. induction n. constructor. constructor. assumption. Qed.

Lemma SnleOef : forall n, S n <= 0 -> False.
Proof.
  induction n; intros.
  inversion H.
  apply IHn. inversion H.
Qed.

Lemma nlemSnleSm : forall n m, n <= m <-> S n <= S m.
Proof with lia.
  intros...
Qed.

Lemma nlemnnemnlem : forall n m, n <= m -> n <> m -> n < m.
Proof. intros. lia. Qed.

Definition nat_interval_ind k (P : nat -> Type) (pfk : forall n, n < k -> P n) (pfx : forall n, k <= n -> P n) : forall n, P n.
Proof.
  intro. revert n pfk pfx. induction k.
  - intros. apply pfx. apply Olen.
  - intros. apply IHk; intros; auto.
    clear IHk.
    destruct (eq_nat_dec k n0).
    + subst. apply pfk. unfold lt. constructor.
    + apply pfx. assert (Hx := nlemnnemnlem _ _ H n1). unfold lt in Hx. assumption.
Qed.

Definition confprops'' l P nn := 
  NoDup l /\
  Forall (fun x => x < nn) l /\
  Forall P l /\
  (forall n, n < nn -> P n -> In n l).

Definition confprops' (l : list nat) P := 
  NoDup l /\
  Forall P l /\
  (forall n, P n -> In n l).

Definition confprops (l : list nat) P := 
  NoDup l /\
  (forall n, P n <-> In n l).

Lemma areconf :
  forall (P : nat -> Prop)
         (ul : nat)
         (pful : forall n, ul <= n -> ~P n)
         l
         (conf : forall n, n < ul -> P n -> In n l),
    (forall n, P n -> In n l).
Proof.
  intros.
  apply conf; [ | assumption ]. clear conf.
  
  induction n using (nat_interval_ind ul). assumption.
  elim (pful _ H0). assumption.
Qed.

Lemma conformants :
  forall {P : nat -> Prop}
         {ul : nat}
         (pful : forall n, ul <= n -> ~P n)
         {l}
         (cpf : confprops'' l P ul),
    confprops' l P.
Proof.
  intros.
  unfold confprops', confprops'' in *.
  destruct cpf as [ isset [ falt [ fapf CthenIn ] ] ].
  split; [ assumption | ].
  split; [ assumption | ].
  apply areconf with ul.
  assumption.
  assumption.
Qed.

Lemma confpiff :
  forall l P, confprops' l P -> confprops l P.
Proof.
   intros. unfold confprops', confprops in *. destruct H as [ lset [ fap fapin ] ].
   split; [ assumption | ].
   apply confiff. assumption. assumption.
Qed.

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 ->
  (forall n:nat, P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 cut (P n /\ P (S n)).
 intros. destruct H. assumption.
 induction n. split; assumption.
 destruct IHn.
 split. assumption.
 apply HSSn. assumption. assumption.
Qed.
