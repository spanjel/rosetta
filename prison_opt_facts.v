Require Export prison_opt.
Require Import math.

Require Import List.
Require Import Arith.
Require Import Lia.

Record prisoostack : Set :=
  {
    ps_idx : nat; (*1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, ...*)
    ps_n : nat;   (*1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, ...*)
    ps_k : nat;   (*0, 2, 1, 0, 4, 3, 2, 1, 0, 6, 5, ...*)
    ps_kle : S (S ps_k) <= ps_n + ps_n;
    ps_idxksq : ps_n * ps_n = ps_idx + ps_k;
    ps_idxsqkz : issq ps_idx <-> ps_k = 0
  }.

Definition prisoostack_root : prisoostack.
Proof.
  refine (Build_prisoostack 1 1 0 _ _ _); auto.
  split; auto. intros _. unfold issq. exists 1. auto.
Defined.

Definition consnnil A (l : list A) (a : A) : {l : list A | l <> nil}.
Proof.
  exists (a::l). intro. discriminate.
Qed.

Definition nextsqrange (s : prisoostack) (kz : ps_k s = 0) : {s' | ps_idx s' = S (ps_idx s) /\ ps_n s' = S (ps_n s) /\ ps_k s' = (ps_n s) + (ps_n s)}.
Proof.
  destruct s. simpl in *. subst.
  set (res := Build_prisoostack (S ps_idx0) (S ps_n0) (ps_n0 + ps_n0)).

  assert (S (S (ps_n0 + ps_n0)) <= S ps_n0 + S ps_n0) as ps_kle'.
    lia.

  assert ((S ps_n0) * (S ps_n0) = (S ps_idx0) + (ps_n0 + ps_n0)) as ps_idxksq'.
    remember (S ps_n0) as n.
    subst. simpl. apply f_equal. rewrite Nat.mul_comm. simpl. rewrite ps_idxksq0. rewrite (Nat.add_comm _ 0). simpl. rewrite Nat.add_assoc. rewrite Nat.add_comm. reflexivity.

  assert (issq (S ps_idx0) <-> ps_n0 + ps_n0 = 0) as ps_idxsqkz'.
  - split; intro.
    + assert (issq ps_idx0). rewrite ps_idxsqkz0. reflexivity.
      assert (Hy := sqSnsq).
      destruct (eq_nat_dec ps_idx0 0).
      * subst. revert ps_idxksq0. clear. intros. simpl in *. destruct ps_n0. reflexivity.
        discriminate.
      * elim Hy with ps_idx0; assumption.
    + destruct ps_n0. simpl in *. rewrite Nat.add_comm in ps_idxksq0. simpl in *. subst. exists 1. reflexivity.
      discriminate.
  - exists (res ps_kle' ps_idxksq' ps_idxsqkz'); auto.
Defined.

Definition nextnsqelem (s : prisoostack) (knz : ps_k s <> 0) : {s' | ps_idx s' = S (ps_idx s) /\ ps_n s' = ps_n s /\ S (ps_k s') = ps_k s}.
Proof.
  destruct s. simpl in *.
  destruct ps_k0. elim knz. reflexivity.
  set (res := Build_prisoostack (S ps_idx0) ps_n0 ps_k0).

  assert (S (S ps_k0) <= ps_n0 + ps_n0) as ps_kle'.
    revert ps_kle0. clear. intro. lia.

  assert (ps_n0 * ps_n0 = (S ps_idx0) + ps_k0) as ps_idxksq'.
    simpl. rewrite ps_idxksq0. rewrite Nat.add_comm. simpl. rewrite Nat.add_comm. reflexivity.

  rename ps_k0 into k'.
  assert (issq (S ps_idx0) <-> k' = 0) as ps_idxsqkz'; [ clear knz res | ].
    split; intro; [ | exists ps_n0; rewrite ps_idxksq0; subst; rewrite Nat.add_comm; reflexivity ].
    assert (issq (ps_n0 * ps_n0)). exists ps_n0. reflexivity.
    destruct (eq_nat_dec k' 0) as [ kz | knz ]. assumption. exfalso.
    assert (S ps_idx0 < ps_n0 * ps_n0).
      rewrite ps_idxksq'. revert knz. clear. intro. lia.
    assert (S ps_idx0 <> 0). intro. discriminate H2.
    assert (Hx := minsqdiff _ _ H H0 H1 H2). rewrite NPeano.Nat.sqrt_square in Hx.
    rewrite ps_idxksq' in Hx. rewrite Nat.add_comm in Hx. rewrite NPeano.Nat.add_sub in Hx.
    simpl in Hx. lia.

  exists (res ps_kle' ps_idxksq' ps_idxsqkz'); auto.
Defined.
 
Definition xeqSynz {x y} (pf : x = S y) : x <> 0.
Proof.
  intro. destruct x. discriminate pf. discriminate H.
Qed.

Fixpoint prisoo'' nd s accu :=
  match nd with
    | O => rev accu
    | S nd' => let n := ps_n s in
               let k := ps_k s in
               let idx := ps_idx s in
               let ra := match k as kx return k = kx -> prisoostack with
                           | O => fun pf => proj1_sig (nextsqrange s pf)
                           | S k' => fun pf => proj1_sig (nextnsqelem s (xeqSynz pf))
                         end eq_refl
               in
               prisoo''
                 nd'
                 ra
                 (s::accu)
  end.

Lemma kzsq : forall s : prisoostack, ps_k s = 0 <-> issq (ps_idx s).
Proof.
  intros. destruct s. simpl in *.
  rewrite ps_idxsqkz0. split; intro; assumption.
Qed.

Definition s2b (s : prisoostack) := 
  match ps_k s with
    | 0 => true
    | S _ => false
  end.

Lemma prisoo'''eq :
  forall nd n k accu idx kle sq iff,
    map s2b (prisoo'' nd (Build_prisoostack idx n k kle sq iff) accu) = prisoo' nd n k (map s2b accu).
Proof.
  induction nd. simpl. intros. rewrite <- map_rev. reflexivity.
  intros. simpl. destruct k; simpl; rewrite IHnd; simpl; unfold s2b; simpl; reflexivity.
Qed.

Lemma prisooeq :
  forall nd, map s2b (prisoo'' nd prisoostack_root nil) = prisoo nd.
Proof.
  intros. unfold prisoo. unfold prisoostack_root. rewrite prisoo'''eq.
  simpl. reflexivity.
Qed.

Lemma prisoo_unfold' :
  forall nd s accu1 accu2,
    prisoo'' nd s (accu1++accu2) = rev accu2 ++ (prisoo'' nd s accu1).
Proof.
  induction nd. simpl. intros. rewrite rev_app_distr. reflexivity.
  intros. simpl. rewrite app_comm_cons.
  rewrite IHnd. reflexivity.
Qed.

Lemma prisoo_unfold :
  forall nd s accu,
    prisoo'' nd s accu = rev accu ++ (prisoo'' nd s nil).
Proof.
  intros. assert (accu = nil ++ accu). simpl. reflexivity.
  rewrite H at 1. rewrite prisoo_unfold'. reflexivity.
Qed.
