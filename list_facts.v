Require Import NPeano.
Require Import List.
Require Export ucp.
Require Export logic.
Require Export nat_facts.

Lemma eq_bool_dec : forall a b : bool, {a=b}+{a<>b}. decide equality. Qed.

Lemma remove_corr_neq :
  forall A dec (l : list A) a b,
    a <> b ->
    (In b l <->
     In b (remove dec a l)).
Proof.
  induction l. simpl. intros. split; intro; assumption.
  rename a into h. intros. rename H into aneb. split; [ intro binhl | intro binrahl ].
  - simpl in binhl. destruct binhl.
    + subst. simpl. destruct (dec a b). elim aneb. assumption.
      simpl. left. reflexivity.
    + simpl. destruct (dec a h).
      * subst. apply IHl; assumption.
      * simpl. destruct (dec h b). left. assumption.
        right. apply IHl; assumption.
  - simpl in *. destruct (dec a h).
    + subst. right. rewrite <- IHl in binrahl; assumption.
    + destruct (dec h b). left. assumption.
      right. simpl in *. destruct binrahl. elim n0. assumption.
      rewrite <- IHl in H; assumption.
Qed.

Lemma rmnothing :
  forall A dec l (a : A),
    ~In a l ->
    l = remove dec a l.
Proof.
  induction l. reflexivity.
  intros b nin. simpl in *. rewrite demorgan1 in nin. destruct nin as [ aneb bninl ].
  destruct (dec b a) as [ beqa | bnea ].
  - rewrite beqa in *. elim aneb. reflexivity.
  - rewrite <- IHl. reflexivity. assumption.
Qed.

Ltac innil := match goal with H: In _ nil |- _ => simpl in H; contradiction H end.
Ltac xneqx := match goal with H: ?x <> ?x |- _ => elim H; reflexivity end.

Lemma Inremoveidem :
  forall A dec (l : list A) a b,
    ~In a l ->
    ~In a (remove dec b l).
Proof.
  intros. intro.
  elim H. clear H.
  rename H0 into ainrbl.
  destruct (inb dec b l) eqn:binlres.
  - destruct (dec a b). subst. elim (remove_In dec l b). assumption.
    clear binlres. revert a b ainrbl n. induction l. simpl. intros. assumption.
    rename a into h. intros.
    simpl in *. destruct (dec b h) as [ beqh | bneh ].
    + right. subst. apply (IHl a h); auto.
    + destruct (dec h a). left. assumption.
      right. apply (IHl a b); auto.
      simpl in ainrbl. destruct ainrbl; auto.
      elim n0. assumption.
  - assert (forall b, b = false -> b <> true). clear. intros. destruct b. discriminate. intro. discriminate.
    assert (binlres' := H _ binlres).
    rewrite inbeqIn in binlres'.
    rewrite <- rmnothing in ainrbl; auto.
Qed.

Lemma setrm :
  forall A dec (l : list A),
    is_set dec l = true ->
    (forall a, is_set dec (remove dec a l) = true).
Proof.
  induction l as [ | h l ]. simpl. reflexivity.
  intros set a. destruct (settail _ _ _ _ set) as [ lset hninl ]. clear set. simpl.
  assert (Hx := IHl lset). clear IHl. rename Hx into IHl.
  destruct (dec a h) as [ aeqh | aneh ].
  - subst. apply IHl.
  - simpl. rewrite IHl. clear IHl.
    destruct (inb dec h (remove _ _ _)) eqn:hinralres.
    + elim (Inremoveidem _ dec l h a hninl).
      rewrite inbeqIn in hinralres.
      assumption.
    + reflexivity.
Qed.

Lemma lrm :
  forall A dec (l : list A),
    is_set dec l = true ->
    forall x, In x l ->
    length l = S (length (remove dec x l)).
Proof.
  induction l. intros _ x innil. simpl in innil. contradiction innil.
  intros set x inal.
  destruct (settail _ _ _ _ set) as [ tset ninl ]. clear set.
  simpl in inal. destruct inal as [ aeqx | inl ].
  - rewrite aeqx in *. clear aeqx a.
    simpl.
    destruct (dec x x) as [ _ | xnex ]; [ | elim xnex; reflexivity ].
    assert (rmidem := rmnothing _ dec l x ninl).
    rewrite <- rmidem in *. reflexivity.
  - simpl.
    destruct (dec x a) as [ xeqa | xnea ].
    + rewrite xeqa in *. clear xeqa x. elim ninl. apply inl.
    + simpl in *.
      assert (indhyp := IHl tset x inl).
      rewrite indhyp. reflexivity.
Qed.

Lemma remove_assoc :
  forall A dec (l : list A) a b,
    remove dec a (remove dec b l) = remove dec b (remove dec a l).
Proof.
  induction l. simpl. reflexivity.
  rename a into h.
  intros a b.
  simpl.
  destruct (dec b h); destruct (dec a h); subst; try rewrite IHl; try reflexivity; simpl;
  destruct (dec h h); try reflexivity; try match goal with H: ?x <> ?x |- _ => elim H; reflexivity end.
  destruct (dec b h); destruct (dec a h); subst; try rewrite IHl; try reflexivity; simpl. elim n. reflexivity.
  elim n0. reflexivity.
Qed.

Lemma removetwo :
  forall A eq_dec (l : list A),
    is_set eq_dec l = true ->
    (forall a,
       In a l ->
       (forall b rbral,
          rbral = remove eq_dec b (remove eq_dec a l) ->
          if eq_dec a b
          then length l = S (length rbral)
          else if inb eq_dec b l
               then length l = S (S (length rbral))
               else length l = S (length rbral)
       )
    ).
Proof.
  intros A dec l set a ainl b rbral rbraldef.
  destruct (dec a b) as [ aeqb | aneb ].
  - subst.
    assert (lenrbrbl := lrm _ _ _ set _ ainl).
    assert (bnilrbl := remove_In dec l b).
    assert (leqrbl := rmnothing _ dec _ _ bnilrbl).
    rewrite <- leqrbl.
    assumption.
  - destruct (inb dec b l) eqn:binl.
    + assert (lenral := lrm _ _ _ set _ ainl).
      assert (ralset := setrm A dec l set a).
      rewrite inbeqIn in binl.
      generalize binl; intro binral.
      rewrite (remove_corr_neq _ dec l _ _ aneb) in binral.
      assert (lenrbral := lrm _ _ _ ralset _ binral).
      rewrite lenrbral in lenral.
      rewrite rbraldef.
      apply lenral.
    + rewrite rbraldef in *. clear rbral rbraldef.
      rewrite inbeqInnot in binl.
      assert (bninral := Inremoveidem _ dec l _ a binl).
      assert (raleqrbral := rmnothing _ dec _ _ bninral).
      rewrite <- raleqrbral.
      apply lrm; auto.
Qed.

Lemma removepairs :
  forall A eq_dec (l : list A) (pair : A -> A),
    is_set eq_dec l = true ->
    (forall a, In a l -> In (pair a) l) ->
    (forall a,
       In a l ->
       (forall rbral,
          rbral = remove eq_dec (pair a) (remove eq_dec a l) ->
          if eq_dec a (pair a)
          then length l = S (length rbral)
          else length l = S (S (length rbral))
       )
    ).
Proof.
  intros A eq_dec l pair set pairIn a ainl rbral rbraleq.
  assert (Hx := removetwo _ eq_dec l set a ainl (pair a) rbral rbraleq).
  destruct (eq_dec a (pair a)) as [ aeqpa | anepa ].
  - assumption.
  - destruct (inb eq_dec (pair a) l) eqn:inres.
    + assumption.
    + assert (Hy := pairIn _ ainl).
      rewrite inbeqInnot in inres. elim inres. assumption.
Qed.

Lemma setrmhd :
  forall A eq_dec (a : A) l,
    is_set eq_dec (a::l) = true ->
    remove eq_dec a (a::l) = l.
Proof.
  intros.
  destruct (settail _ _ _ _ H) as [ lset aninl ].
  simpl. destruct (eq_dec a a). rewrite <- (rmnothing). reflexivity. assumption.
  elim n. reflexivity.
Qed.

Lemma list_eo_ind :
  forall A (P : list A -> Prop),
    P nil ->
    (forall a, P (a::nil)) ->
    (forall a b l, P l -> P (a::b::l)) ->
    forall l, P l.
Proof.
  intros. destruct l. assumption.
  assert (P l /\ P (a::l)).
  revert a. induction l.
  - intros. split. assumption. apply H0.
  - intros. destruct (IHl a). split. assumption.
    apply H1; assumption.
  - destruct H2. assumption.
Qed.

Lemma setsigeq :
  forall A eq_dec (P : {l : list A | is_set eq_dec l = true} -> Prop) lx ly,
    lx = ly ->
    (forall py px, P (exist _ lx px) = P (exist _ ly py)).
Proof.
  intros. subst. assert (px = py). apply (@Eqdep_dec.UIP_dec _ eq_bool_dec _ _).
  rewrite H. reflexivity.
Qed.

Lemma set_ind :
  forall A eq_dec (P : {l | is_set eq_dec l = true} -> Prop),
    (forall nilpf, P (exist _ nil nilpf)) ->
    (forall (a : A) lpf ralpf, P (exist _ (remove eq_dec a (proj1_sig lpf)) ralpf) -> P lpf) ->
    forall l, P l.
Proof.
  intros. destruct l as [ l set ].
  induction l. apply H.
  assert (Hset := setrm A eq_dec (a::l) set a).
  apply (H0 a (exist _ (a::l) set) Hset).
  destruct (settail _ _ _ _ set) as [ lset aninl ].
  assert (raaleql := setrmhd _ _ _ _ set).
  rewrite (setsigeq _ _ P (remove eq_dec a (a::l)) l raaleql lset).
  apply IHl.
Qed.

Lemma set_eo_ind :
  forall A eq_dec (P : {l | is_set eq_dec l = true} -> Prop),
    (forall nilpf, P (exist _ nil nilpf)) ->
    (forall a opf, P (exist _ (a::nil) opf)) ->
    (forall (a b : A) lpf rarblpf, P (exist _ (remove eq_dec b (remove eq_dec a (proj1_sig lpf))) rarblpf) -> P lpf) ->
    forall l, P l.
Proof.
  intros. destruct l as [ l lset ].
  destruct l. apply H.
  rename lset into alset.
  assert (lset := setrm A eq_dec (a::l) alset a).
  destruct (settail A eq_dec l a alset) as [ lset' aninl ].
  cut (P (exist _ _ lset') /\ P (exist _ _ alset)). intro. destruct H2. assumption.
  revert a alset lset aninl lset'. induction l. intros. split; auto.
  intros.
  destruct (settail _ _ _ _ alset) as [ alset' a0ninal ].
  assert (Hxxx := setrm _ _ _ lset' a).
  destruct (settail _ _ _ _ lset').
  destruct (IHl a lset' Hxxx H3 H2). split; auto.
  assert (Hxxxx := H1 a0 a (exist _ _ alset)).
  cbv beta in Hxxxx. unfold proj1_sig in Hxxxx.
  assert (is_set eq_dec (remove eq_dec a (remove eq_dec a0 (a0 :: a :: l))) = true) as setrara0aa0l.
    rewrite setrmhd; auto.
  apply (Hxxxx setrara0aa0l).
  assert (Hx := setsigeq A eq_dec P l (remove eq_dec a (remove eq_dec a0 (a0 :: a :: l)))).
  rewrite <- Hx with (px := H2). assumption.
  repeat rewrite setrmhd; auto.
Qed.

Definition eq_dec_t A := forall a b : A, {a=b}+{a<>b}.
Definition eq_pair_dec {A B} (deca : eq_dec_t A) (decb : eq_dec_t B) : forall a b : A * B, {a=b}+{a<>b}. decide equality. Defined.

Definition sig2sig A (P Q : A -> Prop) (impl : forall a : A, P a -> Q a) (x : {x | P x}) : {x | Q x} := exist _ (proj1_sig x) (impl _ (proj2_sig x)).

Lemma sig2sigp1 :
  forall A P Q impl l,
    map (@proj1_sig _ _) l = map (@proj1_sig _ _) (map (sig2sig A P Q impl) l).
Proof.
  intros. induction l.
  simpl. reflexivity.
  simpl. destruct a. simpl. apply f_equal2; [ reflexivity | assumption ].
Qed.

Definition redundant_list A (l : list A) : {lx : list {x | In x l} | map (@proj1_sig _ _) lx = l}.
Proof.
  induction l. exists nil. simpl. reflexivity.
  assert (forall x, In x l -> In x (a::l)). intros. simpl. right. assumption.
  destruct IHl.
  assert (In a (a::l)). simpl. left. reflexivity.
  refine (exist _ ((exist _ a H0)::(map (sig2sig _ _ _ H) x)) _).
  simpl. apply f_equal2; [ reflexivity | ].
  rewrite <- sig2sigp1. assumption.
Defined.

Lemma redundant_list_len :
  forall A (l : list A),
    length l = length (proj1_sig (redundant_list _ l)).
Proof.
  intros. destruct (redundant_list A l). simpl.
  rewrite <- e at 1. rewrite map_length. reflexivity.
Qed.

Lemma nesigne :
  forall A P (a b : {x : A | P x}), proj1_sig a <> proj1_sig b -> a <> b.
Proof.
  intros. intro. destruct a. destruct b. simpl in *. elim H.
  injection H0. intro. assumption.
Qed.

Lemma eqsigeq :
  forall A P (a b : {x : A | P x}) (irrelev : forall a (p1 p2 : P a), p1 = p2), proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros. destruct a, b. simpl in *. subst. assert (Hx := irrelev x0 p p0). rewrite Hx. reflexivity.
Qed.

Lemma inlinsigl :
  forall A (P : A -> Prop) (pi : forall a (p1 p2 : P a), p1 = p2) (a : A) (l : list {x : A | P x}),
    In a (map (@proj1_sig _ _) l) ->
    (forall pf : P a, In (exist _ a pf) l).
Proof.
  intros. rename H into ainl. rename l into sigl.
  induction sigl. simpl in *. assumption.
  simpl. simpl in ainl. destruct ainl.
  - left. destruct a0. simpl in *. subst.
    rewrite (pi a p pf). reflexivity.
  - right. apply IHsigl. assumption.
Qed.

Ltac ainral := match goal with H : In ?a (remove ?dec ?a ?l) |- _ => elim (remove_In dec l a); assumption end.
Ltac ainrbl := match goal with
                   H : In ?a (remove ?f ?b ?l), aneb: ?a <> ?b |- _ =>
                   let Hx := fresh in
                   assert (Hx := remove_corr_neq _ f l _ _ (neqflip _ _ _ aneb));
                     rewrite <- Hx in H; clear Hx
               end.

Tactic Notation "mysimp" :=
  idtac "mysimp no arguments".

Tactic Notation "mysimp" "in" ident(x) :=
  idtac "mysimp called on" x.

Tactic Notation "mysimp" "in" "*" :=
  idtac "mysimp called on *".

Ltac eqneq := match goal with H : ?a = ?b, HH : ?a <> ?b |- _ => elim HH; assumption
                           | H: ?a = ?b, HH : ?b <> ?a |- _ => elim HH; rewrite H; reflexivity
              end.

Ltac neqneq := match goal with H : ?a <> ?b |- ?b <> ?a => let Hx := fresh in
                                                           intro Hx; rewrite Hx in H; elim H; reflexivity
               end.

Definition paired_list {A} (pair : A -> A) l := forall a, In a l -> In (pair a) l.

Lemma paired_not_1 :
  forall
    A
    (pair_not_id : {pair | forall a, a <> pair a})
    (l : {l : list A | paired_list (proj1_sig pair_not_id) l}),
    length (proj1_sig l) <> 1.
Proof.
  intros A [pair nid] [l pf] l1.
  simpl in *.
  destruct l; [ discriminate | ].
  destruct l; [ | discriminate ].
  clear l1. unfold paired_list in pf.
  specialize pf with a.
  assert (In a (a::nil)) as aina. unfold In. left. reflexivity.
  assert (Hx := pf aina). clear pf. rename Hx into pf.
  simpl in pf. destruct pf; [ | assumption ].
  elim (nid a). assumption.
Qed.

Lemma removepairs_still_paired :
  forall
    A
    eq_dec
    (pair_involutive : {pair | forall a b : A, a <> b -> pair a <> b -> a <> pair b})
    (l_paired : {l | paired_list (proj1_sig pair_involutive) l}),
    (forall a,
       let pair := proj1_sig pair_involutive in
       paired_list pair (remove eq_dec (pair a) (remove eq_dec a (proj1_sig l_paired)))
    ).
Proof.
  intros A eq_dec [ pair pair_dis ] [ l pairIn ] a.
  unfold proj1_sig in *. unfold paired_list in *.
  intros x xinrbral.
  remember (remove _ (pair a) _) as rbral. rename Heqrbral into rbraleq.
  destruct (eq_dec a x) as [ aeqx | anex ].
  - rewrite <- aeqx in *. clear aeqx.
    assert (aninral := remove_In eq_dec l a).
    elim (Inremoveidem _ eq_dec _ _ (pair a) aninral).
    rewrite <- rbraleq. assumption.
  - destruct (eq_dec (pair a) x) as [ paeqx | panex ].
    + rewrite <- paeqx in *. exfalso. clear paeqx.
      assert (aninral := remove_In eq_dec l (pair a)).
      elim (Inremoveidem _ eq_dec _ _ a aninral).
      rewrite remove_assoc.
      rewrite <- rbraleq. assumption.
    + destruct (eq_dec a (pair x)) as [ aeqpx | anepx ].
      * elim (pair_dis _ _ anex panex). assumption.
      * destruct (eq_dec (pair a) (pair x)) as [ paeqpx | panepx ].
        assert (a = x) as aeqx. assert (pair_involutive := involutive_if _ eq_dec _ pair_dis). rewrite pair_involutive. rewrite pair_involutive with a.
        rewrite paeqpx. reflexivity.
        rewrite aeqx in anex. elim anex. reflexivity.
      rewrite rbraleq in *. clear rbraleq rbral.
      repeat match goal with
          H : ?e <> ?v,
              HH : In ?v (remove ?dec ?e ?l)
          |- _
          => let Hx := fresh in
             assert (Hx := remove_corr_neq _ dec l _ _ H);
               rewrite <- Hx in HH;
               clear Hx
      end.
      rename xinrbral into xinl.
      assert (pxinl := pairIn _ xinl).
      repeat match goal with
          H : ?e <> ?v
          |- In ?v (remove ?dec ?e ?l)
          => let Hx := fresh in
             assert (Hx := remove_corr_neq _ dec l _ _ H);
               rewrite <- Hx;
               clear Hx
      end.
      assumption.
Qed.

Require Import PeanoNat.
Lemma paired_even :
  forall
    A
    eq_dec
    (pair : {pair | (forall a, a <> pair a) /\ (forall a b : A, a <> b -> pair a <> b -> a <> pair b)})
    (l_paired : {l | is_set eq_dec l = true /\ paired_list (proj1_sig pair) l}),
  Nat.Even (length (proj1_sig l_paired)).
Proof.
  intros.
  destruct pair as [ pair [ notid involutive ] ].
  destruct l_paired as [ l [ set paired ] ]. simpl in *.
  unfold paired_list in paired.
  remember (length l) as n.
  revert l set paired Heqn. induction n using fib_ind.
  - intros. exists 0. reflexivity.
  - intros. elim (paired_not_1 _ (exist _ _ notid) (exist _ l paired)).
    simpl. rewrite Heqn. reflexivity.
  - intros. clear IHn0.
    assert (rarblpaired := removepairs_still_paired A eq_dec (exist _ _ involutive) (exist _ _ paired)). simpl in rarblpaired.
    assert (Hx := removepairs A eq_dec l pair set paired).
    destruct l. discriminate Heqn.
    assert (Hy := Hx a). clear Hx. assert (In a (a::l)). simpl. left. reflexivity.
    assert (Hx := Hy H). clear Hy H.
    assert (Hy := Hx _ eq_refl). clear Hx.
    destruct (eq_dec a (pair a)). elim (notid a). assumption.
    rewrite (setrmhd _ _ _ _ set) in Hy.
    assert (Hx := IHn (remove eq_dec (pair a) l)). clear IHn.
    assert (lset := setrm _ _ _ set a). rewrite setrmhd in lset; [ | assumption ].
    assert (palset := setrm _ _ _ lset (pair a)).
    assert (Hz := Hx palset). clear Hx.
    unfold paired_list in rarblpaired.
    assert (rblpaired := rarblpaired a). clear rarblpaired. rewrite setrmhd in rblpaired; [ | assumption ].
    assert (Hx := Hz rblpaired). clear Hz rblpaired.
    assert (painl := paired a). assert (In a (a::l)). simpl. left. reflexivity.
    assert (Hz := painl H). clear painl H.
    assert (In (pair a) l) as painl. simpl in Hz. destruct Hz. elim n0. assumption. assumption. clear Hz.
    assert (Hz := lrm _ _ _ lset _ painl). simpl in Heqn. rewrite Hz in Heqn. injection Heqn. intro. clear Hz.
    assert (Hz := Hx H). revert Hz. clear. intro neven.
    unfold Nat.Even in *. destruct neven. rewrite H.
    exists (S x). simpl. auto.
Qed.

Lemma paired_even' :
  forall
    A
    eq_dec
    pair
    (pairpf1 : forall a, a <> pair a)
    (pairpf2 : forall a b : A, a <> b -> pair a <> b -> a <> pair b)
    l
    (l_paired : is_set eq_dec l = true /\ paired_list pair l),
  Nat.Even (length l).
Proof.
  intros. assert (Hx := paired_even _ _ (exist _ pair (conj pairpf1 pairpf2)) (exist _ _ l_paired)).
  simpl in Hx. assumption.
Qed.

Lemma setleneq :
  forall A dec (l ll : list A),
    is_set dec l = true ->
    is_set dec ll = true ->
    (forall a, In a l <-> In a ll) ->
    length l = length ll.
Proof.
  induction l. intros. simpl. destruct ll. reflexivity. simpl in H1.
  assert (a = a \/ In a ll). left. reflexivity.
  rewrite <- H1 in H2. contradiction.
  intros. simpl in *. destruct (inb dec a l) eqn:xx; [ discriminate | ].
  assert (In a ll).
    rewrite <- H1. left. reflexivity.
  assert (Hx := setrm _ _ _ H0 a).
  assert (Hy := lrm _ _ _ H0 _ H2).
  rewrite Hy. rewrite (IHl _ H Hx). reflexivity.
  intros. destruct (dec a a0).
  - rewrite <- e. split; intro.
    + rewrite inbeqInnot in xx. elim xx. assumption.
    + exfalso. revert H3. clear. intro.
      elim (remove_In dec ll a). assumption.
  - rewrite <- (remove_corr_neq _ dec ll _ _ n).
    rewrite <- H1. split; intro.
    + right. assumption.
    + destruct H3.
      * elim n. assumption.
      * assumption.
Qed.

Fixpoint zipmin {A B} (l : list A) (ll : list B) :=
  match l, ll with
    | nil, _ => nil
    | _, nil => nil
    | a::l', b::ll' => (a,b)::(zipmin l' ll')
  end.

Lemma zipminlnil : forall A B (l : list A), zipmin l (@nil B) = nil.
Proof.
  induction l. reflexivity.
  simpl. reflexivity.
Qed.

Lemma rev_unit : forall A (a : A) l, rev l = a::nil -> l = a::nil.
Proof.
  intros.
  assert (length (rev l) = 1). rewrite H. simpl. reflexivity.
  destruct l; [ discriminate H0 | ].
  destruct l; [ solve [ auto ] | ].
  simpl in H0. rewrite <- app_assoc in H0. rewrite app_length in H0.
  simpl in H0. remember (length _). exfalso. revert H0. clear.
  intros.
  rewrite Nat.add_comm in H0. simpl in H0. discriminate H0.
Qed.