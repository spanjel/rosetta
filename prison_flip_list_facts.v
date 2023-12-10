Require Export prison_flip_list.
Require Import prison.

Require Import Arith.
Require Import NPeano.
Require Import List.
Require Import Nat.
Require Import Lia.

Require Import prison_facts.
Require Import logic.
Require Import list_facts.

Definition oddmap lim (l : list (fliplelem lim)) := map (fun c => odd (length (fe_divs _ c))) l.

Lemma consconv_proj1_sig_distr :
  forall lim h l lx ex,
    proj1_sig (consconv lim (h::l) h l eq_refl ex lx) = (proj1_sig ex)::(proj1_sig lx).
Proof.
  intros lim l h lx. destruct lx. simpl.
  revert a. revert l. induction x.
  - intros. destruct a. destruct ex. simpl. reflexivity.
  - intros. destruct a0. destruct ex. simpl. reflexivity.
Qed.

Lemma mapunfold :
  forall A B (f : A -> B) h t, map f (h::t) = (f h)::(map f t).
Proof.
  simpl. reflexivity.
Qed.

Lemma flipeqflipl :
  forall lim l lpf k kpf l',
    l' = (oddmap lim l) ->
    flip l' lim k = oddmap _ (proj1_sig (flipl _ l lpf k kpf)).
Proof.
  intros. rewrite H in *. clear H l'. revert lpf k kpf.
  induction l. simpl. reflexivity.
  intros. cbv zeta in kpf. simpl. destruct k.

  - rewrite (consconv_proj1_sig_distr _ a l).
    unfold plus at 1 in kpf.
    unfold oddmap. rewrite mapunfold. apply f_equal2.
    + destruct (fliplkzh _ _ _ _ _) as [ x [ xid xdiv ] ]. unfold dropsnd. unfold proj1_sig.
      rewrite xdiv. remember (fe_divs _ a).
      clear. assert (length (S lim::l0) = S (length l0)) as tmp. simpl. reflexivity.
      rewrite tmp. clear tmp.
      rewrite Nat.odd_succ.
      rewrite Nat.negb_odd.
      reflexivity.
    + unfold oddmap in *. rewrite <- IHl. reflexivity.

  - rewrite (consconv_proj1_sig_distr _ a l).
    unfold oddmap in *.
    rewrite mapunfold.
    apply f_equal2.
    + destruct (fliplknzh _ _ _ _ _ _) as [ x [ xid xdiv ] ].
      unfold dropsnd. unfold proj1_sig.
      rewrite xdiv. reflexivity.
    + rewrite <- IHl. reflexivity.
Qed.

Lemma flipeacheqflipleach :
  forall lim l cpf l',
    l' = oddmap lim l ->
    match l with
      | nil => True
      | h::_ => fe_idx _ h = 1
    end ->
    flipeach l' lim = oddmap _ (proj1_sig (flipleach lim l cpf)).
Proof.
  intros. unfold flipleach. rewrite <- flipeqflipl with (l' := l'); [ | assumption ].
  rewrite H in *. clear H l'.
  unfold flipeach. destruct l. simpl. reflexivity.
  rewrite H0. unfold plus. rewrite Nat.Div0.mod_same.
  assert (Hx := Nat.sub_0_r lim). rewrite Hx.
  reflexivity.
Qed.

Lemma idxidemunfold :
  forall lim lim' h1 h2 l1 l2,
    idxidem (h1::l1) (h2::l2) ->
    (fe_idx lim h1 = fe_idx lim' h2 /\ idxidem l1 l2).
Proof.
  intros. unfold idxidem in H. simpl in H. rewrite Forall_forall in H.
  split.
  - apply (H (h1, h2)). simpl. left. reflexivity.
  - unfold idxidem. rewrite Forall_forall. intros.
    apply (H x). simpl. right. assumption.
Qed.

Lemma aiffbaiffcbiffc :
  forall a b c, ((a <-> b) /\ (a <-> c)) -> (b <-> c).
Proof.
  intros. destruct H. rewrite <- H. rewrite <- H0. split; intro; assumption.
Qed.

Lemma hin :
  forall A (h : A) l,
    In h (h::l).
Proof. simpl. left. reflexivity. Qed.

Lemma divseq :
  forall lim lim' a b,
    lim = lim' ->
    fe_idx lim a = fe_idx lim' b ->
    length (fe_divs _ a) = length (fe_divs _ b).
Proof.

  intros. subst. destruct a, b. simpl in *.
  subst. revert fe_idx0 fe_divs0 fe_invariant0 fe_invariant. intros.
  destruct fe_invariant0 as [ idnz [ dset [ dle iniff ] ] ].
  destruct fe_invariant as [ _ [ dset' [ dle' iniff' ] ] ].
  rewrite Forall_forall in dle, dle'.
  assert (forall A B C D : Prop, (A -> B) -> (C -> B) -> (B -> (D <-> A)) -> (B -> (D <-> C)) -> (A <-> C)).
  { clear. intros. firstorder. }
  assert (forall x, In x fe_divs <-> In x fe_divs0).
  { intros. rewrite (H _ _ _ _  (dle x) (dle' x) (iniff x) (iniff' x)). firstorder. }
  revert H0 dset dset'; clear; intros.
  assert (Hx := setleneq _ eq_nat_dec). apply Hx; auto.
Qed.

Lemma oddmapfliplelem :
  forall lim (l ll : list (fliplelem lim)),
    length l = length ll ->
    idxidem l ll ->
    oddmap _ l = oddmap _ ll.
Proof.
  induction l; destruct ll; auto; intros; simpl in *; try discriminate.
  destruct (idxidemunfold _ _ _ _ _ _ H0) as [ aeqf lidemll ].
  rewrite IHl with (ll := ll); auto.
  apply f_equal2; [ | reflexivity ].
  rewrite divseq with (b := f); auto.
Qed.

Lemma flipwhileeqfliplwhile :
  forall n l cpf l',
    l' = oddmap 0 l ->
    match l with
      | nil => True
      | h::_ => fe_idx _ h = 1
    end ->
    flipwhile l' n = oddmap _ (proj1_sig (fliplwhile 0 l cpf n)).
Proof.
  induction n.

  - simpl. intros.
    rewrite flipeacheqflipleach with (l := l) (cpf := cpf); auto.

  - intros l cpf l' l'eq h1.
    rewrite l'eq in *. clear l'eq l'.
    unfold flipwhile. fold flipwhile. rewrite flipwhileflipeach.
    assert (Hx := IHn l cpf _ eq_refl h1). rewrite Hx. clear IHn Hx.
    assert (leacheq := fun cpfx => flipeacheqflipleach _ (proj1_sig (fliplwhile 0 l cpf n)) cpfx _ eq_refl).
    assert (S n = S (n + 0)) as tmp; [ auto | ]. rewrite tmp at 1. clear tmp.

    assert (idxcont (proj1_sig (fliplwhile 0 l cpf n))) as cpf'. clear leacheq h1. destruct (fliplwhile _ _ _ _). simpl. destruct a. apply (idxidemidxc _ _ _ _ (eq_flip _ _ _ H) cpf). rewrite idxidemrefl. assumption.

    assert (match proj1_sig (fliplwhile 0 l cpf n) with
       | nil => True
       | h :: _ => fe_idx (S (n + 0)) h = 1
       end) as h1'. clear cpf' leacheq. destruct (fliplwhile _ _ _ _) as [ x [ xl xid ] ]. simpl. destruct x, l; auto; simpl in xl; try discriminate. unfold idxidem in xid. rewrite Forall_forall in xid. assert (xid' := xid (f, f0)). simpl in xid'. rewrite xid'. assumption. left. reflexivity.

    rewrite (leacheq cpf' h1'). clear leacheq h1'.
    simpl.
    match goal with
        |- oddmap _ (proj1_sig ?x) = oddmap _ (proj1_sig ?y) => remember x; remember y
    end. clear Heqs Heqs0.
    destruct s, s0. simpl.
    destruct a as [ xlen xidem ].
    destruct a0 as [ x0len x0idem ].
    destruct (fliplwhile 0 l _ _). simpl in *.
    destruct a as [ x1len x1idem ].
    apply oddmapfliplelem.
    + rewrite x0len. rewrite xlen. rewrite x1len. reflexivity.
    + assert (idxidem x l); [ apply (idxidemtrans _ _ _ x1 _ _); auto | ].
      apply (idxidemtrans _ _ _ l _ _); auto. rewrite xlen. rewrite x1len. reflexivity.
      apply idxidemrefl. assumption.
Qed.

Lemma fliplem0divs :
  forall x : fliplelem 0, fe_divs _ x = nil.
Proof.
  intros. destruct x. simpl. destruct fe_invariant as [ xx [ yy [ dle xin ] ] ].
  rewrite Forall_forall in dle. destruct fe_divs; [ reflexivity | ].
  assert (n=0).
  {
    destruct n; [ reflexivity | ].
    assert (Hx := dle (S n)). simpl in Hx. assert (Hy := Hx (or_introl eq_refl)). lia.
  }
  subst.
  assert (Hx := xin 0). destruct (Hx (le_n 0)). simpl in H0. elim xx. apply H0. auto.
Qed.

Lemma oddmapeq :
  forall (l ll : list (fliplelem 0)),
    length l = length ll ->
    oddmap _ l = oddmap _ ll.
Proof.
  intros x x0 lxeqlx0.
  unfold oddmap. revert x0 lxeqlx0. induction x; intros.
  + simpl. destruct x0. simpl. reflexivity.
    simpl in lxeqlx0. discriminate.
  + simpl. destruct x0.  simpl in lxeqlx0. discriminate. rewrite (IHx x0).
    * simpl. repeat rewrite fliplem0divs. simpl. reflexivity.
    * simpl in lxeqlx0. inversion lxeqlx0. reflexivity.
Qed.

Lemma prisoneq :
  forall cells,
    prison cells = oddmap _ (proj1_sig (prisonl cells)).
Proof.

  intros. unfold prison. unfold prisonl.
  rewrite <- flipwhileeqfliplwhile with (l' := oddmap _ (proj1_sig (prisonlbase cells))).

  - apply f_equal2; auto.
    induction cells. simpl. reflexivity.
    unfold rep in *. fold @rep in *. rewrite IHcells. clear.
    destruct (prisonlbase cells). unfold proj1_sig.
    destruct (prisonlbase (S cells)).
    assert (S (length x) = length x0).
      destruct a as [ xlen _ ]. destruct a0 as [ x0len _ ]. rewrite xlen, x0len. reflexivity.
    clear a a0.
    destruct x0. simpl in *. discriminate.
    simpl. rewrite fliplem0divs. simpl. apply f_equal2; auto.
    simpl in *. inversion H. rename H1 into lxeqlx0. clear H f.
    apply oddmapeq. assumption.

  - destruct cells. simpl. reflexivity.
    destruct (prisonlbase cells).
    destruct (prisonlbase (S cells)). unfold proj1_sig in *.
    apply oddmapeq. rewrite rev_length. reflexivity.

  - destruct (prisonlbase cells). unfold proj1_sig.
    destruct x. simpl. constructor.
    simpl. destruct a as [ _ [ endone _ ] ].
    simpl in endone. destruct (rev x ++ f::nil). constructor.
    apply endone. simpl. reflexivity.
Qed.

Lemma idxcifidxc' :
  forall lim (l : list (fliplelem lim)) a,
    idxcont' l a -> idxcont l.
Proof.
  destruct l. simpl. constructor.
  intros. simpl in *. split; [ reflexivity | ].
  apply H.
Qed.

Definition optmap A B (f : A -> B) (v : option A) := match v with
                                                       | None => None
                                                       | Some v' => Some (f v')
                                                     end.

Definition optidx lim v := optmap _ _ (fe_idx lim) v.

Lemma length_app_distr :
  forall A (l ll : list A),
    length (l ++ ll) = length l + length ll.
Proof.
  induction l. simpl. reflexivity.
  simpl. intros. rewrite IHl. reflexivity.
Qed.

Lemma idxstartend :
  forall lim (l : list (fliplelem lim)),
    idxcont l ->
    (forall h e,
       optidx _ (hd_error l) = Some h ->
       optidx _ (hd_error (rev l)) = Some e ->
       h + (length l) = S e).
Proof.
  induction l. simpl. intros. discriminate.
  simpl. intros.
  induction l using rev_ind; [ | clear IHl0 ].
  - simpl in *. inversion H1. inversion H0. rewrite H3 in *. rewrite H4 in *.
    rewrite Nat.add_comm. simpl. reflexivity.
  - rewrite rev_app_distr in *. simpl in *.
    inversion H0. inversion H1. rewrite H3, H4 in *. rewrite length_app_distr. simpl.
    destruct H as [ _ idxc' ].
    assert (IHl' := IHl (idxcifidxc' _ _ _ idxc')). clear IHl.
    destruct l.
    + simpl in *. destruct idxc' as [ xid _ ]. rewrite xid in *.
      rewrite Nat.add_comm. simpl. rewrite H4. reflexivity.
    + simpl in *. destruct idxc' as [ fid lxcont ]. rewrite fid in *.
      rewrite <- (IHl' _ _ eq_refl eq_refl). clear IHl'.
      rewrite length_app_distr. simpl. lia.
Qed.

Lemma idxend_ge :
  forall lim (l : list (fliplelem lim)),
    idxcont l ->
    (forall e,
       optmap _ _ (fe_idx _) (hd_error (rev l)) = Some e ->
       Forall (fun e' => fe_idx _ e' <= e) l).
Proof.
  intros lim l idxc e eeq. destruct l as [ | f l ]. constructor.
  assert (optidx _ (hd_error (f::l)) = Some (fe_idx _ f)) as tmp. simpl. reflexivity.
  assert (fidlenfleqSe := idxstartend _ _ idxc _ _ tmp eeq). clear tmp.
  simpl in fidlenfleqSe. rewrite Nat.add_comm in fidlenfleqSe.
  simpl in fidlenfleqSe.
  inversion fidlenfleqSe as [ lenfeqe ]. clear fidlenfleqSe. clear eeq.
  rewrite Forall_forall.
  revert dependent f. revert e.
  induction l. simpl. intros. destruct H; subst; [ constructor | elim H ].
  intros e f idxc alfe x xin.
  assert (alcont := idxcontt _ _ _ _ idxc eq_refl).
  assert (length l + fe_idx _ a = e) as lenlaeqe.
    revert idxc alfe. clear. intros.
    simpl in *. destruct idxc as [ _ [ af _ ] ]. rewrite af.
    rewrite <- alfe. lia.
  assert (IHl' := IHl _ _ alcont lenlaeqe x). clear IHl.
  assert (f = x \/ In x (a::l)) as xin'. revert xin. clear. intros. simpl in *. assumption.
  destruct xin' as [ feqx | xinal ].
  - subst. simpl in *. clear.  lia.
  - assert (xleSll := IHl' xinal). clear xinal IHl'.
    assert (fe_idx _ a = S (fe_idx _ f)) as aidSfid. simpl in idxc. apply idxc.
    revert xleSll aidSfid. clear. intros. rewrite aidSfid in *. clear aidSfid.
    simpl. lia.
Qed.

Lemma idxidem_app_distr :
  forall lim lim' l ll a b,
    length l = length ll ->
    idxidem (l ++ a::nil) (ll ++ b::nil) ->
    fe_idx lim a = fe_idx lim' b.
Proof.
  induction l; destruct ll; intros; simpl in *; try discriminate.
  - simpl in H0. unfold idxidem in H0. rewrite Forall_forall in H0.
    apply (H0 (a, b) (or_introl eq_refl)).
  - apply (IHl ll a0 b).
    + inversion H. reflexivity.
    + assert (Hx := idxidemunfold _ _ _ _ _ _ H0).
      apply Hx.
Qed.

Lemma prisonl_idxle :
  forall n,
    Forall (fun e => fe_idx _ e <= S n) (proj1_sig (prisonl n)).
Proof.
  unfold prisonl. intros. rewrite Forall_forall. intros x xin.
  destruct (prisonlbase n) as [ base basepf ]. simpl in *.
  destruct basepf as [ baselen [ beg1 basecont ] ].
  destruct (fliplwhile _ _) as [ res respf ]. simpl in *.
  destruct respf as [ reslen resid ].
  rewrite idxidemrefl in resid.
  assert (rescont := idxidemidxc _ _ _ _ (eq_flip _ _ _ reslen) basecont resid).
  assert (Hx := idxend_ge _ _ rescont).
  destruct base. simpl in *. subst. destruct res. simpl in *. elim xin. simpl in reslen. discriminate reslen.
  assert (Hy := Hx (fe_idx _ f)). clear Hx.
  assert (optmap (fliplelem (S (n + 0))) nat (fe_idx (S (n + 0)))
         (hd_error (rev res)) = Some (fe_idx 0 f)) as lastidreseqbase. clear Hy.
    simpl in resid.
    induction res using rev_ind; [ | clear IHres ]. simpl in xin. elim xin.
    assert (Hx := fun leq => idxidem_app_distr _ _ _ _ _ _ leq resid).
    rewrite Hx. rewrite rev_app_distr. simpl. reflexivity.
    revert reslen baselen. clear. intros.
    simpl in *. repeat rewrite length_app_distr in reslen. simpl in *.
    repeat rewrite (Nat.add_comm _ 1) in reslen. simpl in reslen. inversion reslen. reflexivity.
  assert (Hz := Hy lastidreseqbase). clear Hy lastidreseqbase.
  rewrite Forall_forall in Hz.
  assert (Hx := Hz _ xin). clear Hz.
  rewrite Hx. simpl in *. rewrite <- rev_length in baselen. destruct (rev base). simpl in *. rewrite beg1. rewrite <- baselen. constructor. constructor. reflexivity.
  simpl in *. destruct basecont as [ _ basecont ].
  assert (Hy := idxcont_idx _ _ _ _ basecont). rewrite (beg1 f0) in Hy; [ | reflexivity ].
  rewrite Hy. rewrite <- baselen. simpl. constructor. constructor.
Qed.

Lemma prisonl_alldiv :
  forall n,
    Forall (fun e => forall x, ((fe_idx _ e) mod x = 0) <-> In x (fe_divs _ e)) (proj1_sig (prisonl n)).
Proof.
  intro.
  assert (Hx := prisonl_idxle n).
  rewrite Forall_forall in *.
  intros.
  assert (Hy := Hx _ H).
  assert (S n = S n + 0). lia.
  assert (Hz := alldivs _ x).
  rewrite H0 in Hy. assert (Ha := Hz Hy).
  destruct Ha. destruct a as [ x1def [ x1set diviff ] ].
  assert (diviff' := diviff x0). clear diviff Hx Hy H0 Hz.
  rewrite diviff'. rewrite x1def.
  split; intro; assumption.
Qed.
