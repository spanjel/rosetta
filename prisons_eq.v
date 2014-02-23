Require Import prison.
Require Import prison_opt.
Require Import math.

Require Import prison_facts.
Require Import prison_opt_facts.
Require Import prison_flip_list_facts.

Require Import NPeano.
Require Import List.
Require Import Arith.

Fixpoint with_index {A} (l : list A) (idx : nat) :=
  match l with
    | nil => nil
    | h::t => (h, idx)::(with_index t (S idx))
  end.

Lemma withindeq :
  forall A (l : list A) idx,
    map (@fst _ _) (with_index l idx) = l.
Proof.
  induction l. simpl. reflexivity.
  intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma withindindge :
  forall A (l : list A) idx x,
    In x (with_index l idx) ->
    idx <= snd x.
Proof.
  induction l. simpl. intros. contradiction.
  simpl. intros. destruct H.
  - rewrite <- H in *. simpl. constructor.
  - assert (Hx := IHl _ _ H). omega.
Qed.

Lemma withindindeq :
  forall A (l ll : list A) idx,
    length l = length ll ->
    map (@snd _ _) (with_index l idx) = map (@snd _ _) (with_index ll idx).
Proof.
  induction l. destruct ll; intros. simpl. reflexivity. discriminate H.
  intros. destruct ll. discriminate H.
  simpl in H. injection H. intros. assert (Hx := IHl _ (S idx) H0).
  simpl. rewrite Hx. reflexivity.
Qed.

Definition zip {A B} (l : list A) (ll : list B) (pf : length l = length ll) : {x : list (A * B) | length x = length l}.
Proof.
  revert ll pf.
  induction l; destruct ll; intros. exists nil. reflexivity.
  discriminate.
  discriminate.
  simpl in pf. injection pf. intro.
  exists ((a, b)::(proj1_sig (IHl _ H))).
  simpl. apply f_equal. destruct (IHl _ H).
  simpl. assumption.
Defined.

Lemma lencontract :
  forall A B (a : A) l (b : B) ll,
    length (a::l) = length (b::ll) ->
    length l = length ll.
Proof.
  intros. simpl in *. injection H. intros. assumption.
Qed.
    
Lemma zipunfold :
  forall A B (a : A) l (b : B) ll pf,
    proj1_sig (zip (a::l) (b::ll) pf) = (a, b)::(proj1_sig (zip l ll (lencontract _ _ _ _ _ _ pf))).
Proof.
  intros. simpl. apply f_equal2; auto.
  apply f_equal. remember (f_equal _ _).
  apply f_equal. apply Arith.Peano_dec.UIP_nat.
Qed.

Lemma zipeq_left :
  forall A (l ll : list A) pf,
    Forall (fun x => fst x = snd x) (proj1_sig (zip l ll pf)) ->
    l = ll.
Proof.
  induction l; destruct ll; intros; try apply eq_refl; try discriminate.
  rewrite zipunfold in H.
  inversion H. subst.
  simpl in *. subst. apply f_equal2. reflexivity.
  apply (IHl _ _ H3).
Qed.

Lemma zipeq_right :
  forall A (l ll : list A) pf,
    l = ll ->
    Forall (fun x => fst x = snd x) (proj1_sig (zip l ll pf)).
Proof.
  intros. subst. induction ll. simpl. constructor.
  rewrite Forall_forall. intros.
  rewrite zipunfold in H. simpl in H. destruct H. subst. simpl. reflexivity.
  assert (Hx := IHll eq_refl).
  rewrite Forall_forall in Hx. apply Hx.
  remember (lencontract _ _ _ _ _ _ _).
  assert (e = eq_refl). apply UIP_nat.
  rewrite <- H0. assumption.
Qed.

Lemma flipwlen :
  forall n l, length (flipwhile l n) = length l.
Proof.
  induction n. simpl. intros. rewrite flipeach_length. reflexivity.
  intros.
  simpl. assert (Hx := IHn (flipeach l (S n))).
  rewrite flipeach_length in Hx. rewrite <- Hx. reflexivity.
Qed.

Lemma replen :
  forall A n (a : A), length (rep a n) = n.
Proof.
  induction n. simpl. reflexivity.
  simpl. intros. rewrite IHn. reflexivity.
Qed.

Lemma prisonlenn :
  forall n, length (prison n) = S n.
Proof.
  unfold prison.
  intros. rewrite flipwlen.
  rewrite replen. reflexivity.
Qed.

Lemma prisoo'len :
  forall n x y l, length (prisoo' n x y l) = n + length l.
Proof.
  induction n. simpl. intros. rewrite rev_length. reflexivity.
  intros. simpl. rewrite IHn. simpl. rewrite plus_comm. simpl. rewrite plus_comm. reflexivity.
Qed.

Lemma prisoolenn :
  forall n, length (prisoo n) = S n.
Proof.
  unfold prisoo. intro. rewrite prisoo'len. simpl. rewrite plus_comm. simpl. reflexivity.
Qed.

Lemma prisleneq :
  forall n, length (prison n) = length (prisoo n).
Proof.
  intros. rewrite prisonlenn. rewrite prisoolenn. reflexivity.
Qed.

Lemma idxeq :
  forall A B (l : list A) (ll : list B) idx pf x,
    In x (proj1_sig (zip (with_index l idx) (with_index ll idx) pf)) ->
    snd (fst x) = snd (snd x).
Proof.
  induction l. intros. destruct ll. simpl in *. elim H. simpl in pf. discriminate pf.
  intros. destruct ll. discriminate pf.
  simpl in H. destruct H. subst. simpl. reflexivity.
  assert (length (with_index l (S idx)) = length (with_index ll (S idx))).
   simpl in pf. injection pf. intro. assumption.
  apply IHl with (ll:=ll) (idx := S idx) (pf := H0).
  match goal with
      H : In ?x (proj1_sig (zip ?l ?ll ?pf1)) |- _ =>
      let Hx := fresh in
      assert (pf1 = H0) as Hx
  end.
  apply UIP_nat.
  rewrite <- H1. assumption.
Qed.

Lemma inzipin :
  forall A B (l : list A) (ll : list B) pf x,
    In x (proj1_sig (zip l ll pf)) ->
    In (fst x) l /\ In (snd x) ll.
Proof.
  induction l; intros. destruct ll. simpl in H. elim H. discriminate pf.
  destruct ll. discriminate pf.
  rewrite zipunfold in H. simpl in H. destruct H.
  - subst. simpl. split; left; reflexivity.
  - simpl. destruct (IHl _ _ _ H).
    split; right; assumption.
Qed.

Lemma with_idx_elim_prisoo :
  forall n s,
    let res := prisoo'' n s nil in
    with_index (map s2b res) (ps_idx s) =
    map (fun s => (s2b s, ps_idx s)) res.
Proof.
  induction n. intros. simpl in *. reflexivity.
  intros. unfold res in *. clear res.
  simpl in *. rewrite prisoo_unfold.
  repeat rewrite map_app.
  rewrite <- IHn. clear IHn.
  remember (prisoo'' _ _ _).
  simpl. apply f_equal2; [ reflexivity | ].
  apply f_equal2; [ reflexivity | ]. clear l Heql.
  destruct s. simpl. destruct ps_k; simpl; reflexivity.
Qed.

Lemma withindex_unfold :
  forall A l (a : A) n,
    with_index (l ++ a::nil) n = with_index l n ++ ((a, n + length l)::nil).
Proof.
  induction l.  simpl. intros. rewrite plus_comm. simpl. reflexivity.
  intros. 
  assert (IHl' := IHl a0 (S n)). clear IHl.
  simpl. rewrite IHl'. rewrite (plus_comm n). simpl. rewrite plus_comm. reflexivity.
Qed.

Lemma withindex_app :
  forall A (l ll : list A) n,
    with_index (l ++ ll) n = (with_index l n) ++ (with_index ll (n + length l)).
Proof.
  induction l using rev_ind. simpl. intros. rewrite plus_comm. simpl. reflexivity.
  intros. assert (IHl' := IHl (x::ll) n). clear IHl.
  rewrite <- app_assoc. simpl in *. rewrite IHl'.
  rewrite (withindex_unfold _ l x).
  rewrite <- app_assoc.
  apply f_equal2; [ reflexivity | ].
  simpl. apply f_equal2; [ reflexivity | ].
  rewrite app_length. simpl. rewrite (plus_comm _ 1). simpl. rewrite (plus_comm n (S _)). simpl. rewrite plus_comm. reflexivity.
Qed.

Lemma withindex_cont_eq :
  forall lim (l : list (fliplelem lim)) n,
    (optmap _ _ (fe_idx _) (hd_error l) = Some n) ->
    idxcont l ->
    Forall (fun e => fe_idx _ (fst e) = snd e) (with_index l n).
Proof.
  intros. rewrite Forall_forall. intros.
  revert dependent n. revert dependent x. revert dependent l.
  induction l. simpl in *. intros. contradiction.
  intros. assert (Hx := idxcontt _ _ _ _ H0 eq_refl).
  assert (IHl' := IHl Hx). clear IHl.
  simpl in H. simpl in H1. destruct H1. rewrite <- H1. simpl. inversion H. reflexivity.
  assert (IHl := fun x => IHl' x (S n)). clear IHl'.
  assert (optmap (fliplelem lim) nat (fe_idx lim) (hd_error l) = Some (S n)).
    clear IHl. destruct l. simpl in H1. contradiction.
    simpl. simpl in H0. inversion H. destruct H0 as [ _ [ fid _ ] ].
    rewrite fid. reflexivity.
  assert (IHl' := fun x => IHl x H2). clear IHl H2.
  apply (IHl' _ H1).
Qed.

Lemma with_index_map :
  forall A B (f : A -> B) l n,
    with_index (map f l) n = map (fun x => (f (fst x), snd x)) (with_index l n).
Proof.
  induction l. simpl. reflexivity.
  simpl. intros. apply f_equal2; [ reflexivity | ].
  apply IHl.
Qed.

Lemma with_idx_elim_prisonl :
  forall n,
    with_index (evenmap (S (n + 0)) (proj1_sig (prisonl n))) 1 =
    map (fun e => (even (length (fe_divs _ e)), fe_idx _ e)) (proj1_sig (prisonl n)).
Proof.
  intros. assert (Hx := withindex_cont_eq).
  intros. unfold prisonl. remember (prisonlbase n). clear Heqs. destruct s as [ base basepf ]. simpl.
  destruct basepf as [ x0notnil [ x0hSn [ x0e1 [ lx0Sn rx0cont ] ] ] ].
  assert (Hy := fun pf => Hx _ (rev base) 1 pf rx0cont). clear Hx.
  assert (optmap (fliplelem 0) nat (fe_idx 0) (hd_error (rev base)) = Some 1) as tmp.
    induction base using rev_ind; [ | clear IHbase ]. simpl in lx0Sn. discriminate.
    rewrite rev_app_distr. simpl. rewrite rev_app_distr in x0e1. simpl in x0e1. rewrite x0e1. reflexivity. reflexivity.
  assert (Hz := Hy tmp). clear Hy tmp. rewrite Forall_forall in Hz.
  destruct (fliplwhile _ _ _ _). simpl in *.
  destruct a as [ xlenrblen xid ].
  assert (length x = length base). rewrite rev_length in xlenrblen. assumption.
  unfold evenmap. 
  rewrite with_index_map.
  assert (idxcont x) as xcont. apply idxidemidxc with (l := rev base).
    rewrite H; auto. rewrite rev_length; auto. assumption. apply idxidemrefl. assumption.
  assert (forall h, hd_error x = Some h -> fe_idx _ h = 1).
    intros. destruct x. discriminate H0.
    simpl in H0. inversion H0. rewrite H2 in *. clear H2 f.
    destruct (rev base). simpl in xlenrblen. discriminate.
    destruct (idxidemunfold _ _ _ _ _ _ xid).
    rewrite H1. apply x0e1. simpl. reflexivity.
  revert H0 xcont. clear. intros.
  induction x using rev_ind. simpl. reflexivity.
  simpl. rewrite withindex_app. rewrite map_app. simpl.
  rewrite IHx; clear IHx.
  - rewrite map_app.
    apply f_equal2.
    + reflexivity.
    + simpl. apply f_equal2; [ | reflexivity ].
      apply f_equal2; [ reflexivity | ].
      assert (Hx := idxstartend _ _ xcont).
      destruct x0. simpl in *. rewrite H0; reflexivity.
      assert (Hy := Hx 1 (fe_idx _ x)). clear Hx.
      rewrite rev_app_distr in Hy. simpl in Hy.
      simpl in H0. assert (fid1 := H0 f eq_refl).
      assert (Some (fe_idx (S (n + 0)) f) = Some 1).
        rewrite fid1. reflexivity.
      assert (Hz := Hy H eq_refl). inversion Hz. clear.
      rewrite app_length. simpl. rewrite (plus_comm _ 1). simpl. reflexivity.
  - intros. apply H0.
    destruct x0. simpl in H. discriminate.
    simpl in *. assumption.
  - apply (idxcontt_app _ _ _ _ xcont eq_refl).
Qed.

Goal forall n, prison n = prisoo n.
Proof.

  intros. destruct (eq_nat_dec n 0).
    subst. unfold prisoo. unfold prison. simpl. reflexivity.
  rewrite <- (withindeq bool (prison n) 1).
  rewrite <- (withindeq bool (prisoo n) 1).
  remember (with_index (prison n) 1) as pwi.
  remember (with_index (prisoo n) 1) as pwio.
  cut (pwi = pwio). intro. rewrite H. reflexivity.
  assert (forall x, In x pwi -> (snd x) <> 0).
    rewrite Heqpwi. clear. intros. assert (Hx := withindindge _ _ _ _ H).
    intro. rewrite <- H0 in Hx. omega.
  assert (forall x, In x pwio -> (snd x) <> 0).
    rewrite Heqpwio. clear. intros. assert (Hx := withindindge _ _ _ _ H).
    intro. rewrite <- H0 in Hx. omega.
  cut (forall x (inpf : In x pwi), (~Even (length (divisors_nz (H _ inpf)))) <-> fst x = true).
  intro.
  cut (forall x (inpf : In x pwio), (issq (snd x)) <-> fst x = true).
  intro.
  assert (forall x (inpf : In x pwi), (issq (snd x) <-> ~Even (length (divisors_nz (H _ inpf))))).
    intros. apply sqne.
  assert (forall x (inpf : In x pwio), (issq (snd x) <-> ~Even (length (divisors_nz (H0 _ inpf))))).
    intros. apply sqne.
  assert (lpeq := prisleneq). generalize lpeq. intro lpeqx.
  specialize lpeq with n.
  rewrite <- (withindeq _ (prison n) 1) in lpeq.
  rewrite <- (withindeq _ (prisoo n) 1) in lpeq.
  rewrite map_length in lpeq. rewrite <- Heqpwi in lpeq.
  rewrite map_length in lpeq. rewrite <- Heqpwio in lpeq.
  apply zipeq_left with lpeq.
  generalize H. rename H into H'. intro H. rewrite <- Forall_forall in H.
  generalize H0. rename H0 into H0'. intro H0. rewrite <- Forall_forall in H0.
  assert (forall x (inpf : In x pwi), issq (snd x) <-> fst x = true).
    intros. rewrite H3. apply H1.
  rewrite Forall_forall. intros.
  rewrite Forall_forall in H, H0.
  assert (Hxx := H (fst x)). clear H.
  assert (Hyy := H0 (snd x)). clear H0.
  destruct x. simpl in *.
  assert (H := inzipin).
  assert (Hin := H _ _ _ _ _ _ H6). clear H. simpl in Hin. destruct Hin.
  assert (pnz := Hxx H). clear Hxx.
  assert (p0nz := Hyy H0). clear Hyy.
  assert (Hxx := H2 _ H0).
  assert (Hyy := H5 _ H).
  generalize lpeq. intro lpeq'. rewrite Heqpwi in lpeq'. rewrite Heqpwio in lpeq'.
  assert (Hxy := withindindeq _ _ _ 1 (lpeqx n)).
  cut (snd p = snd p0).
  intro. rewrite H7 in *.
  rewrite Hyy in Hxx. destruct p; destruct p0.
  simpl in *. rewrite H7. apply f_equal2; [ | reflexivity ].
  destruct b; destruct b0; try reflexivity.
  assert (contra := eq_refl true). rewrite Hxx in contra. discriminate contra.
  assert (contra := eq_refl true). rewrite <- Hxx in contra. discriminate contra.

  - subst. clear H3 H1 H4 lpeq' Hxx Hyy pnz p0nz lpeqx n0 H0' H H0 H2 H5 H'.
    generalize lpeq. intro lpeq'.
    rewrite <- map_length with (f:=@snd _ _) in lpeq'.
    rewrite <- map_length with (f:=@snd _ _) in lpeq'.
    assert (Hx := zipeq_right _ _ _ lpeq' Hxy).
    rewrite Forall_forall in Hx.
    assert (Hz := idxeq _ _ _ _ _ _ _ H6). simpl in Hz. assumption.

  - intros. clear Heqpwi pwi H H1.
    rewrite <- prisooeq in Heqpwio.
    rewrite with_idx_elim_prisoo in Heqpwio.
    rewrite Heqpwio in inpf. remember (prisoo'' _ _ _). revert inpf. clear.
    intro. induction l. simpl in inpf. elim inpf.
    simpl in inpf. destruct inpf.
    + clear IHl. rewrite <- H in *. clear x H.
      destruct a. simpl in *. rewrite ps_idxsqkz.
      unfold s2b. simpl. split; intro.
      * subst. reflexivity.
      * destruct ps_k. reflexivity.
        discriminate.
    + apply IHl. assumption.

  - intros. clear Heqpwio pwio H0.
    destruct (divisorspf (H x inpf)).
    rewrite prisoneq in Heqpwi.
    assert (Hx := prisonl_idxle n).
    assert (Hy := prisonl_alldiv n).
    rewrite Forall_forall in *.
    rewrite with_idx_elim_prisonl in Heqpwi.
    destruct (prisonl n) as [ pd pdpf ]. simpl in *. clear pdpf.
    assert (In x (map
             (fun e : fliplelem (S (n + 0)) =>
              (even (length (fe_divs (S (n + 0)) e)), fe_idx (S (n + 0)) e))
             pd)).
      rewrite <- Heqpwi. assumption.
    assert (exists e, In e pd /\ x = (even (length (fe_divs (S (n + 0)) e)), fe_idx (S (n + 0)) e)).
      revert H2. clear. intros. induction pd. elim H2.
      simpl in H2. destruct H2.
        exists a. simpl. split; [ left; reflexivity | ]. rewrite H. reflexivity.
      assert (Hxx := IHpd H). destruct Hxx. exists x0. simpl. split; [ right | ]; apply H0.
    destruct H3. destruct H3 as [ x0inpd xdef ].
    assert (Hy' := Hy _ x0inpd). clear Hy.
    destruct x0. simpl in *. clear x0inpd Hx Heqpwi.
    destruct fe_invariant as [ fidnz [ fdivset [ _ _ ] ] ].
    rewrite xdef at 3. unfold fst in *.
    unfold divisors_nz.
    assert (~ Even (length (remove eq_nat_dec 0 (divisors_raw (H x inpf)))) <-> Even (length (divisors_raw (H x inpf)))).
      assert (Hx := divlcontainsn _ (H x inpf)). cbv zeta in Hx. destruct Hx as [ zin _ ].
      assert (Hy := lrm _ eq_nat_dec _ H0 _ zin).
      rewrite Hy. clear. remember (length _). clear.
      repeat rewrite <- even_spec.
      rewrite Nat.even_succ.
      rewrite <- Nat.negb_even. remember (even n). clear.
      destruct b; split; intro; auto. simpl in H. discriminate.
    rewrite H3. clear H3. rewrite <- even_spec.
    destruct x. inversion xdef. rewrite <- H5 in *.
    unfold snd in H1. assert (forall n, In n fe_divs <-> In n (divisors_raw (H (b, n1) inpf))).
      intros. rewrite <- H1. rewrite Hy'. split; intro; assumption.
    clear Hy' H1.
    assert (Hx := setleneq _ _ _ _ fdivset H0 H3).
    rewrite Hx. split; intro; assumption.
  Grab Existential Variables. assumption.
Qed.

Print Assumptions Unnamed_thm.
