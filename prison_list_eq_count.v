Require Import prison_flip_list.
Require Import prison_count.

Require Import NPeano.
Require Import List.
Require Import Arith.
Require Import math.

Check flipl.

Definition fliplelem2nat lim (e : fliplelem lim) := pred (length (fe_divs _ e)).

Definition flipleleml lim (l : list (fliplelem lim)) := map (fliplelem2nat _) l.

Lemma consconv_proj1_sig_distr :
  forall lim h l lx ex,
    proj1_sig (consconv lim (h::l) h l eq_refl ex lx) = (proj1_sig ex)::(proj1_sig lx).
Proof.
  intros lim l h lx. destruct lx. simpl.
  revert a. revert l. induction x.
  - intros. destruct a. destruct ex. simpl. reflexivity.
  - intros. destruct a0. destruct ex. simpl. reflexivity.
Qed.

Lemma fliplpi :
  forall lim l lpf1 lpf2 k kpf1 kpf2,
    proj1_sig (flipl lim l lpf1 k kpf1) = proj1_sig (flipl lim l lpf2 k kpf2).
Proof.
  induction l. simpl. reflexivity.
  destruct k.
  - intros. simpl. 
    rewrite (consconv_proj1_sig_distr _ a l).
    rewrite (consconv_proj1_sig_distr _ a l).
    unfold dropsnd. simpl. cbv zeta in *. unfold plus at 1 in kpf1. unfold plus at 1 in kpf2.
    destruct lpf1 as [ eqqq lpf1 ]. destruct lpf2 as [ eqqq2 lpf2 ].
    apply f_equal2.
    + assert (kpf1 = kpf2). apply UIP_nat. rewrite H. reflexivity.
    + apply IHl.
  - intros. simpl.
    rewrite (consconv_proj1_sig_distr _ a l).
    rewrite (consconv_proj1_sig_distr _ a l).
    apply f_equal2.
    + assert (kpf1 = kpf2). apply UIP_nat. rewrite H. reflexivity.
    + apply IHl.
Qed.

Lemma mapunfold :
  forall A B (f : A -> B) h t, map f (h::t) = (f h)::(map f t).
Proof.
  simpl. reflexivity.
Qed.

Lemma flipteqflipl :
  forall lim l lc idxc k kpf,
    lc = flipleleml _ l ->
    flipt lc lim k = flipleleml _ (proj1_sig (flipl lim l idxc k kpf)).
Proof.
  induction l. intros. subst.  simpl. reflexivity.
  intros. subst.
  simpl. destruct k.

  - assert (Hx := idxcontt _ _ _ _ idxc eq_refl).
    assert (Hy := IHl (flipleleml _ l) Hx lim).
    assert (match l with
              | nil => True
              | h :: _ =>
                let rem := NPeano.modulo (fe_idx lim h + lim) (S lim) in
                lim = lim + rem
            end) as kpf'.
      cbv zeta. clear Hy IHl. destruct l. constructor. simpl in idxc. destruct idxc as [ _ [ feqa _ ] ].
      cbv zeta in kpf. unfold plus at 1 in kpf. rewrite feqa in *. remember (fe_idx _ a). clear feqa Heqn f a Hx.
      assert (lim mod S lim = lim). clear. apply Nat.mod_small. omega.
      rewrite <- H in kpf at 1.
      assert (Hx := apbmodmeqb_amodmz _ _ _ (eq_flip _ _ _ kpf)).
      assert (S n + lim = n + S lim). clear. omega.
      rewrite H0. rewrite Nat.add_mod.
      rewrite Hx. rewrite Nat.mod_same. simpl. omega. intro. discriminate. intro. discriminate.
    rewrite IHl with (idxc := Hx) (kpf := kpf'); [ | reflexivity ]. clear IHl.
    rewrite (consconv_proj1_sig_distr lim a l).
    unfold flipleleml at 2. 
    rewrite mapunfold.
    unfold fliplelem2nat at 1.
    unfold fliplelem2nat at 1.
    unfold flipleleml.
    apply f_equal2.
    + destruct (fliplkzh _ _ _ _ _). simpl. destruct a0.
      rewrite H0. destruct a. simpl. destruct fe_divs.
      * exfalso. generalize fe_invariant; intro. destruct fe_invariant0 as [ _ [ _ [ _ inv ] ] ].
        revert inv. clear. intros.
        assert (0 <= lim). omega.
        assert (Hx := inv _ H).
        simpl in Hx. rewrite <- Hx. reflexivity.
      * simpl. reflexivity.
    + apply f_equal2; auto.
      apply fliplpi.

  - unfold flipleleml in *.
    rewrite (consconv_proj1_sig_distr _ a l).
    rewrite mapunfold.
    rewrite <- IHl with (lc := map (fliplelem2nat lim) l).
    + apply f_equal2; [ | reflexivity ].
      unfold fliplelem2nat.
      unfold dropsnd. unfold proj1_sig.
      destruct a.
      unfold prison_flip_list.fe_divs.
      destruct (fliplknzh _ _ _ _ _). destruct x. simpl in *. destruct a. rewrite H0. reflexivity.
    + reflexivity.
Qed.

Lemma flipteacheqflipleach :
  forall lim h l cpf,
    fe_idx lim h = 1 ->
    flipteach (flipleleml _ (h::l)) lim = flipleleml _ (proj1_sig (flipleach lim (h::l) cpf)).
Proof.
  unfold flipteach. unfold flipleach. intros.
  rewrite <- flipteqflipl with (lc := flipleleml _ (h::l)); [ | reflexivity ].
  simpl in cpf. destruct cpf as [ _ cpf ].
  rewrite H.
  unfold plus at 1. rewrite Nat.mod_same. simpl.
  destruct lim; auto.
  intro. discriminate.
Qed.

Check convz.
Lemma convzproj1 :
  forall n lim l lx nz,
    flipleleml _ (proj1_sig (convz n lim l lx nz)) = flipleleml _ (proj1_sig lx).
Proof.
  intros. subst. simpl. unfold convz. unfold eq_rec_r. unfold eq_rec. unfold eq_rect. simpl. reflexivity.
Qed.

Lemma fliptwhileeqfliplwhile :
  forall lim h l cpf,
    fe_idx lim h = 1 ->
    fliptwhile (flipleleml _ (h::l)) lim = flipleleml _ (proj1_sig (fliplwhile lim (h::l) cpf lim)).
Proof.
  induction lim.
  - intros. simpl.
    assert (Hx := flipteacheqflipleach 0 h l cpf H).
    unfold flipleleml at 1 in Hx. simpl in Hx. unfold flipleleml at 1.
    rewrite Hx. clear.
    unfold convz. unfold eq_rec_r. unfold eq_rec. unfold eq_rect. simpl. reflexivity.
  - intros. simpl. 
Qed.

Lemma fliplisteqcount :
  forall n,
    prisont n = map (fliplelem2nat _) (proj1_sig (prisonl n)).
Proof.
  induction n. simpl. unfold prisont. simpl. unfold flipteach. simpl. reflexivity.
  unfold prisont in *. simpl in *.
  unfold prisonl in *. simpl in *.
Qed.