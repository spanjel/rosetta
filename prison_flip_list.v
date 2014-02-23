Require Import List.

Require Import NPeano.
Require Import math.
Require Import Arith.

Require Import list_facts.

Definition hdx A (l : {l : list A | l <> nil}) :=
  match proj1_sig l as xx return proj1_sig l = xx -> A with
    | nil => fun pf => False_rect _ ((proj2_sig l) pf)
    | h::_ => fun _ => h
  end (eq_refl (proj1_sig l)).

Record fliplelem (fe_lim : nat) :=
  {
    fe_idx : nat;
    fe_divs : list nat;
    fe_invariant : fe_idx <> 0 /\
                   is_set eq_nat_dec fe_divs = true /\
                   Forall (fun x => fe_idx mod x = 0 /\ x <= fe_lim) fe_divs /\
                   forall x,
                     x <= fe_lim ->
                     (fe_idx mod x = 0 <-> In x fe_divs)
  }.

Definition alldivs
           lim
           (fe : fliplelem lim)
           (idxpf : (fe_idx _ fe) <= lim) :
  {l | fe_divs _ fe = l /\ is_set eq_nat_dec l = true /\ forall x, (fe_idx _ fe) mod x = 0 <-> In x l}.
Proof.
  destruct fe. simpl in *.
  destruct fe_invariant0 as [ idxnz [ dset [ alldiv divin ] ] ].
  refine (exist _ fe_divs0 _).
  split; [ reflexivity | split; [ assumption | ] ].
  intro.
  induction x using (nat_interval_ind (S lim)). apply divin. omega.
  assert (Hx := fun m => gtnotdivides fe_idx0 m idxnz).
  split; intro.
  - assert (Hy := Hx x). assert (fe_idx0 < x). omega.
    elim (Hy H1). assumption.
  - rewrite Forall_forall in alldiv. apply alldiv. assumption.
Defined.

Fixpoint idxcont' {lim} l pidx :=
  match l with
    | nil => True
    | h::t => (fe_idx lim h) = pidx /\ idxcont' t (S (fe_idx lim h))
  end.

Definition idxcont {lim} l :=
  match l with
    | nil => True
    | h::_ => @idxcont' lim l (fe_idx _ h)
  end.

Definition idxidem {lim lim'} l ll := Forall (fun e => fe_idx lim (fst e) = fe_idx lim' (snd e)) (zipmin l ll).

Lemma Slimdivs :
  forall k n m,
    m = k + (n + m) mod S m ->
    match k with
      | O => n mod S m = 0
      | S _ => n mod S m <> 0
    end.

Proof.
  intros. rename H into kpf.
  assert (S m <> 0) as Smnz. intro. discriminate H.
  assert (m = m mod S m) as meqmmSm. clear. rewrite Nat.mod_small; [ reflexivity | ]. omega.
  destruct k.

  - unfold plus at 1 in kpf.
    assert (Hx := Nat.add_mod n m (S m) Smnz).
    rewrite Hx in kpf.
    rewrite meqmmSm in kpf at 1.
    rewrite <- meqmmSm in kpf at 2.
    assert (Hy := apbmodmeqb_amodmz _ _ _ (eq_flip _ _ _ kpf)).
    rewrite Nat.mod_mod in Hy. assumption.
    intro. discriminate.

  - intro nmSm. rewrite Nat.add_mod in kpf.
    + rewrite nmSm in kpf.
      unfold plus at 2 in kpf.
      repeat rewrite <- meqmmSm in kpf.
      revert kpf. clear. intro. omega.
    + intro. discriminate.
Defined.

Lemma idxidemnil : forall lim lim', @idxidem lim lim' nil nil. unfold idxidem. simpl. constructor. Qed.

Definition convlnil
           lim (l : list (fliplelem lim))
           (v : {lx : list (fliplelem (S lim)) | length lx = length (@nil (fliplelem lim)) /\ idxidem lx (@nil (fliplelem lim))})
           (lnilpf : l = nil) :
  {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l}.
Proof.
  rewrite lnilpf in *.
  apply v.
Defined.

Lemma nltSn : forall n, n < S n. intros. omega. Qed.

Definition fliplkzh
           lim
           (h : fliplelem lim)
           k
           (kpf : let rem := ((fe_idx _ h) + lim) mod (S lim) in
                  lim = k + rem)
           (kz : k = 0) :
  { e : fliplelem (S lim) | fe_idx _ e = fe_idx _ h /\ fe_divs _ e = (S lim)::(fe_divs _ h) }.

Proof.
  rewrite kz in *. clear kz.
  unfold plus at 2 in kpf.
  cbv zeta in kpf.
  assert (Hx := eq_flip _ _ _ kpf).
  assert (lim = lim mod S lim) as modsmall. clear. rewrite Nat.mod_small. reflexivity. apply nltSn.
  rewrite modsmall in Hx.
  assert (Hy := apbmodmeqb_amodmz _ _ _ Hx). clear kpf Hx modsmall.
  destruct h. unfold fe_idx in *. unfold fe_divs in *.
  destruct fe_invariant0 as [ idxnz [ dset [ dNle letdiffin ] ] ].
  rewrite Forall_forall in dNle.
  set (res := Build_fliplelem (S lim) fe_idx0 (S lim::fe_divs0)).
  
  assert (fe_idx0 <> 0 /\
          is_set eq_nat_dec (S lim :: fe_divs0) = true /\
          Forall (fun x : nat => fe_idx0 mod x = 0 /\ x <= S lim)
                 (S lim :: fe_divs0) /\
          (forall x : nat,
             x <= S lim -> (fe_idx0 mod x = 0 <-> In x (S lim :: fe_divs0)))).
         
  split; [ assumption | split; [ | split ] ].

  - simpl. rewrite dset. clear dset letdiffin.
    destruct (inb _ _ _) eqn:inbeq; [ exfalso | reflexivity ].
    rewrite inbeqIn in inbeq.
    destruct (dNle _ inbeq) as [ _ modsm ].
    omega.

  - rewrite Forall_forall. intros x indiv.
    simpl in indiv. destruct indiv as [ Slimeqx | indiv ]; [ rewrite <- Slimeqx in * | ]; split.
    + assumption.
    + constructor.
    + rewrite letdiffin. assumption.
      apply dNle. assumption.
    + destruct (dNle _ indiv) as [ xdiv xle ]. omega.

  - intros x xleSlim. split; [ intro xdiv | intro xin ].
    + simpl. destruct (eq_nat_dec x (S lim)) as [ xeq | xne ].
      * rewrite xeq in *. left. constructor.
      * right. rewrite <- letdiffin. assumption. omega.
    + simpl in xin. destruct xin as [ xeq | xin ].
      * rewrite <- xeq. assumption.
      * destruct (eq_nat_dec x (S lim)) as [ xeq | xne ].
          rewrite xeq. assumption.
        rewrite letdiffin. assumption.
        omega.

  - assert (fe_idx _ (res H) = fe_idx0). unfold res. simpl. reflexivity.
    exists (res H). unfold res. split; reflexivity.
Defined.

Definition fliplknzh
           lim
           (h : fliplelem lim)
           k
           (kpf : let rem := ((fe_idx _ h) + lim) mod (S lim) in
                  lim = k + rem)
           k'
           (knz : k = S k') :
  { e : fliplelem (S lim) | fe_idx _ e = fe_idx _ h /\ fe_divs _ e = fe_divs _ h }.

Proof.
  cbv zeta in kpf. rewrite knz in *. clear k knz.
  destruct h. unfold fe_idx at 2. unfold fe_idx in kpf. unfold fe_divs in *.
  destruct fe_invariant0 as [ idxnz [ dset [ ddNxle letdiffin ] ] ].
  rewrite Forall_forall in ddNxle.
  set (res := Build_fliplelem (S lim) fe_idx0 fe_divs0).
  assert (fe_idx0 <> 0 /\
          is_set eq_nat_dec fe_divs0 = true /\
          Forall (fun x : nat => fe_idx0 mod x = 0 /\ x <= S lim) fe_divs0 /\
          (forall x : nat, x <= S lim -> (fe_idx0 mod x = 0 <-> In x fe_divs0))) as respf; [ clear res | ].
  split; [ | split; [ | split ] ]; auto.

  - rewrite Forall_forall. intros x xin.
    destruct (ddNxle _ xin) as [ xdiv xle ].
    split; [ assumption | ].
    revert xle. clear. intro. omega.

  - intros x xleSlim.
    destruct (eq_nat_dec x (S lim)) as [ xeq | xne ]; [ | apply letdiffin; omega ].
    rewrite xeq in *. clear xeq x.
    clear xleSlim.
    split; [ intro Slimdiv | intro Slimin ]; exfalso.
    + assert (Hx := Slimdivs _ _ _ kpf). cbv iota beta in Hx.
      elim Hx. assumption.
    + destruct (ddNxle _ Slimin) as [ _ impo ]. revert impo. clear. intros. omega.

  - exists (res respf).
    unfold res. simpl. split; reflexivity.
Defined.

Definition kremconv
           k
           lim
           h
           l'
           l
           (lpf : l = h::l')
           (v : match l with
                  | nil => True
                  | h :: _ => let rem := (fe_idx lim h + lim) mod S lim in lim = k + rem
                end) :
  (let rem := (fe_idx lim h + lim) mod S lim in lim = k + rem).
Proof.
  rewrite lpf in *. assumption.
Defined.

Definition consconv
           lim
           (l : list (fliplelem lim))
           h
           l'
           (lpf : l = h::l')
           (e': { e : fliplelem (S lim) | fe_idx _ e = fe_idx _ h })
           (lx' : {lx : list (fliplelem (S lim)) | length lx = length l' /\ idxidem lx l'}) :
  {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l}.
Proof.
  rewrite lpf in *. clear lpf l.
  destruct lx' as [ lx [ lxlen lxidem ] ].
  destruct e' as [ e epf ].
  exists (e::lx).
  split.
  - simpl. rewrite lxlen. reflexivity.
  - unfold idxidem. simpl. constructor.
    + simpl. assumption.
    + apply lxidem.
Defined.

Definition idxcontt
           lim
           (l : list (fliplelem lim))
           h
           t
           (lpf : idxcont l)
           (leq : l = h::t) :
  idxcont t.
Proof.
  rewrite leq in *. clear leq l.
  simpl in lpf. destruct lpf.
  unfold idxcont.
  destruct t. constructor.
  simpl in *. split; [ reflexivity | ].
  apply H0.
Qed.

Definition nextkkz
           lim
           (l : list (fliplelem lim))
           h
           t
           k
           (leq : l = h::t)
           (idxc : idxcont l)
           (kpf : lim = k + (fe_idx _ h + lim) mod S lim)
           (kz : k = 0) :
  match t with
    | nil => True
    | h :: _ => let rem := (fe_idx lim h + lim) mod S lim in lim = lim + rem
  end.
Proof.
  destruct t. constructor.
  rewrite leq in *. clear leq l.
  simpl in idxc. destruct idxc as [ _ [ sfeqh idxc ] ].
  rewrite sfeqh in *. clear f sfeqh idxc t.
  cbv zeta.
  rewrite kz in *. clear k kz.
  unfold plus at 1 in kpf.
  unfold plus. fold plus.
  assert (forall a, S a = 1 + a). clear. intros. omega.
  rewrite H. clear H.
  rewrite Nat.add_mod; [ | intro; discriminate ]. rewrite <- kpf.
  clear h kpf.
  destruct lim. simpl. reflexivity.
  destruct lim. simpl. reflexivity.
  assert (1 mod S (S (S lim)) = 1). apply Nat.mod_small. omega.
  rewrite H. clear H.
  assert (1 + (S (S lim)) = S (S (S lim))). simpl. reflexivity.
  rewrite H. clear H.
  rewrite Nat.mod_same; [ | intro; discriminate ].
  rewrite plus_comm. simpl. reflexivity.
Defined.

Definition nextkknz
           lim
           (l : list (fliplelem lim))
           h
           t
           k
           k'
           (leq : l = h::t)
           (idxc : idxcont l)
           (kpf : lim = k + (fe_idx _ h + lim) mod S lim)
           (knz : k = S k') :
  match t with
    | nil => True
    | h :: _ => let rem := (fe_idx lim h + lim) mod S lim in lim = k' + rem
  end.
Proof.
  destruct t. constructor.
  rewrite leq in *. clear l leq.
  simpl in idxc. destruct idxc as [ _ [ feqh _ ] ].
  rewrite feqh in *. clear feqh t f.
  assert (Hx := Slimdivs _ _ _ kpf).
  rewrite knz in *. clear k knz.
  cbv zeta.
  unfold plus; fold plus.
  rewrite xmodmnem_SxmodmeqSxmodm.
  - rewrite plus_comm. simpl. rewrite plus_comm. simpl in kpf. apply kpf.
  - intro. discriminate.
  - intro. clear kpf k'.
    assert ((fe_idx lim h + lim) mod S lim = lim). injection H. intro. assumption. clear H.
    rewrite Nat.add_mod in H0; [ | intro; discriminate ].
    assert (lim = lim mod S lim). clear. rewrite Nat.mod_small. reflexivity. omega.
    rewrite <- H in H0.
    assert (forall A (a b c : A), a = b -> b = c -> a = c). clear. intros. subst. reflexivity.    
    assert (Hy := H1 _ _ _ _ H0 H). clear H1 H H0.
    assert (Hz := apbmodmeqb_amodmz _ _ _ Hy).
    rewrite Nat.mod_mod in Hz. elim Hx. assumption.
    intro. discriminate.
Defined.

Definition dropsnd A P Q (v : {x : A | P x /\ Q x}) : {x | P x} := exist _ (proj1_sig v) (proj1 (proj2_sig v)).

Fixpoint flipl
         lim
         (l : list (fliplelem lim))
         (lpf : idxcont l)
         (k : nat)
         (kpf : match l with
                  | nil => True
                  | h::_ => let rem := ((fe_idx _ h) + lim) mod (S lim) in
                            lim = k + rem
                end) :
  {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l} :=
  match l as lx return l = lx -> {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l} with
    | nil => fun eqpf =>
               convlnil _ _
                        (exist _
                           (@nil (fliplelem (S lim)))
                           (conj
                              (eq_refl (length nil))
                              (idxidemnil _ _)))
                        eqpf
    | h::t => fun leq => match k
                               as kx
                               return k = kx ->
                                      {lx : list (fliplelem (S lim)) |
                                       length lx = length l /\ idxidem lx l}
                         with
                           | O    => fun kz  =>
                                       let krem := kremconv _ _ _ _ _ leq kpf in
                                       consconv _ _ _ _ leq
                                                (dropsnd _ _ _ (fliplkzh _ h _ krem kz))
                                                (flipl
                                                   lim
                                                   t
                                                   (idxcontt _ _ _ _ lpf leq)
                                                   lim
                                                   (nextkkz _ _ _ _ _ leq lpf krem kz))
                           | S k' => fun knz =>
                                       let krem := (kremconv _ _ _ _ _ leq kpf) in
                                       consconv _ _ _ _ leq
                                                (dropsnd _ _ _ (fliplknzh _ h _ krem _ knz))
                                                (flipl
                                                   lim
                                                   t
                                                   (idxcontt _ _ _ _ lpf leq)
                                                   _
                                                   (nextkknz _ _ _ _ _ _ leq lpf krem knz))
                         end eq_refl
  end eq_refl.

Lemma idxidemidxc' :
  forall lim0 l a0 lim1 ll,
    length l = length ll ->
    @idxcont' lim0 l a0 ->
    idxidem l ll ->
    @idxcont' lim1 ll a0.
Proof.
  induction l. unfold idxidem. intros. assert (ll = nil). destruct ll; [ reflexivity | ]. simpl in H. discriminate H. rewrite H2 in *. simpl. apply I.

  intros. destruct ll. simpl in H. discriminate H.
  unfold idxidem in H1. simpl in H1. inversion H1. clear H1. subst. simpl in *. rewrite H4 in *. clear a H4.
  destruct H0. split; [ assumption | ].
  injection H. intro lleqlll.
  apply (IHl _ _ _ lleqlll); assumption.
Qed.

Lemma idxidemidxc :
  forall lim0 l lim1 ll,
    length l = length ll ->
    @idxcont lim0 l ->
    idxidem l ll ->
    @idxcont lim1 ll.
Proof.
  intros. unfold idxcont in *.
  destruct ll. apply I.
  apply idxidemidxc' with (l := l); try assumption.
  destruct l. simpl in H. discriminate H.
  cut (fe_idx lim0 f0 = fe_idx lim1 f). intro. rewrite <- H2. assumption.
  revert H1. clear. intro.
  unfold idxidem in H1. simpl in H1. inversion H1. clear H1. subst. simpl in H2. assumption.
Qed.

Lemma idxidemrefl :
  forall lim l llim ll,
    @idxidem lim llim l ll <-> idxidem ll l.
Proof.
  induction l.
  - intros; split; intro.
    + destruct ll. unfold idxidem. simpl. constructor.
      unfold idxidem. constructor.
    + unfold idxidem. constructor.
  - intros; split; intro.
    + unfold idxidem in *. destruct ll. simpl. constructor.
      constructor. simpl. simpl in H. inversion H. simpl in H2. rewrite H2. reflexivity.
      fold @zipmin. apply IHl.
      simpl in H. inversion H. apply H3.
    + unfold idxidem in *. destruct ll. simpl. constructor.
      constructor. simpl. simpl in H. inversion H. simpl in H2. rewrite H2. reflexivity.
      fold @zipmin. apply IHl.
      simpl in H. inversion H. apply H3.
Qed.

Lemma idxidemtrans :
  forall lim l llim ll lllim lll,
    length l = length ll -> length ll = length lll ->
    @idxidem lim llim l ll -> idxidem ll lll -> @idxidem _ lllim l lll.
Proof.
  induction l. intros. constructor.
  intros. unfold idxidem in *. destruct lll. simpl. constructor.
  simpl. constructor.
  - simpl. destruct ll.
    + simpl in H0. discriminate.
    + simpl in H1. simpl in H2. inversion H1. simpl in H5. rewrite H5.
      clear H5 H6 H3 H4.
      inversion H2.
      simpl in H5. rewrite H5.
      reflexivity.
  - destruct ll.
    + simpl in H. discriminate.
    + apply IHl with (ll := ll) (llim := llim).
      * simpl in H. injection H. intro. assumption.
      * simpl in H0. injection H0. intro. assumption.
      * simpl in H1. inversion H1. assumption.
      * simpl in H2. inversion H2. assumption.
Qed.

Lemma ididxidem :
  forall lim l,
    @idxidem lim _ l l.
Proof.
  induction l. constructor.
  constructor. reflexivity.
  fold @zipmin. apply IHl.
Qed.

Definition kcheck
           lim
           l
           n
           (neq : n = match l with
                        | nil => 0
                        | h::_ => (lim - ((fe_idx lim h + lim) mod S lim))
                      end) :
  match l with
    | nil => True
    | hx::_ => let rem := ((fe_idx _ hx) + lim) mod S lim in
               lim = n + rem
  end.
Proof.
  destruct l. constructor.
  cbv zeta.
  assert (forall a b, a <= b -> b - a + a = b). clear. intros. omega.
  rewrite neq.
  rewrite H. reflexivity. clear H.
  assert (forall a b, a < S b -> a <= b). clear. intros. omega.
  apply H. clear H.
  apply Nat.mod_upper_bound. intro. discriminate.
Qed.

Definition flipleach lim (l : list (fliplelem lim)) (cpf : idxcont l) :
  {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l} :=
  flipl _ _ cpf
        match l with
          | nil => 0
          | h::_ => (lim - ((fe_idx lim h + lim) mod S lim))
        end
        (kcheck _ _ _ eq_refl).

Definition convz
           n
           lim
           (l : list (fliplelem lim))
           (x : {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l})
           (nz : n = 0) :
  {lx : list (fliplelem (S (n + lim))) | length lx = length l /\ idxidem lx l}.
Proof. subst. unfold plus in *. apply x. Defined.

Lemma lfll :
  forall lim l cpf,
    length l = length (proj1_sig (flipleach lim l cpf)).
Proof.
  intros.
  destruct (flipleach _ _ _). simpl. destruct a. rewrite H. reflexivity.
Qed.

Definition convS
           lim n' (l : list (fliplelem lim)) n cpf
           (v : {lx : list (fliplelem (S (n' + S lim))) |
                  length lx = length (proj1_sig (flipleach lim l cpf)) /\
                  idxidem lx (proj1_sig (flipleach lim l cpf))})
           (eqpf : n = S n') :
  {lx : list (fliplelem (S (n + lim))) | length lx = length l /\ idxidem lx l}.
Proof.
  destruct v as [ lx [ lpf idxi ] ].
  rewrite eqpf in *. clear eqpf.
  assert (S (S n' + lim) = S (n' + S lim)). omega.
  rewrite H. clear H.
  exists lx. destruct (flipleach _ _ cpf). unfold proj1_sig in *.
  destruct a.
  rewrite lpf. rewrite H. split; [ reflexivity | ].
  apply idxidemtrans with (ll := x); auto.
Defined.

Lemma fliplwhilecont
      lim
      (l : list (fliplelem lim))
      (lc : idxcont l)
      (lx : {lx : list (fliplelem (S lim)) | length lx = length l /\ idxidem lx l}) :
  idxcont (proj1_sig lx).
Proof.
  destruct lx. simpl. destruct a.
  apply idxidemidxc with (l := l); auto.
  apply idxidemrefl. assumption.
Qed.

Fixpoint fliplwhile
         lim
         (l : list (fliplelem lim))
         (cpf : idxcont l)
         (n : nat) :
  {lx : list (fliplelem (S (n + lim))) | length lx = length l /\ idxidem lx l} :=
  match n as nx return n = nx -> {lx : list (fliplelem (S (n + lim))) | length lx = length l /\ idxidem lx l} with
    | O => fun eqpf => convz _ _ _ (flipleach _ _ cpf) eqpf
    | S n' => fun eqpf =>
                convS _ _ _ _ _
                      (fliplwhile
                         (S lim)
                         (proj1_sig (flipleach _ _ cpf))
                         (fliplwhilecont _ _ cpf _)
                         n')
                      eqpf
  end eq_refl.

Lemma revnn :
  forall A (l : list A) h t (ln : l = h::t), (rev l) <> nil.
Proof.
  intros. rewrite ln in *. intro. simpl in *. destruct (rev t).
  simpl in H. discriminate.
  simpl in H. discriminate.
Qed.

Fixpoint derivP A B (m : A -> B) (P : B -> B -> Prop) (dec : forall a aa, {P a aa}+{~P a aa}) l z :=
  match l with
    | nil => True
    | h::t => if dec z (m h)
              then derivP _ _ m P dec t (m h)
              else False
  end.

Lemma derivPdec :
  forall A B m P dec l z, {derivP A B m P dec l z}+{~derivP A B m P dec l z}.
Proof.
  induction l. simpl. intros. left. constructor.
  intros. simpl. destruct (dec z (m a)). apply IHl.
  right. intro. assumption.
Qed.

Lemma derivpfx :
  forall A B m P dec l x z,
    derivP A B m P dec (l ++ x::nil) z ->
    derivP A B m P dec l z.
Proof.
  induction l. simpl. constructor.
  simpl. intros. destruct (dec z (m a)).
  - apply IHl with (x := x). assumption.
  - assumption.
Qed.

Lemma derivcat :
  forall A B m P dec l z ll zz,
    derivP A B m P dec l z ->
    (zz = match l as lx return l = lx -> B with
       | nil => fun _ => z
       | h::t => fun leq => m (hdx _ (exist _ (rev l) (revnn _ _ _ _ leq)))
     end eq_refl) ->
    derivP A B m P dec ll zz ->
    derivP A B m P dec (l ++ ll) z.
Proof.
  induction l using rev_ind. simpl. intros. subst. assumption.
  intros z ll zz lxconf zzdef llconf. rewrite zzdef in *. clear zz zzdef.
  rewrite <- app_assoc.
  set (newzz :=
         match l as lx return l = lx -> B with
           | nil => fun _ => z
           | h::t => fun leq => m (hdx _ (exist _ (rev l) (revnn _ _ _ _ leq)))
         end eq_refl).
  apply IHl with (zz := newzz); clear IHl.
  - revert lxconf. clear. intros. apply derivpfx with (x := x). assumption.
  - unfold newzz. reflexivity.
  - unfold newzz. clear newzz.
    assert (forall A l a x pf, hdx A (exist _ (rev (a::(l ++ x::nil))) pf) = x). clear. intros.
    remember (a::l++x::nil).
    assert (a::l++x::nil = (a::l) ++ x::nil). simpl. reflexivity.
    rewrite H in Heql0. clear H. subst.
    remember (rev ((a::l) ++ x::nil)).
    assert (Hx := rev_app_distr (a::l) (x::nil)). rewrite Hx in Heql0.
    clear Hx. subst. simpl. unfold hdx. simpl. reflexivity.
    destruct l. simpl in *. unfold hdx in llconf; simpl in llconf. destruct (dec z (m x)); auto.
    assert ((a :: l) ++ x :: nil = a::(l++x::nil)). clear. simpl. reflexivity.
    rewrite H0 in llconf. clear H0.
    rewrite H in llconf. clear H.
    simpl. destruct (dec _ (m x)). assumption.
    elim n. clear n llconf.
    simpl in lxconf. destruct (dec z (m a)); [ | elim lxconf ].
    revert lxconf. clear. revert x a. induction l. simpl in *. intros. unfold hdx. simpl. destruct (dec (m a) (m x)); auto. elim lxconf.
    intros. simpl in lxconf. destruct (dec (m a0) (m a)); [ | elim lxconf ].
    assert (Hx := IHl _ _ lxconf). clear IHl lxconf.
    assert (forall a b x, a = b -> P a x -> P b x). clear. intros. rewrite <- H. assumption.
    apply H with (a := m (hdx A
            (exist (fun l : list A => l <> nil) (rev l ++ a :: nil)
               (revnn A (a :: l) a l eq_refl)))). clear H Hx.
    assert (forall A l pf a, hdx A (exist _ l pf) = hd a l). clear. intros. induction l. elim pf. reflexivity. simpl. unfold hdx. simpl. reflexivity.
    repeat rewrite H with (a := a).
    simpl. rewrite <- app_assoc. simpl. destruct (rev l). simpl. reflexivity. simpl. reflexivity.
    assumption.
Qed.

Lemma hdxspeccase :
  forall A l a b pf, hdx A (exist _ (rev (l ++ a::nil) ++ b::nil) pf) = a.
Proof.
  intros A l a b. rewrite rev_app_distr. simpl. unfold hdx. simpl. reflexivity.
Qed.

Lemma hdxspeccase2 :
  forall A l a b c pf, hdx A (exist _ ((rev (l ++ a::nil) ++ b::nil) ++ c::nil) pf) = a.
Proof.
  intros A l a b c. rewrite rev_app_distr. simpl. unfold hdx. simpl. reflexivity.
Qed.

Lemma derivpsplit :
  forall A B m P dec ll z l,
    derivP A B m P dec (l ++ ll) z ->
    derivP A B m P dec l z /\
    derivP A B m P dec ll (match l as lx return l = lx -> B with
                             | nil => fun _ => z
                             | h::t => fun leq => m (hdx _ (exist _ (rev l) (revnn _ _ _ _ leq)))
                           end eq_refl).

Proof.
  induction ll. intros. rewrite app_nil_r in H. split; auto. simpl. constructor.
  intros z l lallconf. assert (IHll' := IHll z (l ++ a::nil)). clear IHll.
  assert (derivP A B m P dec ((l ++ a::nil) ++ ll) z) as lxconf.
    clear IHll'. rewrite <- app_assoc. simpl. assumption.
  assert (IHll'' := IHll' lxconf). clear IHll' lxconf.
  destruct IHll'' as [ laconf llconf ].
  split; [ apply derivpfx with (x := a); assumption | ].
  simpl. destruct l; simpl in *; auto.

  destruct (dec _ (m a)); [ rewrite hdxspeccase in *; assumption | ].
  elim n. clear n. clear llconf lallconf.

  destruct (dec z (m a0)) as [ _ | _ ]; [ | contradiction ].
  revert dependent a. revert dependent a0. revert dependent l. clear.

  induction l.
  - simpl in *. unfold hdx. simpl in *. intros. destruct (dec _ _); auto. contradiction.
  - intros.
    simpl in laconf. destruct (dec (m a0) (m a)) as [ _ | _ ]; [ | contradiction ].
    assert (res := IHl _ _ laconf). clear IHl laconf.
    simpl. induction l using rev_ind; [ | clear IHl ].
    + simpl in *. unfold hdx in *. simpl in *. assumption.
    + rewrite hdxspeccase in res.
      rewrite hdxspeccase2. assumption.
Qed.

Definition mpred n (nnz : n <> 0) : nat. destruct n. elim nnz. reflexivity. apply n. Defined.
Definition Sdec n m : {S n = m}+{S n <> m}. apply eq_nat_dec. Defined.
Lemma idxc2deriv :
  forall lim l n (nnz : n <> 0),
    @idxcont' lim l n <-> derivP _ _ (fe_idx _) (fun a b => S a = b) Sdec l (mpred _ nnz).
Proof.
  induction l. simpl. intros. split; auto.
  intros. destruct n. elim nnz. reflexivity. unfold mpred in *. split; intro.
  - simpl in H. rewrite IHl in H.
    + simpl. destruct H. destruct (Sdec n _).
      * assumption.
      * elim n0. rewrite H. reflexivity.
    + intro. discriminate H0.
  - simpl. rewrite IHl.
    + simpl in H. destruct (Sdec n _).
      * split. rewrite e. reflexivity.
        assumption.
      * elim H.
    + intro. discriminate.
Qed.

Definition idxcontt_app
           lim
           i
           e
           (l : list (fliplelem lim))
           (lpf : idxcont l)
           (leq : l = i ++ e) :
  idxcont i /\ idxcont e.
Proof.
  revert dependent lim. induction i using rev_ind. simpl. intros. subst. split; auto.
  intros. rewrite leq in *. clear l leq.
  assert (Hx := IHi (x::e) _ lpf). clear IHi. rewrite <- app_assoc in Hx. simpl in Hx.
  destruct (Hx eq_refl) as [ icont [ _ econt' ] ]; clear Hx.
  split.
  - unfold idxcont in *. destruct i. simpl in *. auto.
    simpl in *. split; auto. destruct lpf as [ _ ixepf ].
    rewrite idxc2deriv in *.
    destruct (derivpsplit _ _ _ _ _ _ _ _ ixepf) as [ res _ ].
    apply res.
  - unfold idxcont. destruct e; [ constructor | ].
    unfold idxcont in *. destruct i.
    + simpl in *. destruct lpf as [ _ [ fidSxid econt ] ].
      split; [ reflexivity | ].
      assumption.
    + simpl in *. destruct lpf as [ _ ixfecont ].
      destruct icont as [ _ icont ].
      destruct econt' as [ fideqSxid econt' ].
      split; [ reflexivity | ].
      assumption.
  Grab Existential Variables.
  intro contra; discriminate contra.
  intro contra; discriminate contra.
  intro contra; discriminate contra.
Qed.

Lemma idxcnz :
  forall lim l n,
    l <> nil ->
    @idxcont' lim l n ->
    n <> 0.
Proof.
  intros. destruct l. elim H. reflexivity.
  simpl in H0. destruct H0. rewrite <- H0. clear. intro. destruct f. exfalso. simpl in H. destruct fe_invariant0 as [ idnz _ ]. elim idnz. assumption.
Qed.

Definition isnil A l : {l = @nil A}+{l <> nil}. destruct l. left. reflexivity. right. intro. discriminate H. Defined.

Lemma idxcapp :
  forall lim l ll n nn,
    @idxcont' lim l n ->
    (nn = match l as lx return l = lx -> nat with
       | nil => fun _ => n
       | h::t => fun leq => S (fe_idx _ (hdx _ (exist _ (rev l) (revnn _ _ _ _ leq))))
     end eq_refl) ->
    @idxcont' lim ll nn ->
    idxcont' (l ++ ll) n.
Proof.
  intros.
  destruct (isnil _ l); destruct (isnil _ ll); subst; simpl; auto. rewrite app_nil_r. assumption.
  assert (Hx := idxcnz _ _ _ n0 H).
  assert (Hy := idxcnz _ _ _ n1 H1).
  rewrite (idxc2deriv _ _ _ Hx) in H.
  rewrite (idxc2deriv _ _ _ Hy) in H1.
  assert (l ++ ll <> nil). destruct l. auto. destruct ll. auto. simpl. intro. discriminate.
  rewrite (idxc2deriv _ _ _ Hx).
  refine (derivcat _ _ _ _ _ _ _ _ _ H _ H1).
  destruct l. destruct n. elim Hy. reflexivity. simpl. reflexivity.
  induction l using rev_ind; auto.
Qed.

Lemma hdx2hd :
  forall A l pf a,
    hdx A (exist _ l pf) = hd a l.
Proof.
  induction l. intros. elim pf. reflexivity.
  simpl. unfold hdx. simpl. reflexivity.
Qed.

Lemma hd_error_app :
  forall A l (a b : A),
    hd_error (l ++ (a::nil) ++ b::nil) = hd_error (l ++ a::nil).
Proof.
  induction l. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Definition prisonlbase
           (idx' : nat) :
  { l : list (fliplelem 0) | l <> nil /\
                             (forall h,
                                hd_error l = Some h ->
                                fe_idx _ h = S idx') /\
                             (forall h,
                                hd_error (rev l) = Some h ->
                                fe_idx _ h = 1) /\
                             length l = S idx' /\
                             idxcont (rev l) }.

Proof.
  induction idx'.

  - pose (Build_fliplelem 0 1 (0::nil)).
    assert (1 <> 0 /\
            is_set eq_nat_dec (0 :: nil) = true /\
            Forall (fun x : nat => 1 mod x = 0 /\ x <= 0) (0 :: nil) /\
            (forall x : nat, x <= 0 -> (1 mod x = 0 <-> In x (0 :: nil)))).
    split. intro. discriminate.
    split. simpl. reflexivity.
    split. rewrite Forall_forall. intros. simpl in H. destruct H; [ | elim H ]. rewrite <- H in *. split; auto.
    intros. assert (x = 0). omega. rewrite H0 in *. simpl. split; auto.
    pose (f H).
    exists (f0::nil).
    split. intro.  discriminate H0.
    split. intros. simpl in H0. inversion H0. unfold f0. simpl. reflexivity.
    simpl. split; auto.
    intros. unfold f0 in H0. unfold f in H0. inversion H0. simpl. reflexivity.

  - destruct IHidx'. destruct x. destruct a. elim H. reflexivity.
    destruct a as [ _ [ a [ endone [ lres xc ] ] ] ].
    assert (Hx := a f eq_refl). clear a.
    pose (Build_fliplelem 0 (S (S idx')) (0::nil)).
    assert (S (S idx') <> 0 /\
            is_set eq_nat_dec (0 :: nil) = true /\
            Forall (fun x : nat => S (S idx') mod x = 0 /\ x <= 0) (0 :: nil) /\
            (forall x : nat, x <= 0 -> (S (S idx') mod x = 0 <-> In x (0 :: nil)))) as respf.
      split. intro. discriminate.
      split. simpl. reflexivity.
      split. rewrite Forall_forall. intros. simpl in H. destruct H; [ | elim H ]. rewrite <- H in *. simpl. split; auto.
      intros. assert (x0 = 0). omega. rewrite H0 in *. simpl. split; auto.
   pose (f0 respf).
   exists (f1::f::x).
   split. intro. discriminate.
   split. intros. simpl in H. inversion H. rewrite <- H1 in *. clear h H1.
   unfold f1. unfold f0. simpl. reflexivity.
   split. intros. simpl in endone. simpl in H. rewrite <- app_assoc in H. rewrite hd_error_app in H. apply endone. assumption.
   split. simpl. rewrite <- lres. simpl. reflexivity.
   unfold f0 in f1. clear f0.
   simpl in *. remember (rev x). clear Heql x lres.
   unfold idxcont in *. destruct l. simpl in *. rewrite Hx. auto.
   simpl in *. split; [ reflexivity | ]. 
   destruct xc as [ _ lfc ].
   destruct f0. simpl in *. remember (S fe_idx0). revert lfc Hx. clear. intros.
   assert (fe_idx _ f1 = S (S idx')). unfold f1. simpl. reflexivity.
   remember f1. remember (S idx'). revert Hx H lfc. clear. intros.
   apply idxcapp with (nn := S n0). assumption.
   destruct l. simpl. unfold hdx. simpl. rewrite <- Hx. reflexivity.
   simpl. rewrite <- Hx. apply f_equal. rewrite hdx2hd with (a := f).
   rewrite rev_app_distr. simpl. reflexivity.
   simpl. split; auto.
Defined.

Definition prisonl cells := let base := prisonlbase cells in
                            fliplwhile _ (rev (proj1_sig base)) (proj2 (proj2 (proj2 (proj2 (proj2_sig base))))) cells.
