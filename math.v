Require Import Zdiv.
Require Import List.
Require Import Arith.
Require Import Zquot.
Require Import NPeano.
Require Import PeanoNat.
Import Nat.
Require Export ucp.
Require Export logic.
Require Export list_facts.

Inductive evenl A :=
| Enil : evenl A
| Econsc : A -> A -> evenl A -> evenl A.

Definition divides_dec n m : {n mod m = 0}+{n mod m <> 0}.
Proof.
  apply eq_nat_dec.
Defined.

Require Import Omega.
Lemma pltppq : forall p q, (0 <= q -> p <= p + q)%Z.
Proof.
  intros. omega.
Qed.

Lemma Zneglt0 : forall p, (Z.neg p < 0)%Z.
Proof.
  intros. unfold Zlt. simpl. reflexivity.
Qed.

Lemma ltneqgt : forall p q, (p < q -> p > q -> False)%Z.
Proof.
  intros. omega.
Qed.

Lemma exneggt0 : forall p, (Z.neg p > 0)%Z -> False.
Proof.
  intros. apply (ltneqgt (Z.neg p) 0%Z).
  apply Zneglt0.
  assumption.
Qed.

Lemma prodsgn : forall n m, (0 < n -> 0 < n * m -> 0 < m)%Z.
Proof.
  destruct n, m; auto; try omega.
  intros. elim (exneggt0 p). omega.
Qed.

Lemma ltadd : forall p q, (p <= p + q <-> 0 <= q)%Z.
Proof.
  intros. omega.
Qed.

Lemma prodSn : forall n m, (0 < n -> 0 < m -> n <= n * m)%Z.
Proof.
  intros. destruct n, m;
          auto;
          try omega;
          try solve [ elim (exneggt0 p0); omega ];
          try solve [ elim (exneggt0 p); omega ].
  clear.
  destruct p0 using Pos.peano_ind; [ omega | clear IHp0 ].
  assert (Z.pos (Pos.succ p0) = 1 + Z.pos p0)%Z.
    simpl. destruct p0; auto.
  rewrite H. clear H. rewrite Zmult_plus_distr_r.
  rewrite Zmult_comm. assert (forall z, (1 * z = z)%Z); [ intros; omega | ].
  rewrite H. clear H.
  rewrite ltadd. simpl. unfold Zle. simpl. intro. discriminate.
Qed.

Lemma itenat2Z :
  forall A n m (tv fv : A),
    (if eq_nat_dec n m then tv else fv) = (if Z.eq_dec (Z.of_nat n) (Z.of_nat m) then tv else fv).
Proof.
  intros. destruct eq_nat_dec.
  subst. destruct Z.eq_dec. reflexivity. elim n. reflexivity.
  destruct Z.eq_dec; [ | reflexivity ].
  elim n0. omega.
Qed.

Lemma OeqOZ : Z.of_nat 0 = 0%Z. simpl. reflexivity. Qed.

Lemma divides_lt : forall m n, n <> 0 -> m <> 0 -> n mod m = 0 -> m <= n.
Proof.
  intros m n nnz mneq0 mdiv.
  destruct (Nat.div_exact n m mneq0) as [ _ mdivthenndivexact ].
  assert (divexact := mdivthenndivexact mdiv). clear mdivthenndivexact.
  assert (smallthen0 := Nat.div_small n m).
  destruct (lt_dec n m) as [ small | notsmall ].
  rewrite (smallthen0 small) in divexact. elim nnz. rewrite divexact. rewrite mult_comm. simpl. reflexivity.
  revert notsmall. clear. intros. omega.
Qed.

Lemma gtnotdivides' : forall n m, n <> 0 -> n < m -> (forall x, m <= x -> n mod x <> 0).
Proof.
  intros n m nnz nltm x mlex.
  assert (m <> 0) as mnz. omega.
  assert (n < x) as nltx. omega.
  assert (x <> 0) as xnz. omega.
  rewrite <- (Nat.mod_small_iff _ _ xnz) in nltx.
  rewrite nltx. assumption.  
Qed.

Lemma gtnotdivides : forall n m, n <> 0 -> n < m -> n mod m <> 0.
Proof.
  intros.
  apply (gtnotdivides' n m H H0 m). constructor.
Qed.

Fixpoint conformants''x {P : nat -> Prop} (dec : forall n, {P n}+{~P n}) nn : list nat :=
  match nn with
    | O => nil
    | S nn' => let l' := conformants''x dec nn'
               in if dec nn'
                  then nn'::l'
                  else l'
  end.

Lemma conformants'
         {P : nat -> Prop}
         (dec : forall n, {P n}+{~P n})
         (nn : nat)
: confprops'' (conformants''x dec nn) P nn.

Proof.
  unfold confprops''. induction nn.
  - simpl. split; [ | split; [ | split ] ]; auto. intros. omega.
  - destruct IHnn as [ set [ ltx [ conf meat ] ] ]. split; [ | split; [ | split ] ]; simpl; remember (conformants''x dec nn) as l'; clear Heql'.
    + destruct (dec nn); [ | assumption ].
      simpl. rewrite set. destruct (inb eq_nat_dec nn _) eqn:inbeq; [ | reflexivity ].
      exfalso. revert inbeq ltx dec. clear. intros.
      apply forallneqthennotin with (A := nat) (dec:=eq_nat_dec) (l:=l') (a:=nn).
      * apply PthenQthenFAPthenFAQ with (P := fun x => x < nn).
        clear. intros. omega.
        assumption.
      * assumption.
    + destruct (dec nn);
      [ constructor; [ omega | ] | ];
        apply PthenQthenFAPthenFAQ with (P:=fun x => x < nn);
        try solve [ intros; omega ]; assumption.
    + destruct (dec nn); [ | assumption ].
      constructor; assumption.
    + intros. destruct (dec nn).
      * destruct (eq_nat_dec nn n). left. assumption.
        right. apply meat. omega. assumption.
      * destruct (eq_nat_dec nn n). elim n0. rewrite e. assumption.
        apply meat. omega. assumption.
Qed.

Definition divisors_raw {n} (nnz : n <> 0) := conformants''x (divides_dec n) (S n).

Lemma divisorspf :
  forall {n} (nnz : n <> 0),
    confprops (divisors_raw nnz) (fun x => n mod x = 0).
Proof.
  unfold confprops.
  intros n nnz.
  unfold divisors_raw.
  assert (gtnd := fun m => gtnotdivides _ m nnz). unfold lt in gtnd.
  assert (Hx := @conformants' _ (divides_dec n) (S n)).
  assert (Hy := @conformants _ _ gtnd _ Hx).
  unfold confprops in Hy.
  destruct Hy as [ set [ ldiv divIn ] ].
  split; [ assumption | ].
  apply confiff. assumption. assumption.
Qed.

Lemma nsq : forall n, (S n) * (S n) = n*n + 2*n + 1.
Proof.
  intros. ring.
Qed.

Lemma nsqsub : forall n, (S n)*(S n) - n*n = 2*n + 1.
Proof.
  intros. rewrite nsq. omega.
Qed.

Lemma div_modnz : forall n k, n <> 0 -> k <> 0 -> n mod k = 0 -> n / k <> 0.
Proof.
  intros n k nnz knz kdivn.
  rewrite <- (Nat.div_exact n k knz) in kdivn.
  destruct (n / k). rewrite mult_comm in kdivn. simpl in kdivn. subst. assumption.
  intro. discriminate.
Qed.

Lemma deqndndd : forall n d, n <> 0 -> n mod d = 0 -> d = n / (n / d).
Proof.
  intros n d nnz ddiv.
  destruct (eq_nat_dec d 0) as [ dz | dnz ]. subst. simpl. reflexivity.
  rewrite <- (Nat.div_exact n d dnz) in ddiv.
  rewrite ddiv at 1.
  rewrite Nat.div_mul. reflexivity.
  apply div_modnz; [ assumption | assumption | ].
  rewrite <- Nat.div_exact; assumption.
Qed.

Lemma deneqden :
  forall n d1 d2,
    n <> 0 ->
    d1 <> 0 ->
    n mod d1 = 0 ->
    d2 <> 0 ->
    n mod d2 = 0 -> 
    n / d1 = n / d2 ->
    d1 = d2.
Proof.
  intros n d1 d2 nnz d1nz d1d d2nz d2d deq.
  assert (n / d2 <> 0) as ndd2nz.
    apply (div_modnz _ _ nnz d2nz d2d).
  assert (dm1 := div_mod n d1 d1nz).
  assert (dm2 := div_mod n d2 d2nz).
  rewrite dm2 in dm1 at 1. clear dm2.
  rewrite deq in dm1. clear deq.
  rewrite d1d in dm1. rewrite d2d in dm1. clear d1d d2d.
  rewrite plus_comm in dm1. simpl in dm1. rewrite plus_comm in dm1. simpl in dm1.
  rewrite mult_comm in dm1. rewrite (mult_comm d1) in dm1.
  rewrite Nat.mul_cancel_l in dm1.
  rewrite dm1. reflexivity.
  assumption.
Qed.

Lemma divisorpair : forall n k, n mod k = 0 -> n mod (n / k) = 0.
Proof.
  intros n k kdiv.
  destruct (eq_nat_dec n 0) as [ nz | nnz ]. subst.
    destruct k. simpl. reflexivity. simpl. reflexivity.
  destruct (eq_nat_dec k 0) as [ kz | knz ]. subst. simpl. reflexivity.
  assert (ndivkexact := Nat.div_exact n k knz).
  assert (ndknz := div_modnz n k nnz knz kdiv).
  rewrite <- Nat.div_exact; [ | assumption ]. rewrite mult_comm.
  rewrite <- deqndndd; try assumption.
  rewrite ndivkexact; assumption.
Qed.

Lemma nfsq : forall n k, k <> 0 -> n mod k = 0 -> k = n / k -> n = k * k.
Proof.
  intros n k knz kdiv keqndk. rewrite <- (Nat.div_exact n k knz) in kdiv.
  rewrite <- keqndk in kdiv. assumption.
Qed.

Lemma fsqn : forall n k, n = k * k -> k = n / k.
Proof.
  intros n k neqkk.
  destruct (eq_nat_dec k 0).
  subst. simpl. reflexivity.
  rewrite neqkk. rewrite Nat.div_mul. reflexivity.
  assumption.
Qed.

Lemma fsqd : forall n k, n = k * k -> n mod k = 0.
Proof.
  intros. rewrite H. 
  destruct (eq_nat_dec k 0).
  subst. simpl. reflexivity.
  apply Nat.mod_mul. assumption.
Qed.

Lemma sqiff : forall n k, k <> 0 -> ((n mod k = 0 /\ n mod (n / k) = 0 /\ k = n / k) <-> n = k * k).
Proof with auto.
  intros n k knz.
  split; [ intros [ kdiv [ ndkdiv keqndk ] ] | intro nsq ].
  - apply nfsq...
  - split; [ | split; [ apply divisorpair | apply fsqn ] ]; auto; apply fsqd...    
Qed.

Lemma sqrtuniq : forall n k l, n = k * k -> n = l * l -> k = l.
Proof.
  intros n k l ksq lsq. intros.
  rewrite <- Nat.sqrt_square with l.
  rewrite <- Nat.sqrt_square with k.
  rewrite <- ksq. rewrite <- lsq.
  reflexivity.
Qed.

Lemma divy : forall n k l, n = k * l -> n mod k = 0 /\ n mod l = 0.
Proof.
  intros.
  destruct (eq_nat_dec k 0) as [ kz | knz ]. subst. simpl. split; auto. destruct l; auto. simpl. rewrite minus_diag. reflexivity.
  destruct (eq_nat_dec l 0) as [ lz | lnz ]. subst. simpl. split; auto. rewrite mult_comm. simpl. destruct k; auto. simpl. rewrite minus_diag. reflexivity.
  assert (Hk := Nat.mod_mul l k knz).
  assert (Hl := Nat.mod_mul k l lnz).
  rewrite mult_comm in Hk.
  rewrite <- H in *. split; assumption.
Qed.

Lemma divdiv :
  forall n k m (knz : k <> 0) (nnz : n <> 0),
    k mod m = 0 ->
    n mod k = 0 -> 
    n mod m = 0.
Proof.
  intros n k m knz nnz mdivk kdivn.
  destruct (eq_nat_dec m 0) as [ mz | mnz ].
    subst. simpl. reflexivity.
  rewrite <- (Nat.div_exact _ _ mnz) in mdivk.
  rewrite <- (Nat.div_exact _ _ knz) in kdivn.
  rewrite mdivk in kdivn.
  rewrite kdivn. rewrite <- mult_assoc. rewrite mult_comm.
  apply Nat.mod_mul. assumption.
Qed.

Lemma divsdivs :
  forall n k (knz : k <> 0) (nnz : n <> 0),
    n mod k = 0 ->
    incl (divisors_raw knz) (divisors_raw nnz).
Proof.
  intros n k knz nnz kdiv.
  destruct (divisorspf knz) as [ _ kdivpf ].
  destruct (divisorspf nnz) as [ _ ndivpf ].
  unfold incl. rewrite <- Forall_forall.
  apply FAfe with (fun x => n mod x = 0). intros. rewrite <- ndivpf. assumption.
  assert (Forall (fun x => k mod x = 0) (divisors_raw knz)) as famodin.
    rewrite Forall_forall. intros. rewrite kdivpf. assumption.
  apply PthenQthenFAPthenFAQ with (fun x => k mod x = 0); auto.
  intros. apply divdiv with k; auto.
Qed.

Lemma divlcontainsn :
  forall n (nnz : n <> 0),
    let l := divisors_raw nnz in
    (In 0 l /\ In 1 l /\ In n l).
Proof.
  intros.
  destruct (divisorspf nnz) as [ _ iff ].
  unfold l.
  split; [ | split ]; rewrite <- iff; auto.
  apply Nat.mod_same. assumption.
Qed.

Lemma sqz :
  forall n,
    sqrt n = 0 <-> n = 0.
Proof.
  intros.
  split; intro.
  - destruct n; auto.
    destruct n; auto.
    assert (Hx := Nat.sqrt_le_mono 1 (S (S n))).
    assert (1 <= S (S n)); [ omega | ].
    assert (Hy := Hx H0). rewrite H in Hy. 
    rewrite Nat.sqrt_1 in Hy.
    omega.
  - rewrite H.
    rewrite Nat.sqrt_0. reflexivity.
Qed.

Lemma sqval :
  forall n,
    sqrt n <= n / sqrt n.
Proof.
  intros.
  destruct (eq_nat_dec n 0). simpl. subst. rewrite Nat.sqrt_0. auto.
  assert (sqrt n <> 0). intro. rewrite sqz in H. subst. elim n0. reflexivity.
  destruct (sqrt_spec n); [ omega | ]. unfold lt in *.
  assert (Hx :=  Nat.div_le_lower_bound _ _ _ H H0). assumption.
Qed.

Lemma sq_exact :
  forall n,
    n mod (sqrt n) = 0 ->
    sqrt n <= n / sqrt n <= 2 + sqrt n.
Proof.
  intros n sqdiv.
  destruct (eq_nat_dec n 0). subst. rewrite Nat.sqrt_0. split. simpl. constructor. simpl. repeat constructor.
  assert (sqrt n <> 0). rewrite sqz. assumption.
  assert (ndsqdiv := divisorpair _ _ sqdiv).
  assert (Hx := sqval n).
  assert (Hy := Nat.div_exact n (sqrt n) H).
  assert (n / sqrt n <> 0). apply div_modnz; auto.
  assert (Hz := Nat.div_exact n (n / sqrt n) H0).
  generalize sqdiv. intro neqsq. rewrite <- Hy in neqsq. clear Hy.
  generalize ndsqdiv. intro neqnsq. rewrite <- Hz in neqnsq. clear Hz.
  destruct (sqrt_spec n); [ omega | ]. unfold lt in H2. simpl in H2.
  assert (n <= sqrt n + sqrt n * S (sqrt n)). omega. clear H2.
  assert (sqrt n <= n / sqrt n <= 2 + sqrt n). split. 
    assumption. assert (Hxx := Nat.div_le_mono n (sqrt n + sqrt n * S (sqrt n)) _ H H3).
    assert (sqrt n + sqrt n * S (sqrt n) = sqrt n * (2 + (sqrt n))).
      assert (2 + sqrt n = 1 + S (sqrt n)). omega. rewrite H2. rewrite mult_plus_distr_l.
      rewrite (mult_comm _ 1). simpl. rewrite (plus_comm _ 0). simpl. reflexivity.
      rewrite H2 in Hxx. rewrite mult_comm in Hxx. rewrite Nat.div_mul in Hxx; auto.
  assumption.
Qed.

Lemma sqrt_corr :
  forall n k,
    n = k * k ->
    k = sqrt n.
Proof.
  intros.
  assert (hh := Nat.sqrt_square k). rewrite <- H in *. rewrite hh. reflexivity.
Qed.

Lemma sqrt_corr_sq :
  forall n,
    n <> sqrt n * sqrt n -> (forall k, n <> k * k).
Proof.
  intros. intro.
  elim H. clear H.
  assert (sqrt n = sqrt (k * k)). rewrite H0. reflexivity.
  rewrite H. rewrite Nat.sqrt_square. assumption.
Qed.

Lemma perfect_root_dec :
  forall n,
    {k | n = k * k}+{forall k, n <> k * k}.
Proof.
  intros.
  destruct (eq_nat_dec n (sqrt n * sqrt n)).
  - left. exists (sqrt n). assumption.
  - right. apply sqrt_corr_sq. assumption.
Defined.

Lemma not_square_then_m_neq_ndm :
  forall n,
    (forall k, n <> k * k) ->
    (forall m,
       m <> 0 ->
       n mod m = 0 ->
       m <> n / m).
Proof.
  intros n nsq m mnz mdiv.
  intro meqndm.
  assert (Hx := nfsq n _ mnz mdiv meqndm).
  elim (nsq m).
  assumption.
Qed.

Lemma meqndmsq :
  forall n m,
    m <> 0 ->
    n mod m = 0 ->
    m = n / m ->
    m = (sqrt n).
Proof.
  intros n m mnz mdiv meqndm.
  assert (Hx := nfsq _ _ mnz mdiv meqndm).
  assert (Hy := sqrt_corr _ _ Hx).
  assumption.
Qed.

Definition divisors_nz {n} (nnz : n <> 0) := remove eq_nat_dec 0 (divisors_raw nnz).
Definition divisors_nsr {n} (nnz : n <> 0) := let nzd := divisors_nz nnz in
                                              if eq_nat_dec n (sqrt n * sqrt n)
                                              then remove eq_nat_dec (sqrt n) nzd
                                              else nzd.

Lemma divisors_nz_nz :
  forall n (nnz : n <> 0) a,
    In a (divisors_nz nnz) -> a <> 0.
Proof.
  intros. intro. unfold divisors_nz in H.
  rewrite H0 in H.
  ainral.
Qed.

Lemma divisors_nsr_nz :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> a <> 0.
Proof.
  intros. intro. unfold divisors_nsr in H. unfold divisors_nz in H.
  rewrite H0 in H.
  destruct (eq_nat_dec n _); [ | ainral ].
  rewrite remove_assoc in H. ainral.
Qed.

Lemma divisors_nz_ainndain :
  forall n (nnz : n <> 0) a,
    In a (divisors_nz nnz) -> In (n / a) (divisors_nz nnz).
Proof.
  intros n nnz0 a pf.
  destruct (divisorspf nnz0) as [ lzset indiv ].
  assert (anz := divisors_nz_nz _ nnz0 _ pf).
  unfold divisors_nz in *.
  ainrbl.
  generalize pf; intro. rewrite <- indiv in pf0.
  assert (Hx := divisorpair _ _ pf0).
  assert (Hy := div_modnz _ _ nnz0 anz pf0).
  rewrite indiv in Hx. rewrite <- remove_corr_neq; [ | neqneq ].
  assumption.
Qed.

Lemma divisors_nsr_ainndain :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> In (n / a) (divisors_nsr nnz).
Proof.
  intros n nnz0 a pf.
  destruct (divisorspf nnz0) as [ lzset indiv ].
  assert (anz := divisors_nsr_nz _ nnz0 _ pf).
  unfold divisors_nsr in *. unfold divisors_nz in *.
  destruct (eq_nat_dec n (sqrt n * sqrt n)) as [ nsq' | nnsq' ].
  - rewrite remove_assoc in pf. ainrbl.
    destruct (eq_nat_dec (sqrt n) a) as [ xeqa | xnea ].
    + rewrite xeqa in *. ainral.
    + assert (anex := neqflip _ _ _ xnea). ainrbl.
      generalize pf; intro. rewrite <- indiv in pf0.
      assert (ndad := divisorpair _ _ pf0). rewrite indiv in ndad.
      assert (ndanz := div_modnz _ _ nnz0 anz pf0).
      rewrite remove_assoc. rewrite <- remove_corr_neq; [ | neqneq ].
      destruct (eq_nat_dec (sqrt n) (n / a)); [ | rewrite <- remove_corr_neq; assumption ].
      rewrite (fsqn _ _ nsq') in e.
      rewrite (deneqden _ _ (sqrt n) nnz0 anz pf0) in xnea.
      * elim xnea. reflexivity.
      * intro srz. rewrite srz in nsq'. simpl in nsq'. elim nnz0. assumption.
      * apply fsqd. assumption.
      * rewrite e. reflexivity.
  - apply divisors_nz_ainndain. assumption.
Qed.

Lemma divisors_nz_ainadiv :
  forall n (nnz : n <> 0) a,
    In a (divisors_nz nnz) -> n mod a = 0.
Proof.
    intros n nnz a ainl.
    assert (anz := divisors_nz_nz _ nnz _ ainl).
    destruct (divisorspf nnz) as [ lzset indiv ].
    unfold divisors_nz in ainl.
    rewrite indiv.
    ainrbl. assumption.
Qed.

Lemma divisors_nsr_ainadiv :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> n mod a = 0.
Proof.
    intros n nnz a ainl.
    assert (anz := divisors_nsr_nz _ nnz _ ainl).
    destruct (divisorspf nnz) as [ lzset indiv ].
    unfold divisors_nsr in ainl. unfold divisors_nz in ainl.
    rewrite indiv.
    destruct (eq_nat_dec n (sqrt n * sqrt n)) as [ nsq | nnsq ].
    - destruct (eq_nat_dec a (sqrt n)) as [ asr | nasr ].
      + rewrite <- asr in ainl. ainral.
      + ainrbl. ainrbl. assumption.
    - ainrbl. assumption.
Qed.

Lemma divisors_nsr_is_set :
  forall n (nnz : n <> 0),
    is_set eq_nat_dec (divisors_nsr nnz) = true.
Proof.
  intros.
  destruct (divisorspf nnz) as [ lzset _ ].
  unfold divisors_nsr. unfold divisors_nz.
  destruct eq_nat_dec; repeat apply setrm; assumption.
Qed.

Lemma divisorcount :
  forall n (nnz : n <> 0) l,
    l = divisors_nsr nnz ->
    Even (length l).

Proof.
  intros n nnz0 l leq.
  destruct (divisorspf nnz0) as [ lzset indiv ].

  assert (inpirr := UIP_inp _ eq_nat_dec _ (divisors_nsr_is_set _ nnz0)).
  rewrite <- leq in inpirr.

  assert (forall a, In a l -> a <> 0) as innz.
    rewrite leq. apply divisors_nsr_nz.

  assert (forall a (pf : In a l), In (n / a) l) as ainndain.
    rewrite leq. apply divisors_nsr_ainndain.

  assert (forall a, In a l -> n / a <> 0) as inndnz.
    intros. apply innz. apply ainndain. assumption.

  assert (forall a, In a l -> n mod a = 0) as inldiv.
   rewrite leq. apply (divisors_nsr_ainadiv).

  assert (Hx := redundant_list _ l). destruct Hx as [ x e ].
  set (pair := fun x : {x | In x l} => n / (proj1_sig x)).

  assert (forall x, In (pair x) l) as pairin.
    intros x0. destruct x0 as [ xx xxinl ].
    unfold pair. simpl. apply ainndain.
    assumption.

  unfold divisors_nsr in leq. unfold divisors_nz in leq.
  assert ({f : {x | In x l} -> {x | In x l} | forall a, a <> f a /\ a = f (f a) /\ (In a x -> In (f a) x)}) as pairsig.
  unshelve refine (exist _ (fun x => exist _ (pair x) (*pairin*)_) _); [ auto | ]. intro. split; [ | split ].
  - unfold pair. destruct a. unfold proj1_sig in *.
    assert (anz := innz _ i). assert (ndanz := inndnz _ i). assert (adiv := inldiv _ i). assert (ndadiv := divisorpair _ _ adiv).
    destruct (eq_nat_dec x0 (n / x0)) as [ x0eqndx0 | x0nendx0 ].
    + exfalso.
      assert (nsq := nfsq _ _ anz adiv x0eqndx0).
      assert (x0eqsr := meqndmsq _ _ anz adiv x0eqndx0). rewrite x0eqsr in *.
      rewrite leq in i. revert i nsq. clear.
      intros. destruct eq_nat_dec. ainral.
      elim n0. assumption.
    + apply nesigne. simpl. assumption.

  - unfold pair. simpl. destruct a. simpl.
    apply eqsigeq; [ auto | ]. simpl.
    apply deqndndd.
    assumption.
    apply inldiv. assumption.

  - intros. unfold pair.
    destruct a. simpl.
    assert (j := ainndain _ i).
    apply inlinsigl; auto.
    rewrite e. assumption.
    
  - destruct pairsig as [ pair' pairpairs ].
    assert (forall a b : {x|In x l}, {a=b}+{a<>b}) as eq_signat_dec.
      intros. destruct a, b. destruct (eq_nat_dec x0 x1).
        left. revert e0 inpirr. clear. intros. subst. apply eqsigeq; auto.
        right. apply nesigne. assumption.
    assert (forall a, a <> pair' a) as pnid. intro. destruct (pairpairs a) as [ ni _ ]. assumption.
    assert (forall a, a = pair' (pair' a)) as pinv. intro. destruct (pairpairs a) as [ _ [ pinv _ ] ]. assumption.
    assert (forall a, In a x -> In (pair' a) x) as ainpain. intro. destruct (pairpairs a) as [ _ [ _ inin ] ]. assumption.
    assert (pinv' := if_involutive _ _ pinv).
    assert (iftheneven := paired_even' ({x|In x l}) eq_signat_dec pair' pnid pinv' x).
    rewrite <- e at 1. rewrite map_length.
    apply iftheneven. split.

    + assert (is_set eq_nat_dec l = true) as lset. rewrite leq. destruct (eq_nat_dec n (sqrt n * sqrt n)); repeat apply setrm; assumption.
      rewrite <- e in lset. revert lset inpirr. clear. intros lset inpirr. remember (proj1_sig (P:=fun x : nat => In x l)) as y.
      induction x. simpl. reflexivity.
      simpl in *.
      destruct (inb _ _ (map y x)) eqn:x0inl. discriminate.
      rewrite (IHx lset). clear lset IHx.
      destruct (inb _ _ x) eqn:x0inx; auto.
      rewrite <- x0inl. rewrite <- x0inx.
      revert Heqy inpirr. clear. intros. induction x. simpl. reflexivity.
      simpl. rewrite IHx. clear IHx.
      destruct a, a0. rewrite Heqy. simpl.
      destruct (eq_nat_dec x0 x1).
        subst. assert (Hx := inbeqIn _ eq_nat_dec x1 l). rewrite (inpirr x1 i0 i). destruct (eq_signat_dec _ _); [ reflexivity | ].
        elim n. reflexivity.
      destruct (eq_signat_dec _ _); [ | reflexivity ].
      assert (x0inx := nesigne _ _ (exist (fun x : nat => In x l) x0 i) (exist _ x1 i0) n).
      simpl in x0inx. elim x0inx. assumption.

    + unfold paired_list. intros a ainx.
      apply ainpain. assumption.
Grab Existential Variables.
Qed.

Definition issq n := exists k, n = k * k.

Lemma issq_dec :
  forall n, {issq n}+{~issq n}.
Proof.
  intros. destruct (perfect_root_dec n).
  - left. unfold issq. destruct s. exists x. assumption.
  - right. intro. unfold issq in H. destruct H. elim (n0 x). assumption.
Qed.

Lemma nlesqn :
  forall n, n <= n * n.
Proof.
  induction n. simpl. constructor.
  simpl. rewrite mult_comm. simpl. remember (n*n). clear Heqn0. omega.
Qed.

Lemma nltsqn :
  forall n, 1 < n -> n < n * n.
Proof.
  induction n. simpl. intros. omega.
  intros. destruct (eq_nat_dec 1 n).
  - subst. simpl. omega.
  - assert (1 < n). omega.
    assert (Hx := IHn H0).
    simpl. rewrite mult_comm. simpl. omega.
Qed.

Lemma sqmon_left :
  forall n m, n < m -> n * n < m * m.
Proof.
  induction n. simpl. intros. destruct m. omega. simpl. remember (m * _). omega.
  intros. simpl. rewrite mult_comm. simpl. destruct m. exfalso. omega.
  assert (n < m). omega.
  assert (Hx := IHn _ H0). simpl. rewrite (mult_comm m _). simpl. remember (n*n). remember (m*m).
  omega.
Qed.

Lemma sqmon_right :
  forall n m, n * n < m * m -> n < m.
Proof.
  intros.
  assert (Hx := Nat.sqrt_le_mono (n*n) (m*m)).
  repeat rewrite Nat.sqrt_square in Hx.
  destruct (eq_nat_dec n m). subst. exfalso. clear Hx. omega.
  assert (n * n <= m * m). omega.
  assert (Hy := Hx H0). omega.
Qed.

Lemma apbsq :
  forall a b, (a + b) * (a + b) = a*a + 2*a*b + b*b.
Proof.
  induction a. simpl. reflexivity.
  intros. simpl. apply f_equal. repeat rewrite <- plus_assoc. apply f_equal2. reflexivity.
  rewrite (plus_comm _ 0). simpl. rewrite mult_comm. simpl. rewrite IHa. clear IHa.
  repeat rewrite (mult_comm _ (S _)). simpl.
  repeat rewrite (plus_comm _ (S a)). simpl.
  rewrite (plus_comm _ 0). simpl. omega.
Qed.

Lemma sqdiff :
  forall n m, n * n < m * m -> m * m = n * n + 2 * n * (m - n) + (m - n) * (m - n).
Proof.
  intros.
  assert (Hx := sqmon_right _ _ H).
  assert (m = n + (m - n)). omega.
  rewrite H0 in *.
  remember (m - n). clear.
  assert (Hx := apbsq n n0).
  rewrite Hx. assert (forall a b, a + b - a = b). clear. intros. omega.
  rewrite H. reflexivity.
Qed.

Lemma sqrtmid :
  forall x n, n * n < x < (S n) * (S n) -> ~issq x.
Proof.
  intros. intro. unfold issq in H0. destruct H0. destruct H.
  subst.
  assert (Hxx := sqmon_right _ _ H). clear H.
  assert (Hyy := sqmon_right _ _ H1). clear H1.
  omega.
Qed.

Lemma sqSnsq :
  forall n, n <> 0 -> issq n -> ~issq (S n).
Proof.
  intros n nnz nsq. intro Snnsq. unfold issq in *. destruct nsq as [ sqn nsq ], Snnsq as [ sqSn Snnsq ].
  assert (sqn * sqn < sqSn * sqSn) as xsqltx0sq. omega.
  assert (sqltsqS := sqmon_right _ _ xsqltx0sq).
  assert (sqSn = sqn + (sqSn - sqn)) as sqSn'eq. omega.
  rewrite sqSn'eq in *. remember (sqSn - sqn) as sqSn'. clear sqSn sqSn'eq HeqsqSn'.
  rewrite apbsq in Snnsq. rewrite nsq in Snnsq.
  assert (sqn <> 0) as sqnnz. intro sqnz. rewrite sqnz in nsq. simpl in nsq. elim nnz. assumption.
  assert (S (sqn * sqn) = sqn * sqn + 1) as Ssqnsq. omega.
  rewrite Ssqnsq in Snnsq. revert Snnsq sqnnz. clear. intros.
  rewrite <- plus_assoc in Snnsq.
  rewrite Nat.add_cancel_l in Snnsq.
  destruct sqSn'. rewrite mult_comm in Snnsq. simpl in Snnsq. discriminate.
  rewrite plus_comm in Snnsq.
  destruct sqn. elim sqnnz. reflexivity.
  clear sqnnz.
  simpl in Snnsq. rewrite plus_comm in Snnsq. simpl in Snnsq. discriminate.
Qed.

Lemma nextsq :
  forall n,
    issq n ->
    (forall k,
       0 < k <= 2 * (sqrt n) ->
       ~issq (n + k)).
Proof.
  intros n nsq k klims nsqnk. destruct nsqnk as [ sr' nsqnk ].
  destruct nsq as [ srn nsq ].
  assert (Hx := Nat.sqrt_square srn). rewrite nsq in *. rewrite Hx in *. clear Hx nsq.
  assert (Hx := sqrtmid (srn * srn + k) srn).
  assert (srn * srn < srn * srn + k < S srn * S srn).
    simpl. rewrite (mult_comm _ (S _)). simpl.
    simpl in klims. rewrite (plus_comm _ 0) in klims. simpl in klims.
    remember (srn * srn). revert klims. clear. intros. omega.
  assert (Hy := Hx H). clear Hx H. elim Hy. exists sr'. assumption.
Qed.

Lemma divisorparity_nsq :
  forall n (nnz : n <> 0),
    ~issq n ->
    Even (length (divisors_nz nnz)).
Proof.
  intros n nnz nnsq.
  assert (evenall := divisorcount _ nnz (divisors_nsr nnz)).
  unfold divisors_nsr in evenall.
  destruct (eq_nat_dec _ _).
  - elim nnsq. unfold issq. exists (sqrt n). assumption.
  - apply evenall. reflexivity.
Qed.

Lemma divisorparity_sq :
  forall n (nnz : n <> 0),
    issq n ->
    ~Even (length (divisors_nz nnz)).
Proof.
  intros n nnz nnsq. intro nzev.
  assert (evenall := divisorcount _ nnz (divisors_nsr nnz)).
  unfold divisors_nsr in evenall.
  destruct (eq_nat_dec _ _).
  - destruct (divisorspf nnz) as [ lzset indiv ].
    assert (In (sqrt n) (divisors_nz nnz)).
      unfold divisors_nz in *.
      assert (srdiv := fsqd _ _ e).
      assert (srin := fsqd _ _ e). rewrite indiv in srin.
      assert (sqrt n <> 0) as srnz. rewrite sqz. assumption.
      rewrite <- remove_corr_neq. assumption. neqneq.
    assert (lset := setrm _ _ _ lzset 0).
    assert (Hx := lrm _ eq_nat_dec _ lset (sqrt n) H).
    unfold divisors_nz in *.
    rewrite Hx in nzev. clear Hx.
    remember (length (remove _ _ _)). revert nzev evenall. clear. intros.
    induction n0; firstorder.
    
  - elim n0. unfold issq in nnsq. destruct nnsq.
    assert (Hx := sqrt_corr _ _ H).
    rewrite Hx in H. assumption.
Qed.

Lemma sqne :
  forall n (nnz : n <> 0),
    issq n <-> ~Even (length (divisors_nz nnz)).
Proof.
  intros.
  assert (Hx := iffif {x | x <> 0} (fun nnz => issq (proj1_sig nnz)) (fun nnz => Even (length (divisors_nz (proj2_sig nnz))))). simpl in *.

  set (x := exist (fun x => x <> 0) n nnz).
  assert ((forall a : {x | x <> 0}, {issq (proj1_sig a)} + {~ issq (proj1_sig a)})) as issq_dec_sig.
    clear Hx. intros. destruct a. simpl. apply issq_dec.
  assert (Hy := Hx issq_dec_sig). clear Hx issq_dec_sig.

  assert (forall a : {x | x <> 0}, {Even (length (divisors_nz (proj2_sig a)))} + {~ Even (length (divisors_nz (proj2_sig a)))}) as evendec.
    clear.
    intros. destruct a. simpl.
    remember (length _). clear.
    assert (Hx := Nat.even_spec).
    destruct (even n0) eqn:n0ev.
      left. rewrite Hx in n0ev. assumption.
      right. intro. rewrite <- Hx in H. rewrite H in n0ev. discriminate n0ev.
  assert (Hx := Hy evendec). clear Hy evendec.

  assert (forall a : {x | x <> 0}, issq (proj1_sig a) -> ~ Even (length (divisors_nz (proj2_sig a)))) as divisorparity_sq'.
    intros. destruct a. simpl in *. apply divisorparity_sq; assumption.
  assert (Hy := Hx divisorparity_sq'). clear Hx divisorparity_sq'.

  assert (forall a : {x | x <> 0}, ~ issq (proj1_sig a) -> Even (length (divisors_nz (proj2_sig a)))) as divisorparity_nsq'.
    intros. apply divisorparity_nsq; assumption.
  assert (Hx := Hy divisorparity_nsq' x). clear Hy divisorparity_nsq'.
  
  unfold x in Hx. simpl in Hx. assumption.
Qed.

Lemma add_lt_mul :
  forall a, 2 < a -> a + a < a * a.
Proof.
  intros.
  assert (1 < a). omega.
  assert (Hx := Nat.add_le_mul a a H0 H0). clear H0.
  destruct (eq_nat_dec (a + a) (a * a)); [ | omega ].
  rewrite e in *.
  revert H e Hx. induction a using (nat_interval_ind 3).
  - intros. destruct a; [ omega | ]. destruct a; [ omega | ]. destruct a; omega.
  - intros. destruct a; [ omega | ]. destruct a; [ omega | ]. destruct a; try omega.
    exfalso. revert e. clear. intros.
    simpl in *. injection e. clear e. intro e.
    rewrite Nat.add_cancel_l in e. injection e. clear e. intro e.
    assert (a = a + 0). rewrite plus_comm. simpl. reflexivity.
    rewrite H in e at 1.
    rewrite Nat.add_cancel_l in e. discriminate.
Qed.
  
Lemma minsqdiff :
  forall a b,
    issq a ->
    issq b ->
    a < b ->
    a <> 0 ->
   2 * NPeano.Nat.sqrt b < S (S (b - a)).
Proof.
  intros.
  destruct H, H0.
  rewrite H, H0 in *.
  assert (Hx := sqdiff _ _ H1).
  rewrite NPeano.Nat.sqrt_square.
  rewrite Hx.
  assert (x * x + 2 * x * (x0 - x) + (x0 - x) * (x0 - x) - x * x = 2 * x * (x0 - x) + (x0 - x) * (x0 - x)). clear. simpl. repeat rewrite (plus_comm _ 0). simpl. rewrite <- plus_assoc. rewrite plus_comm.
  rewrite NPeano.Nat.add_sub. reflexivity.
  rewrite H3.
  assert (Hy := sqmon_right _ _ H1).
  assert (x0 = x + (x0 - x)). revert Hy. clear. intro. omega.
  rewrite H4 in *. remember (x0 - x). clear H4 x0 Heqn.
  assert (x + n - x = n). rewrite plus_comm. rewrite (NPeano.Nat.add_sub n x). reflexivity.
  rewrite H4.
  clear Hx H H0 H1 H3 H4 a b. destruct n. rewrite plus_comm in Hy. simpl in Hy. omega.
  rewrite plus_comm. unfold plus at 1. fold plus. clear Hy.
  simpl. repeat rewrite (plus_comm _ 0). simpl. repeat rewrite (mult_comm _ (S _)). simpl.
  rewrite plus_comm. simpl. rewrite (plus_comm _ (S (n + _))). simpl.
  assert (n + x + (n + x) < S (n + (n + n * n) + (x + x + n * (x + x)))).
  rewrite mult_plus_distr_l. remember (n * n). remember (n * x). omega.
  omega.
Defined.

Lemma xmodmeqk_Sxmodmeq0 :
  forall x m,
    S (x mod m) = m ->
    (S x) mod m = 0.
Proof.
  intros. destruct m. simpl. reflexivity.
  assert (S m <> 0) as mnz. intro. discriminate.
  assert (Hx := Nat.add_mod_idemp_l x 1 _ mnz).
  repeat rewrite (plus_comm _ 1) in Hx. unfold plus in Hx.
  assert (x mod (S m) = m). simpl in *. injection H. intro. assumption.
  rewrite H0 in *.
  rewrite <- Hx.
  rewrite Nat.mod_same; [ | assumption ].
  reflexivity.
Qed.

Lemma xmodmnem_SxmodmeqSxmodm :
  forall x m,
    m <> 0 ->
    S (x mod m) <> m ->
    (S x) mod m = S (x mod m).
Proof.
  intros.
  assert (Hx := Nat.add_mod_idemp_l x 1 _ H).
  repeat rewrite (plus_comm _ 1) in Hx. unfold plus in Hx.
  rewrite <- Hx.
  remember (x mod m).
  assert (n < m).
    assert (0 <= x). omega.
    assert (0 < m). omega.
    destruct (mod_bound_pos _ _ H1 H2). rewrite Heqn. assumption.
  assert (S n < m). omega.
  assert (Hz := Nat.mod_small _ _ H2). assumption.
Qed.

Lemma apbmodmeqb_amodmz :
  forall a b m, (a + b) mod m = b mod m -> a mod m = 0.
Proof.
  intros. destruct m. simpl. reflexivity.
  destruct m. simpl. reflexivity.
  assert (1 < S (S m)). omega. remember (S (S m)) as m'. clear m Heqm'. rename m' into m.
  rewrite Nat.add_mod in H; [ | omega ].
  assert (m <> 0); [ omega | ].
  assert (Hx := Nat.mod_upper_bound a _ H1).
  assert (Hy := Nat.mod_upper_bound b _ H1).
  remember (a mod m) as a'. clear a Heqa'. rename a' into a.
  remember (b mod m) as b'. clear b Heqb'. rename b' into b.

  assert (Ha := div_mod a _ H1).
  assert (Hb := div_mod b _ H1).
  assert (Hxx := div_mod (a + b) _ H1). rewrite H in Hxx.
  repeat rewrite (plus_comm _ b) in Hxx.
  assert (Hyy := plus_reg_l _ _ _ Hxx). clear Hxx. rewrite plus_comm in Hyy.
  destruct (eq_nat_dec ((a + b) / m) 0). rewrite e in Hyy. rewrite mult_comm in Hyy. simpl in Hyy. assumption.
  destruct (eq_nat_dec ((a + b) / m) 1). rewrite e in Hyy. rewrite mult_comm in Hyy. simpl in Hyy. rewrite plus_comm in Hyy. simpl in Hyy. rewrite Hyy in Hx. revert Hx. clear. intro. omega.
  assert ((a + b) < 2 * m). omega.
  rewrite mult_comm in H2.
  assert (Hxz := Nat.div_lt_upper_bound _ _ _ H1 H2). omega.
Qed.
