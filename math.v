Require Import Zdiv.
Require Import List.
Require Import Arith.
Require Import Zquot.
Require Import PeanoNat.
Import Nat.
Require Export ucp.
Require Export logic.
Require Export list_facts.
Require Import nodup_in_pi.

Inductive evenl A :=
| Enil : evenl A
| Econsc : A -> A -> evenl A -> evenl A.

Definition divides_dec n m : {n mod m = 0}+{n mod m <> 0}.
Proof.
  apply eq_nat_dec.
Defined.

Require Import Lia.
Lemma pltppq : forall p q, (0 <= q -> p <= p + q)%Z.
Proof.
  intros. lia.
Qed.

Lemma Zneglt0 : forall p, (Z.neg p < 0)%Z.
Proof.
  intros. unfold Z.lt. simpl. reflexivity.
Qed.

Lemma ltneqgt : forall p q, (p < q -> p > q -> False)%Z.
Proof.
  intros. lia.
Qed.

Lemma exneggt0 : forall p, (Z.neg p > 0)%Z -> False.
Proof.
  intros. apply (ltneqgt (Z.neg p) 0%Z).
  apply Zneglt0.
  assumption.
Qed.

Lemma prodsgn : forall n m, (0 < n -> 0 < n * m -> 0 < m)%Z.
Proof with lia.
  destruct n, m...
Qed.

Lemma ltadd : forall p q, (p <= p + q <-> 0 <= q)%Z.
Proof with lia.
  intros...
Qed.

Lemma prodSn : forall n m, (0 < n -> 0 < m -> n <= n * m)%Z.
Proof.
  intros. destruct n, m;
          auto;
          try lia;
          try solve [ elim (exneggt0 p0); lia ];
          try solve [ elim (exneggt0 p); lia ].
  clear.
  destruct p0 using Pos.peano_ind; [ lia | clear IHp0 ].
  assert (Z.pos (Pos.succ p0) = 1 + Z.pos p0)%Z.
    simpl. destruct p0; auto.
  rewrite H. clear H. rewrite Zmult_plus_distr_r.
  rewrite Zmult_comm. assert (forall z, (1 * z = z)%Z); [ intros; lia | ].
  rewrite H. clear H.
  rewrite ltadd. simpl. unfold Z.le. simpl. intro. discriminate.
Qed.

Lemma itenat2Z :
  forall A n m (tv fv : A),
    (if eq_nat_dec n m then tv else fv) = (if Z.eq_dec (Z.of_nat n) (Z.of_nat m) then tv else fv).
Proof.
  intros. destruct eq_nat_dec.
  subst. destruct Z.eq_dec. reflexivity. elim n. reflexivity.
  destruct Z.eq_dec; [ | reflexivity ].
  elim n0. lia.
Qed.

Lemma OeqOZ : Z.of_nat 0 = 0%Z. simpl. reflexivity. Qed.

Lemma divides_lt : forall m n, n <> 0 -> m <> 0 -> n mod m = 0 -> m <= n.
Proof.
  intros m n nnz mneq0 mdiv.
  destruct (Div0.div_exact n m) as [ _ mdivthenndivexact ].
  assert (divexact := mdivthenndivexact mdiv). clear mdivthenndivexact.
  assert (smallthen0 := Nat.div_small n m).
  destruct (lt_dec n m) as [ small | notsmall ].
  rewrite (smallthen0 small) in divexact. elim nnz. rewrite divexact. rewrite mul_comm. simpl. reflexivity.
  revert notsmall. clear. intros. lia.
Qed.

Lemma gtnotdivides' : forall n m, n <> 0 -> n < m -> (forall x, m <= x -> n mod x <> 0).
Proof.
  intros n m nnz nltm x mlex.
  assert (m <> 0) as mnz. lia.
  assert (n < x) as nltx. lia.
  assert (x <> 0) as xnz. lia.
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
  - simpl. split; [ | split; [ | split ] ]; [ constructor | constructor | constructor | ]. intros. lia.
  - destruct IHnn as [ set [ ltx [ conf meat ] ] ]. split; [ | split; [ | split ] ]; simpl; remember (conformants''x dec nn) as l'; clear Heql'.
    + destruct (dec nn); [ | assumption ].
      assert (~In nn l').
      {
        intro. clear meat conf p.
        apply (forallneqthennotin _ eq_nat_dec nn l').
        - refine (PthenQthenFAPthenFAQ _ _ _ _ _ ltx). intros. lia.
        - rewrite inbeqIn. assumption.
          }
      constructor; assumption.
    + destruct (dec nn);
      [ constructor; [ lia | ] | ];
        apply PthenQthenFAPthenFAQ with (P:=fun x => x < nn);
        try solve [ intros; lia ]; assumption.
    + destruct (dec nn); [ | assumption ].
      constructor; assumption.
    + intros. destruct (dec nn).
      * destruct (eq_nat_dec nn n). left. assumption.
        right. apply meat. lia. assumption.
      * destruct (eq_nat_dec nn n). elim n0. rewrite e. assumption.
        apply meat. lia. assumption.
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
  intros. rewrite nsq. lia.
Qed.

Lemma div_modnz : forall n k, n <> 0 -> k <> 0 -> n mod k = 0 -> n / k <> 0.
Proof.
  intros n k nnz knz kdivn.
  rewrite <- (Div0.div_exact n k) in kdivn.
  destruct (n / k). rewrite mul_comm in kdivn. simpl in kdivn. subst. assumption.
  intro. discriminate.
Qed.

Lemma deqndndd : forall n d, n <> 0 -> n mod d = 0 -> d = n / (n / d).
Proof.
  intros n d nnz ddiv.
  destruct (eq_nat_dec d 0) as [ dz | dnz ]. subst. simpl. reflexivity.
  rewrite <- (Div0.div_exact n d) in ddiv.
  rewrite ddiv at 1.
  rewrite Nat.div_mul. reflexivity.
  apply div_modnz; [ assumption | assumption | ].
  rewrite <- Div0.div_exact; assumption.
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
  rewrite add_comm in dm1. simpl in dm1. rewrite add_comm in dm1. simpl in dm1.
  rewrite mul_comm in dm1. rewrite (mul_comm d1) in dm1.
  rewrite Nat.mul_cancel_l in dm1.
  rewrite dm1. reflexivity.
  assumption.
Qed.

Lemma divisorpair : forall n k, n mod k = 0 -> n mod (n / k) = 0.
Proof.
  intros n k kdiv.
  destruct (eq_nat_dec n 0) as [ nz | nnz ].
  - subst. destruct k; reflexivity.
  - destruct (eq_nat_dec k 0) as [ kz | knz ].
    + subst. rewrite mod_0_r in kdiv. subst. simpl. reflexivity.
    + assert (ndivkexact := Div0.div_exact n k).
      assert (ndknz := div_modnz n k nnz knz kdiv).
      rewrite <- Div0.div_exact. rewrite mul_comm.
      rewrite <- deqndndd; try assumption.
      rewrite ndivkexact; assumption.
Qed.

Lemma nfsq : forall n k, k <> 0 -> n mod k = 0 -> k = n / k -> n = k * k.
Proof.
  intros n k knz kdiv keqndk. rewrite <- (Div0.div_exact n k) in kdiv.
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
  apply Div0.mod_mul.
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
  destruct (eq_nat_dec k 0) as [ kz | knz ]. subst. simpl. split; auto. destruct l; auto. simpl. rewrite sub_diag. reflexivity.
  destruct (eq_nat_dec l 0) as [ lz | lnz ]. subst. simpl. split; auto. rewrite mul_comm. simpl. destruct k; auto. simpl. rewrite sub_diag. reflexivity.
  assert (Hk := Div0.mod_mul l k).
  assert (Hl := Div0.mod_mul k l).
  rewrite mul_comm in Hk.
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
  - subst. simpl. rewrite mod_0_r in mdivk. subst. rewrite mod_0_r in kdivn. assumption.
  - rewrite <- Div0.div_exact in mdivk.
    rewrite <- Div0.div_exact in kdivn.
    rewrite mdivk in kdivn.
    rewrite kdivn. rewrite <- mul_assoc. rewrite mul_comm.
    apply Div0.mod_mul.
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
    (In 1 l /\ In n l).
Proof.
  intros.
  destruct (divisorspf nnz) as [ _ iff ].
  unfold l.
  split; rewrite <- iff; [ apply mod_1_r | apply Div0.mod_same ].
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
    assert (1 <= S (S n)); [ lia | ].
    assert (Hy := Hx H0). rewrite H in Hy. 
    rewrite Nat.sqrt_1 in Hy.
    lia.
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
  destruct (sqrt_spec n); [ lia | ]. unfold lt in *.
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
  assert (Hy := Div0.div_exact n (sqrt n)).
  assert (n / sqrt n <> 0). apply div_modnz; auto.
  assert (Hz := Div0.div_exact n (n / sqrt n)).
  generalize sqdiv. intro neqsq. rewrite <- Hy in neqsq. clear Hy.
  generalize ndsqdiv. intro neqnsq. rewrite <- Hz in neqnsq. clear Hz.
  destruct (sqrt_spec n); [ lia | ]. unfold lt in H2. simpl in H2.
  assert (n <= sqrt n + sqrt n * S (sqrt n)). lia. clear H2.
  assert (sqrt n <= n / sqrt n <= 2 + sqrt n). split. 
    assumption. assert (Hxx := Div0.div_le_mono n (sqrt n + sqrt n * S (sqrt n)) (sqrt n) H3).
    assert (sqrt n + sqrt n * S (sqrt n) = sqrt n * (2 + (sqrt n))).
      assert (2 + sqrt n = 1 + S (sqrt n)). lia. rewrite H2. rewrite mul_add_distr_l.
      rewrite (mul_comm _ 1). simpl. rewrite (add_comm _ 0). simpl. reflexivity.
      rewrite H2 in Hxx. rewrite mul_comm in Hxx. rewrite Nat.div_mul in Hxx; auto.
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

Definition divisors_nsr {n} (nnz : n <> 0) := let nzd := divisors_raw nnz in
                                              if eq_nat_dec n (sqrt n * sqrt n)
                                              then remove eq_nat_dec (sqrt n) nzd
                                              else nzd.

Lemma divisors_raw_nz :
  forall n (nnz : n <> 0) a,
    In a (divisors_raw nnz) -> a <> 0.
Proof.
  intros. intro. subst.
  assert (Hx := @divisorspf _ nnz).
  unfold confprops in Hx. destruct Hx.
  assert (H1 := H1 0).
  rewrite <- H1 in H. clear H1 H0.
  destruct n; [ elim nnz; reflexivity | ].
  rewrite Nat.mod_0_r in H. discriminate.
Qed.

Lemma divisors_nsr_nz :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> a <> 0.
Proof.
  intros. intro. unfold divisors_nsr in H.
  destruct (eq_nat_dec n _).
  - subst. 
    assert (Hx := in_remove eq_nat_dec _ _ _ H).
    destruct Hx as [ Hx _ ].
    assert (Hy := divisors_raw_nz).
    assert (Hy := Hy _ _ _ Hx).
    elim Hy; reflexivity.
  - subst. 
    assert (Hy := divisors_raw_nz).
    assert (Hy := Hy _ _ _ H).
    elim Hy; reflexivity.
Qed.

Lemma divisors_raw_ainndain :
  forall n (nnz : n <> 0) a,
    In a (divisors_raw nnz) -> In (n / a) (divisors_raw nnz).
Proof.
  intros n nnz0 a pf.
  destruct (divisorspf nnz0) as [ lzset indiv ].
  assert (anz := divisors_raw_nz _ nnz0 _ pf).
  generalize pf; intro. rewrite <- indiv in pf0.
  assert (Hx := divisorpair _ _ pf0).
  assert (Hy := div_modnz _ _ nnz0 anz pf0).
  rewrite indiv in Hx.
  assumption.
Qed.

Lemma divisors_nsr_ainndain :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> In (n / a) (divisors_nsr nnz).
Proof.
  intros n nnz0 a pf.
  destruct (divisorspf nnz0) as [ lzset indiv ].
  assert (anz := divisors_nsr_nz _ nnz0 _ pf).
  unfold divisors_nsr in *.
  destruct (eq_nat_dec n (sqrt n * sqrt n)) as [ nsq' | nnsq' ].
  - destruct (eq_nat_dec (sqrt n) a) as [ xeqa | xnea ].
    + rewrite xeqa in *. ainral.
    + assert (anex := neqflip _ _ _ xnea). ainrbl.
      generalize pf; intro. rewrite <- indiv in pf0.
      assert (ndad := divisorpair _ _ pf0). rewrite indiv in ndad.
      assert (ndanz := div_modnz _ _ nnz0 anz pf0).
      destruct (eq_nat_dec (sqrt n) (n / a)); [ | rewrite <- remove_corr_neq; assumption ].
      rewrite (fsqn _ _ nsq') in e.
      rewrite (deneqden _ _ (sqrt n) nnz0 anz pf0) in xnea.
      * elim xnea. reflexivity.
      * intro srz. rewrite srz in nsq'. simpl in nsq'. elim nnz0. assumption.
      * apply fsqd. assumption.
      * rewrite e. reflexivity.
  - apply divisors_raw_ainndain. assumption.
Qed.

Lemma divisors_nz_ainadiv :
  forall n (nnz : n <> 0) a,
    In a (divisors_raw nnz) -> n mod a = 0.
Proof.
    intros n nnz a ainl.
    assert (anz := divisors_raw_nz _ nnz _ ainl).
    destruct (divisorspf nnz) as [ lzset indiv ].
    rewrite indiv.
    assumption.
Qed.

Lemma divisors_nsr_ainadiv :
  forall n (nnz : n <> 0) a,
    In a (divisors_nsr nnz) -> n mod a = 0.
Proof.
    intros n nnz a ainl.
    assert (anz := divisors_nsr_nz _ nnz _ ainl).
    destruct (divisorspf nnz) as [ lzset indiv ].
    unfold divisors_nsr in ainl.
    rewrite indiv.
    destruct (eq_nat_dec n (sqrt n * sqrt n)) as [ nsq | nnsq ].
    - destruct (eq_nat_dec a (sqrt n)) as [ asr | nasr ].
      + rewrite <- asr in ainl. ainral.
      + ainrbl. assumption.
    - assumption.
Qed.

Lemma divisors_nsr_is_set :
  forall n (nnz : n <> 0),
    NoDup (divisors_nsr nnz).
Proof.
  intros.
  destruct (divisorspf nnz) as [ lzset _ ].
  unfold divisors_nsr.
  destruct eq_nat_dec; repeat apply setrm; assumption.
Qed.

Lemma divisorcount :
  forall n (nnz : n <> 0) l,
    l = divisors_nsr nnz ->
    Even (length l).

Proof.
  intros n nnz0 l leq.
  destruct (divisorspf nnz0) as [ lzset indiv ].

  assert (inpirr := NoDup_In_proof_irrelevant2 eq_nat_dec (divisors_nsr_is_set _ nnz0)).
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

  unfold divisors_nsr in leq.
  assert ({f : {x | In x l} -> {x | In x l} | forall a, a <> f a /\ a = f (f a) /\ (In a x -> In (f a) x)}) as pairsig.
  refine (exist _ (fun x => exist _ (pair x) (*pairin*)_) _). intro. split; [ | split ].
  Unshelve.
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
    rewrite <- e at 1. rewrite length_map.
    apply iftheneven. split.

    + assert (NoDup l) as lset. rewrite leq. destruct (eq_nat_dec n (sqrt n * sqrt n)); repeat apply setrm; assumption.
      rewrite <- e in lset. revert lset inpirr. clear. intros lset inpirr. remember (proj1_sig (P:=fun x : nat => In x l)) as y.
      induction x. simpl. constructor.
      simpl in *.
      assert (NoDup x) as xset.
      { apply IHx. inversion lset. assumption. }
      assert (~In (y a) (map y x)) as aninx'.
      { inversion lset. assumption. }
      assert (~In a x) as aninx.
      { revert Heqy aninx'. clear. intros; subst.
        destruct a. simpl in *.
        intro inx. elim aninx'. clear aninx'.
        induction x.
        - simpl in *. assumption.
        - simpl in *. destruct inx.
          + subst. simpl. left. reflexivity.
          + right. apply IHx. assumption.
      }
      constructor; assumption.

    + unfold paired_list. intros a ainx.
      apply ainpain. assumption.
  - solve [ apply pairin ].
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
  simpl. rewrite mul_comm. simpl. remember (n*n). clear Heqn0. lia.
Qed.

Lemma nltsqn :
  forall n, 1 < n -> n < n * n.
Proof.
  induction n. simpl. intros. lia.
  intros. destruct (eq_nat_dec 1 n).
  - subst. simpl. lia.
  - assert (1 < n). lia.
    assert (Hx := IHn H0).
    simpl. rewrite mul_comm. simpl. lia.
Qed.

Lemma sqmon_left :
  forall n m, n < m -> n * n < m * m.
Proof.
  induction n. simpl. intros. destruct m. lia. simpl. remember (m * _). lia.
  intros. simpl. rewrite mul_comm. simpl. destruct m. exfalso. lia.
  assert (n < m). lia.
  assert (Hx := IHn _ H0). simpl. rewrite (mul_comm m _). simpl. remember (n*n). remember (m*m).
  lia.
Qed.

Lemma sqmon_right :
  forall n m, n * n < m * m -> n < m.
Proof.
  intros.
  assert (Hx := Nat.sqrt_le_mono (n*n) (m*m)).
  repeat rewrite Nat.sqrt_square in Hx.
  destruct (eq_nat_dec n m). subst. exfalso. clear Hx. lia.
  assert (n * n <= m * m). lia.
  assert (Hy := Hx H0). lia.
Qed.

Lemma apbsq :
  forall a b, (a + b) * (a + b) = a*a + 2*a*b + b*b.
Proof.
  induction a. simpl. reflexivity.
  intros. lia.
Qed.

Lemma sqdiff :
  forall n m, n * n < m * m -> m * m = n * n + 2 * n * (m - n) + (m - n) * (m - n).
Proof.
  intros.
  assert (Hx := sqmon_right _ _ H).
  assert (m = n + (m - n)). lia.
  rewrite H0 in *.
  remember (m - n). clear.
  assert (Hx := apbsq n n0).
  rewrite Hx. assert (forall a b, a + b - a = b). clear. intros. lia.
  rewrite H. reflexivity.
Qed.

Lemma sqrtmid :
  forall x n, n * n < x < (S n) * (S n) -> ~issq x.
Proof.
  intros. intro. unfold issq in H0. destruct H0. destruct H.
  subst.
  assert (Hxx := sqmon_right _ _ H). clear H.
  assert (Hyy := sqmon_right _ _ H1). clear H1.
  lia.
Qed.

Lemma sqSnsq :
  forall n, n <> 0 -> issq n -> ~issq (S n).
Proof.
  intros n nnz nsq. intro Snnsq. unfold issq in *. destruct nsq as [ sqn nsq ], Snnsq as [ sqSn Snnsq ].
  assert (sqn * sqn < sqSn * sqSn) as xsqltx0sq. lia.
  assert (sqltsqS := sqmon_right _ _ xsqltx0sq).
  assert (sqSn = sqn + (sqSn - sqn)) as sqSn'eq. lia.
  rewrite sqSn'eq in *. remember (sqSn - sqn) as sqSn'. clear sqSn sqSn'eq HeqsqSn'.
  rewrite apbsq in Snnsq. rewrite nsq in Snnsq.
  assert (sqn <> 0) as sqnnz. intro sqnz. rewrite sqnz in nsq. simpl in nsq. elim nnz. assumption.
  assert (S (sqn * sqn) = sqn * sqn + 1) as Ssqnsq. lia.
  rewrite Ssqnsq in Snnsq. revert Snnsq sqnnz. clear. intros.
  rewrite <- add_assoc in Snnsq.
  rewrite Nat.add_cancel_l in Snnsq.
  destruct sqSn'. rewrite mul_comm in Snnsq. simpl in Snnsq. discriminate.
  rewrite add_comm in Snnsq.
  destruct sqn. elim sqnnz. reflexivity.
  clear sqnnz.
  simpl in Snnsq. rewrite add_comm in Snnsq. simpl in Snnsq. discriminate.
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
    simpl. rewrite (mul_comm _ (S _)). simpl.
    simpl in klims. rewrite (add_comm _ 0) in klims. simpl in klims.
    remember (srn * srn). revert klims. clear. intros. lia.
  assert (Hy := Hx H). clear Hx H. elim Hy. exists sr'. assumption.
Qed.

Lemma divisorparity_nsq :
  forall n (nnz : n <> 0),
    ~issq n ->
    Even (length (divisors_raw nnz)).
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
    ~Even (length (divisors_raw nnz)).
Proof.
  intros n nnz nnsq. intro rawev.
  assert (evenall := divisorcount _ nnz (divisors_nsr nnz) ltac:(reflexivity)).
  unfold divisors_nsr in evenall.
  destruct (eq_nat_dec n _).
  - destruct (divisorspf nnz) as [ lzset indiv ].
    assert (In (sqrt n) (divisors_raw nnz)) as sqd.
    {
      unfold divisors_raw in *.
      assert (srdiv := fsqd _ _ e).
      assert (srin := fsqd _ _ e). rewrite indiv in srin.
      assert (sqrt n <> 0) as srnz. rewrite sqz. assumption.
      assumption.
    }
    remember (divisors_raw nnz).
    remember (sqrt n).
    assert (Hx := lrm _ eq_nat_dec l lzset _ sqd).
    remember (length l).
    remember (length (remove eq_dec n0 l)).
    revert rawev evenall Hx.
    clear. intros. subst.
    rewrite Even_succ in rawev.
    apply Even_Odd_False with n2; assumption.
  - elim n0. unfold issq in nnsq. destruct nnsq.
    assert (Hx := sqrt_corr _ _ H).
    rewrite Hx in H. assumption.
Qed.

Lemma sqne :
  forall n (nnz : n <> 0),
    issq n <-> ~Even (length (divisors_raw nnz)).
Proof.
  intros.
  assert (Hx := iffif {x | x <> 0} (fun nnz => issq (proj1_sig nnz)) (fun nnz => Even (length (divisors_raw (proj2_sig nnz))))). simpl in *.

  set (x := exist (fun x => x <> 0) n nnz).
  assert ((forall a : {x | x <> 0}, {issq (proj1_sig a)} + {~ issq (proj1_sig a)})) as issq_dec_sig.
    clear Hx. intros. destruct a. simpl. apply issq_dec.
  assert (Hy := Hx issq_dec_sig). clear Hx issq_dec_sig.

  assert (forall a : {x | x <> 0}, {Even (length (divisors_raw (proj2_sig a)))} + {~ Even (length (divisors_raw (proj2_sig a)))}) as evendec.
    clear.
    intros. destruct a. simpl.
    remember (length _). clear.
    assert (Hx := Nat.even_spec).
    destruct (even n0) eqn:n0ev.
      left. rewrite Hx in n0ev. assumption.
      right. intro. rewrite <- Hx in H. rewrite H in n0ev. discriminate n0ev.
  assert (Hx := Hy evendec). clear Hy evendec.

  assert (forall a : {x | x <> 0}, issq (proj1_sig a) -> ~ Even (length (divisors_raw (proj2_sig a)))) as divisorparity_sq'.
    intros. destruct a. simpl in *. apply divisorparity_sq; assumption.
  assert (Hy := Hx divisorparity_sq'). clear Hx divisorparity_sq'.

  assert (forall a : {x | x <> 0}, ~ issq (proj1_sig a) -> Even (length (divisors_raw (proj2_sig a)))) as divisorparity_nsq'.
    intros. apply divisorparity_nsq; assumption.
  assert (Hx := Hy divisorparity_nsq' x). clear Hy divisorparity_nsq'.
  
  unfold x in Hx. simpl in Hx. assumption.
Qed.

Lemma add_lt_mul :
  forall a, 2 < a -> a + a < a * a.
Proof.
  intros.
  assert (1 < a). lia.
  assert (Hx := Nat.add_le_mul a a H0 H0). clear H0.
  destruct (eq_nat_dec (a + a) (a * a)); [ | lia ].
  rewrite e in *.
  revert H e Hx. induction a using (nat_interval_ind 3).
  - intros. destruct a; [ lia | ]. destruct a; [ lia | ]. destruct a; lia.
  - intros. destruct a; [ lia | ]. destruct a; [ lia | ]. destruct a; try lia.
Qed.
  
Lemma minsqdiff :
  forall a b,
    issq a ->
    issq b ->
    a < b ->
    a <> 0 ->
   2 * Nat.sqrt b < S (S (b - a)).
Proof.
  intros.
  destruct H, H0.
  rewrite H, H0 in *.
  assert (Hx := sqdiff _ _ H1).
  rewrite Nat.sqrt_square.
  rewrite Hx.
  assert (x * x + 2 * x * (x0 - x) + (x0 - x) * (x0 - x) - x * x = 2 * x * (x0 - x) + (x0 - x) * (x0 - x)). clear. simpl. repeat rewrite (add_comm _ 0). simpl. rewrite <- add_assoc. rewrite add_comm.
  rewrite Nat.add_sub. reflexivity.
  rewrite H3.
  assert (Hy := sqmon_right _ _ H1).
  assert (x0 = x + (x0 - x)). revert Hy. clear. intro. lia.
  rewrite H4 in *. remember (x0 - x). clear H4 x0 Heqn.
  assert (x + n - x = n). rewrite add_comm. rewrite (Nat.add_sub n x). reflexivity.
  rewrite H4.
  clear Hx H H0 H1 H3 H4 a b. destruct n. rewrite add_comm in Hy. simpl in Hy. lia.
  rewrite add_comm. unfold plus at 1. fold plus. clear Hy.
  simpl. repeat rewrite (add_comm _ 0). simpl. repeat rewrite (mul_comm _ (S _)). simpl.
  rewrite add_comm. simpl. rewrite (add_comm _ (S (n + _))). simpl.
  assert (n + x + (n + x) < S (n + (n + n * n) + (x + x + n * (x + x)))).
  rewrite mul_add_distr_l. remember (n * n). remember (n * x). lia.
  lia.
Defined.

Lemma xmodmeqk_Sxmodmeq0 :
  forall x m,
    S (x mod m) = m ->
    (S x) mod m = 0.
Proof.
  intros. destruct m; [ discriminate | ].
  assert (S m <> 0) as mnz; [ intro; discriminate | ].
  assert (Hx := Div0.add_mod_idemp_l x 1 (S m)).
  repeat rewrite (add_comm _ 1) in Hx. unfold plus in Hx.
  assert (x mod (S m) = m).
  - simpl in *. injection H. intro. assumption.
  - rewrite H0 in *.
    rewrite <- Hx.
    rewrite Div0.mod_same.
    reflexivity.
Qed.

Lemma xmodmnem_SxmodmeqSxmodm :
  forall x m,
    m <> 0 ->
    S (x mod m) <> m ->
    (S x) mod m = S (x mod m).
Proof.
  intros.
  assert (Hx := Div0.add_mod_idemp_l x 1 m).
  repeat rewrite (add_comm _ 1) in Hx. unfold plus in Hx.
  rewrite <- Hx.
  remember (x mod m).
  assert (n < m).
  {
    assert (0 <= x). lia.
    assert (0 < m). lia.
    destruct (mod_bound_pos _ _ H1 H2). rewrite Heqn. assumption.
  }
  assert (S n < m). lia.
  assert (Hz := Nat.mod_small _ _ H2). assumption.
Qed.

Lemma apbmodmeqb_amodmz :
  forall a b m, m <> 0 -> (a + b) mod m = b mod m -> a mod m = 0.
Proof.
  intros a b m mnz H. destruct m; [ contradiction | clear mnz ].
  destruct m; [ solve [ apply mod_1_r ] | ].
  assert (1 < S (S m)) as H0; [ lia | ]. remember (S (S m)) as m'. clear m Heqm'. rename m' into m.
  rewrite Div0.add_mod in H.
  assert (m <> 0); [ lia | ].
  assert (Hx := Nat.mod_upper_bound a _ H1).
  assert (Hy := Nat.mod_upper_bound b _ H1).
  remember (a mod m) as a'. clear a Heqa'. rename a' into a.
  remember (b mod m) as b'. clear b Heqb'. rename b' into b.

  assert (Ha := div_mod a _ H1).
  assert (Hb := div_mod b _ H1).
  assert (Hxx := div_mod (a + b) _ H1). rewrite H in Hxx.
  repeat rewrite (add_comm _ b) in Hxx.
  rewrite add_cancel_l in Hxx. rewrite add_comm in Hxx.
  destruct (eq_nat_dec ((a + b) / m) 0).
  - rewrite e in Hxx. rewrite mul_comm in Hxx. simpl in Hx. assumption.
  - destruct (eq_nat_dec ((a + b) / m) 1).
    + rewrite e in Hxx. rewrite mul_comm in Hxx. simpl in Hxx. rewrite add_comm in Hxx. simpl in Hxx. rewrite Hxx in Hx. revert Hx. clear. intro. lia.
    + assert ((a + b) < 2 * m); [ lia | ].
      rewrite mul_comm in H2.
      assert (Hxz := Div0.div_lt_upper_bound _ _ _ H2). lia.
Qed.
