From Undecidability.Axioms Require Import axioms principles EA.
From Undecidability.Shared Require Import embed_nat Pigeonhole Dec partial.
From Undecidability.Synthetic Require Import simple Definitions FinitenessFacts reductions SemiDecidabilityFacts DecidabilityFacts.
Require Import Init.Nat Lists.ListSet Arith.PeanoNat Arith.Compare_dec.
From Coq Require Import Lia FinFun Program.Basics.
From Equations Require Import Equations.
Require Import List.
Import ListNotations.
From Kolmogorov Require Import binaryEncoding preliminaries listFacts kolmogorov.

Definition nonR n x : Prop :=
    exists i s, T n i s = Some x /\ length (encode i) < length (encode x).

Definition R n x : Prop :=
    forall i s, T n i s = Some x -> length (encode i) >= length (encode x).

Lemma R_nonR_contradiction c :
    forall x, ~(R c x /\ nonR c x).
Proof.
    intros x [H (i & s & ?H & ?H)].
    specialize (H i s H0).
    lia.
Qed.

Lemma nonR_nonRalt c :
    LEM -> forall x, nonR c x <-> (exists kc, kol c x kc /\ kc < length(encode x)).
Proof.
    intros xm x.
    split.
    {
        intros (i & s & ?H & ?H).
        destruct (xm (exists kc, kol c x kc)) as [[kc ?H]|].
        {
            exists kc; split; [easy|].
            destruct H1 as (?i & ?s & ?H & <- & ?H).
            enough (length (encode i0) <= length(encode i)) by lia.
            exact (H2 i s H).
        }
        {
            exfalso.
            apply (exists_kol c i x s H).
            exact H1.
        }        
    }
    {
        intros (kc & (i & s & ?H & <- & _) & ?H).
        exists i, s.
        auto.
    }
Qed.

Lemma R_Ralt c :
    LEM -> forall x, R c x <-> (exists kc, kol c x kc /\ kc >= length(encode x)) \/ (forall kc, ~kol c x kc).
Proof.
    intros xm x.
    split.
    {
        intros.
        destruct (xm (exists kc, kol c x kc)) as [[kc ?H]|].
        {
            left.
            exists kc; split; [easy|].
            destruct H0 as (?i & ?s & ?H & <- & _).
            exact (H i s H0).
        }
        {
            right.
            destruct (xm (forall kc : nat, ~ kol c x kc)); [easy|].
            exfalso.
            apply H1; intros kc ?H.
            apply H0.
            now exists kc.
        }        
    }
    {
        intros [(kc & (i' & s' & ?H & <- & ?H) & ?H)|] i s H2.
        - specialize (H0 i s H2).
          lia.
        - enough (exists kc, kol c x kc) as [kc ?H].
          + now specialize (H kc).
          + assert (H3 := exists_kol c i x s H2).
            now destruct (xm (exists kc : nat, kol c x kc)).
    }
Qed.

Lemma nonR_R n :
    forall x, (compl (nonR n) x) <-> R n x.
Proof.
    unfold compl, R, nonR in *.
    split; intros.
    {
        assert (forall i s : nat, ~ (T n i s = Some x /\ length (encode i) < length (encode x))) by eauto.
        specialize (H1 i s).
        assert (T n i s <> Some x \/ ~(length (encode i) < length (encode x))) by tauto.
        destruct H2; [contradiction|lia]. 
    }
    {
        intros (i & s & ?H & ?H).
        specialize (H i s H0).
        lia.
    }
Qed.

Lemma R_nonR1 n :
    forall x, nonR n x -> (compl (R n) x).
Proof.
    intros x (?i & ?s & ?H & ?H) ?H.
    specialize (H1 i s H).
    lia.
Qed.

Lemma R_nonR n :
    MP -> forall x, (compl (R n) x) <-> nonR n x.
Proof.
    intros mp x.
    unfold compl.
    split.
    {
        intros.
        unfold nonR.
        enough (exists p, (let (i,s) := unembed p in (andb (ONat_eqb (T n i s) (Some x)) (Nat.ltb (length (encode i)) (length (encode x))))) = true) as [p ?H].
        {
            destruct (unembed p) as [i s].
            apply Bool.andb_true_iff in H0.
            exists i, s.
            destruct H0.
            apply ONat_eqb_eq in H0.
            apply Nat.ltb_lt in H1.
            easy. 
        }
        apply mp.
        intro.
        apply H.
        apply nonR_R.
        intros (i & s & ?H & ?H).
        apply H0.
        exists (embed (i,s)).
        rewrite embedP.
        apply Bool.andb_true_iff; split.
        { now apply ONat_eqb_eq. }
        { now apply Nat.ltb_lt. }
    }
    {
        apply R_nonR1.
    }
Qed.

Lemma nonR_enumerator c:
    univ c -> {f : nat -> option nat | enumerator f (nonR c)}.
Proof.
    intros.
    exists (fun p => let (i,s) := unembed p in match T c i s with
                                                              | Some o => if lt_dec (length (encode i)) (length (encode o)) then Some o else None
                                                              | None   => None end).
    split; intros.
    {
        destruct H0 as (i & s & ?H & ?H).
        exists (embed (i,s)).
        rewrite embedP, H0.
        destruct (lt_dec (length (encode i)) (length (encode x))).
        { reflexivity. }
        { contradiction. }
    }
    {
        destruct H0 as [p H0].
        destruct (unembed p) as [i s] eqn:?H.
        destruct (T c i s) as [o|] eqn:?H; [|discriminate].
        destruct (lt_dec (length (encode i)) (length (encode o))); [|discriminate].
        exists i, s.
        inversion H0.
        intuition.
    }
Qed.


Lemma nonR_enum c:
    univ c -> enumerable (nonR c).
Proof.
    intros; destruct (nonR_enumerator c H) as [f ?H].
    now exists f.
Qed.

Lemma nonR_list c :
    forall k L, NoDup L -> incl L (map decode (n_list k)) -> Forall (nonR c) L -> exists L', length L = length L' /\ NoDup L' /\ Forall (fun i => exists s o, T c i s = Some o /\ In o L /\ length (encode i) < length (encode o)) L'.
Proof.
    induction L; intros; [exists nil; repeat apply conj; repeat constructor|].
    depelim H.
    depelim H2.
    unshelve eassert (IHL := IHL H0 _ H3).
    { intros x ?H. apply H1. now right. }
    destruct IHL as [L' (?H & ?H & ?H)].
    destruct H2 as (?i & ?s & ?H & ?H).
    exists (i :: L').
    repeat apply conj; cbn.
    - lia.
    - constructor; [intro|easy].
      rewrite Forall_forall in H6.
      specialize (H6 i H8) as (?s & ?o & ?H & ?H & ?H).
      enough (a = o) by intuition.
      apply (monotonic_eq Nat.eq_dec _ (T_mono c i) s s0 a o H2 H6).
    - constructor.
      + exists s, a.
        repeat apply conj; intuition.
      + rewrite Forall_forall in *; intros.
        specialize (H6 x H8) as (?s & ?o & ?H & ?H & ?H).
        exists s0, o; repeat apply conj; intuition.
Qed.

Lemma nonR_length c l' k :
    univ c -> NoDup l' ->
    (forall x : nat, In x l' -> (nonR c) x /\ In x (map decode (n_list k))) -> length l' < 2^k.
Proof.
    intros.
    assert (length l' < 2 ^ k \/ length l' = 2 ^ k \/ length l' > 2 ^ k) as [|[|]] by lia; [easy| |].
    {
        rewrite <- (n_list_length k) in *.
        assert (incl l' (map decode (n_list k))) by (intros x ?H; now specialize (H1 x H3)).
        enough (~forall x, In x l' -> nonR c x /\ (length (encode x) = k)).
        {
            exfalso.
            apply H4; intros.
            split; intros; specialize (H1 x H5) as [?H ?H]; [easy|].
            rewrite in_map_iff in H6.
            destruct H6 as [y [<- H7]].
            rewrite encodeDecode.
            now apply n_list_In.
        }
        intro. (* TODO : clear H1 *)
        assert (Forall (nonR c) l') as tmp by (apply Forall_forall; intuition).
        destruct (nonR_list c k l' H0 H3 tmp) as (L' & ?H & ?H & ?H); clear tmp.
        rewrite Forall_forall in H7.
        enough (length L' < length l') by lia.
        destruct k.
        {
            destruct L' as [|x [|]] eqn:?H; cbn in *; [lia| |lia].
            specialize (H7 x (or_introl eq_refl)) as (?s & ?o & _ & ?H & ?H).
            specialize (H4 o H7) as [_ H4].
            lia.
        }
        {
            assert (H8 := le_n_list_lt_n_list k).
            enough (length L' <= length (le_n_list k)) by lia.
            rewrite <- (map_length decode).
            apply pigeonhole_length; [lia|easy|].
            intros x ?H.
            specialize (H7 x H9) as (_ & ?o & _ & ?H & ?H).
            apply in_map_iff; exists (encode x); rewrite decodeEncode; apply conj; [reflexivity|].
            apply le_n_list_In.
            specialize (H4 o H7); lia.
        }
    }
    {
        exfalso.
        rewrite <- (n_list_length k), <- (map_length decode) in H2.
        apply (N_imp _ (pigeonhole_constructive l' (map decode (n_list k)) H0 H2)); intros (x & ?H & ?H).
        specialize (H1 x H3) as [_ H1].
        contradiction.
    }
Qed.

Lemma R_unbounded c :
    univ c -> forall k, ~~ exists x, length (encode x) = k /\ ~(nonR c x).
Proof.
    intros H k.
    pose (n_list_In k).
    apply (DN_imp (p_sublist_NoDup nat Nat.eq_dec (nonR c) (map decode (n_list k)))).
    intros [l' [H0 H1]].
    pose (pigeonhole_constructive (n_list k) (map encode l') (n_list_NoDup k)).
    assert (forall x : nat, In x l' -> nonR c x /\ In x (map decode (n_list k))) as H1' by intuition.
    pose (nonR_length c l' k H H0 H1').
    assert (length (n_list k) > length (map encode l')).
    {
        rewrite map_length.
        rewrite n_list_length.
        easy.   
    }
    specialize (n H2).
    apply (DN_imp n); intros [L [?H ?H]]; clear n.
    apply DN_intro.
    exists (decode L).
    split.
    {
        apply n_list_In in H3.
        now rewrite <- H3, encodeDecode.
    }
    {
        intro.
        clear l.
        specialize (H1 (decode L)) as [_ H1].
        apply H4.
        apply in_map_iff.
        exists (decode L).
        rewrite encodeDecode.
        split; [easy|].
        apply H1; split; [easy|].
        apply in_map_iff.
        now exists L.
    }
Qed.

Corollary R_unbounded' c :
    univ c -> forall k, ~~ exists x, length (encode x) = k /\ R c x.
Proof.
    intros.
    apply (DN_imp (R_unbounded c H k)); intros (x & ?H & ?H%nonR_R); apply DN_intro.
    exists x; easy.
Qed.

Lemma R_infinite c :
    univ c -> ~ exhaustible (compl (nonR c)).
Proof.
    intros H [L H0].
    pose (R_unbounded c H (S(list_numbers.max_list_with (compose length encode) L))).
    apply (N_imp (exists x : nat, length (encode x) = S (list_numbers.max_list_with (compose length encode) L) /\ ~ nonR c x) n); clear n.
    intros (x & ?H & ?H).
    specialize (H0 x H2).
    pose (max_list_with_spec x L (compose length encode) H0).
    cbn [compose] in l.
    lia.
Qed.

Lemma R_no_enum_inf_subp c :
    MP -> univ c -> 
    ~ (exists q : nat -> Prop, enumerable q /\ ~ exhaustible q /\ (forall x : nat, q x -> compl (nonR c) x)).
Proof.
    intros mp H (q & (f & ?H) & ?H & ?H).
    enough (forall m, {n | match f n with Some y => (compose length encode) y > m | None => False end}).
    {
        destruct (univ_upper_bound c (fun m => (match f(proj1_sig (H3 m)) with Some x => x | _ => 0 end)) H) as (k & ?H).
        apply l_sublinear.
        exists k.
        intros m.
        specialize (H4 m) as (?i & ?s & ?H & ?H).
        destruct (H3 m) as (?n & ?H); cbn in H4; clear H3.
        destruct (f n) as [y|] eqn:?H; [|now exfalso].
        specialize (H0 y).
        assert (q y) by (apply H0; now exists n).
        specialize (H2 y H7); clear H7.
        apply nonR_R in H2.
        specialize (H2 i s H4); clear H4.
        cbn [compose] in H6.
        lia.
    }
    {
        intros.
        apply mu_nat.mu_nat_dep.
        {
            intros.
            destruct (f n); [|now right].
            apply gt_dec.
        }
        {
            enough (exists n : nat, (if f n is (Some x) then Nat.ltb m (length (encode x)) else false) = true).
            {
                destruct H3 as [n ?H].
                exists n.
                destruct (f n); [now apply Nat.ltb_lt|discriminate].
            }
            {
                apply mp.
                apply (DN_imp (p_enumerable_infinite_unbounded q f H0 H1 m)); intros [n H5].
                apply DN_intro.
                exists n.
                destruct (f n); [now apply Nat.ltb_lt|contradiction].
            }
        }
    }
Qed.

Definition simple (p : nat -> Prop) :=
  enumerable p /\ ~ exhaustible (compl p) /\ ~ exists q, enumerable q /\ ~ exhaustible q /\ (forall x, q x -> compl p x).

Lemma nonR_simple c :
    MP -> univ c -> simple (nonR c).
Proof.
    intros mp H.
    repeat apply conj.
    { exact (nonR_enum c H). }
    { exact (R_infinite c H). }
    { exact (R_no_enum_inf_subp c mp H). }
Qed.

Fact simple_enum_sdec (p : nat -> Prop) : simple p <-> simple.simple p.
Proof.
    split; intros (?H & ?H & ?H); repeat apply conj; auto.
    - apply enumerable_semi_decidable; [apply discrete_nat|easy].
    - intros (q & ?H & ?H & ?H); apply H1.
      exists q; repeat apply conj; auto.
      apply semi_decidable_enumerable; auto.
      exists EnumerabilityFacts.nat_enum.
      apply EnumerabilityFacts.enumeratorᵗ_nat.
    - apply semi_decidable_enumerable; auto.
      exists EnumerabilityFacts.nat_enum.
      apply EnumerabilityFacts.enumeratorᵗ_nat.
    - intros (q & ?H & ?H & ?H); apply H1.
      exists q; repeat apply conj; auto.
      apply enumerable_semi_decidable; [apply discrete_nat|easy].
Qed.

Lemma nonR_undecidable c :
    MP -> univ c -> ~ decidable(nonR c).
Proof.
    intros.
    apply simple_undecidable, simple_enum_sdec.
    now apply nonR_simple.
Qed.

Lemma nonR_m_incomplete c :
    MP -> univ c -> ~ m-complete (nonR c).
Proof.
    intros.
    apply simple_m_incomplete, simple_enum_sdec.
    now apply nonR_simple.
Qed.