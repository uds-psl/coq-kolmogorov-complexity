From Undecidability.Axioms Require Import axioms principles.
From Undecidability.Shared Require Import embed_nat Pigeonhole Dec partial.
From Undecidability.Synthetic Require Import simple Definitions FinitenessFacts reductions SemiDecidabilityFacts DecidabilityFacts.
Require Import Init.Nat Lists.ListSet Arith.PeanoNat Arith.Compare_dec.
From Coq Require Import Lia FinFun Program.Basics.
From Equations Require Import Equations.
Require Import List.
Import ListNotations.
From Kolmogorov Require Import binaryEncoding preliminaries listFacts kolmogorov randomNumbers preliminaries.

Fixpoint enum_p_list (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) : list nat.
destruct s.
{
    refine (if f 0 is Some x then _ else nil).
    refine (if Nat.eq_dec (length (encode x)) n then _ else nil).
    refine (if m then nil else [x]).
}
{

    refine (let L := enum_p_list p f m n s in _).
    refine (if Nat.eq_dec (length L) m then L else _).
    refine (if f(S s) is Some x then _ else L).
    refine (if Nat.eq_dec (length (encode x)) n then _ else L).
    refine (if in_dec Nat.eq_dec x L then L else x :: L).
}
Defined.

Lemma enum_p_list_NoDup (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    NoDup (enum_p_list p f m n s).
Proof.
    unfold enum_p_list.
    induction s.
    {
        destruct (f 0) as [x|]; [destruct (Nat.eq_dec (length (encode x)) n), m|]; cbn; repeat constructor.
        intros [].
    }
    {
        fold enum_p_list in *.
        destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m); [easy|].
        destruct (f (S s)); [|easy].
        destruct (Nat.eq_dec (length (encode n1)) n); [|easy].
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); [easy|].
        constructor; easy.
    }
Qed.

Lemma enum_p_list_length (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    length (enum_p_list p f m n s) <= m.
Proof.
    unfold enum_p_list.
    induction s.
    {
        destruct (f 0) as [x|]; cbn; [|lia].
        destruct (Nat.eq_dec (length (encode x)) n); cbn; repeat constructor.
        { destruct m; cbn. all: lia. }
        { lia. }
    }
    {
        fold enum_p_list in *.
        destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m); [easy|].
        destruct (f (S s)); [|easy].
        destruct (Nat.eq_dec (length (encode n1)) n); [|easy].
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); [easy|].
        cbn.
        lia.
    }
Qed.

Lemma enum_p_list_length_s (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
  length (enum_p_list p f m n s) <= S s.
Proof.
  unfold enum_p_list.
  induction s.
  - destruct (f 0) as [x|]; cbn; [|repeat constructor].
    destruct (Nat.eq_dec (length (encode x)) n), m; cbn; repeat constructor.
  - fold enum_p_list in *.
    destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m), (f (S s)); [lia|lia| |lia].
    destruct (Nat.eq_dec (length (encode n1)) n), (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); [lia| |lia|lia].
    cbn.
    lia.
Qed.

Lemma enum_p_list_sat_p (p : nat -> Prop) (m n s : nat) (f : nat -> option nat) :
    enumerator f p -> forall x, In x (enum_p_list p f m n s) -> p x.
Proof.
    unfold enum_p_list.
    induction s.
    {
        intros.
        destruct (f 0) eqn:?H; cbn; [|contradiction].
        destruct (Nat.eq_dec (length (encode n0)) n); cbn in H0; [|contradiction].
        destruct m; cbn in H0; [contradiction|destruct H0 as [|[]]].
        apply H.
        exists 0.
        now rewrite <- H0.
    }
    {
        fold enum_p_list in *.
        intros.
        specialize (IHs H x).
        destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m).
        { now apply IHs. }
        destruct (f (S s)) eqn:?H.
        2:{ now apply IHs. }
        destruct (Nat.eq_dec (length (encode n1)) n).
        2:{ now apply IHs. }
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)).
        { now apply IHs. }
        destruct H0.
        {
            apply H.
            exists (S s).
            now rewrite <- H0.
        }
        { now apply IHs. }
    }
Qed.

Lemma enum_p_list_sat_len_n (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    forall x, In x (enum_p_list p f m n s) -> length(encode x) = n.
Proof.
    unfold enum_p_list.
    induction s.
    {
        destruct (f 0) as [x|]; cbn; [|lia].
        destruct (Nat.eq_dec (length (encode x)) n); cbn; intros.
        {
            destruct m; cbn in *.
            { contradiction. }
            { destruct H as [<-|[]]. easy. }
        }
        { contradiction. }
    }
    {
        fold enum_p_list in *.
        destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m); [easy|].
        destruct (f (S s)); [|easy].
        destruct (Nat.eq_dec (length (encode n1)) n); [|easy].
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); [easy|].
        cbn.
        intros x [->|?H]; [apply e|].
        now apply IHs.
    }
Qed.

Lemma enum_p_list_incl_step (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    incl (enum_p_list p f m n s) (enum_p_list p f m n (S s)).
Proof.
    induction s; intros x H.
    {
        unfold enum_p_list; fold (enum_p_list p f m n 0).
        destruct (Nat.eq_dec (length (enum_p_list p f m n 0)) m); [easy|].
        destruct (f 1) eqn:?H; [|easy].
        destruct (Nat.eq_dec (length (encode n1)) n); [|easy].
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n 0)); [easy|].
        right.
        easy.
    }
    {
        unfold enum_p_list. fold (enum_p_list p f m n (S s)).
        destruct (Nat.eq_dec (length (enum_p_list p f m n (S s))) m); [easy|].
        destruct (f (S (S s))) eqn:?H; [|easy].
        destruct (Nat.eq_dec (length (encode n1)) n); [|easy].
        destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n (S s))); [easy|].
        right.
        easy.
    }
Qed.

Lemma enum_p_list_incl (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    forall s', s' >= s -> incl (enum_p_list p f m n s) (enum_p_list p f m n s').
Proof.
    induction s'; intros.
    { assert (s = 0) as -> by lia. easy. }
    assert (S s' = s \/ s' >= s) as [->|] by lia; [easy|].
    apply (incl_transitive _ (enum_p_list p f m n s')).
    { apply IHs'. exact H0. }
    { apply (enum_p_list_incl_step p f m n s'). }
Qed.

Lemma enum_p_list_mono_length (p : nat -> Prop) (f : nat -> option nat) (m n : nat) :
    forall s s', s' >= s -> length (enum_p_list p f m n s') >= length (enum_p_list p f m n s).
Proof.
    intros.
    apply pigeonhole_length.
    - lia.
    - apply enum_p_list_NoDup.
    - apply enum_p_list_incl. exact H. 
Qed.

Lemma enum_p_list_max_length (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    forall s', s' >= s -> length(enum_p_list p f m n s) = m -> length(enum_p_list p f m n s') = m.
Proof.
    intros.
    assert (H1 := enum_p_list_mono_length p f m n s s' H).
    assert (H2 := enum_p_list_length p f m n s').
    lia.
Qed.

Lemma enum_p_list_equiv (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    forall s', length(enum_p_list p f m n s) = length(enum_p_list p f m n s') -> equiv (enum_p_list p f m n s') (enum_p_list p f m n s).
Proof.
    intros.
    assert (s <= s' \/ s' <= s) as [|] by lia; split.
    2,3: apply enum_p_list_incl; easy.
    all: assert (H1 := enum_p_list_incl p f m n).
    1: specialize (H1 s s' H0). 2: specialize (H1 s' s H0).
    all: apply NoDup_length_incl; auto; try lia.
    all: apply enum_p_list_NoDup.
Qed.

Lemma enum_p_m_Sm (p : nat -> Prop) (f : nat -> option nat) (n s : nat) :
    forall m, exists L, length L <= 1 /\ equiv (enum_p_list p f (S m) n s) (L ++ (enum_p_list p f m n s)) /\ NoDup (L ++ (enum_p_list p f m n s)).
Proof.
    induction s.
    {
        cbn in *; intros.
        destruct (f 0); [|exists nil; cbn; repeat split; try lia; try easy; try constructor].
        destruct (Nat.eq_dec (length (encode n0))); [|exists nil; cbn; auto; repeat split; try lia; try easy; try constructor].
        destruct m.
        - exists [n0]; cbn; intuition. repeat constructor. intros [].
        - exists nil; cbn; intuition. repeat constructor. intros [].
    }
    {
        intros.
        assert (H := (enum_p_list_NoDup p f (S m) n (S s))); assert (H0 := enum_p_list_NoDup p f m n (S s)).
        cbn in *.
        destruct (Nat.eq_dec (length (enum_p_list p f (S m) n s)) (S m)), (Nat.eq_dec (length (enum_p_list p f m n s)) m); [apply IHs| | |].
        {
            exfalso.
            specialize (IHs m) as [L (?H & ?H & ?H)].
            destruct L as [|?x [|]]; cbn in *; [| |lia].
            - assert (H4 := NoDup_equiv_length_eq Nat.eq_dec (enum_p_list p f (S m) n s) (enum_p_list p f m n s) H (enum_p_list_NoDup p f m n s) H2).
              assert (H5 := enum_p_list_length p f m n s).
              lia.
            - assert (H4 := NoDup_equiv_length_eq Nat.eq_dec (enum_p_list p f (S m) n s) (x :: (enum_p_list p f m n s)) H H3 H2).
              assert (H5 := enum_p_list_length p f m n s).
              rewrite H4 in e; cbn in e.
              lia.
        }
        {
            destruct (f(S s)); [|apply IHs].
            destruct (Nat.eq_dec (length (encode n1)) n); [|apply IHs].
            destruct (in_dec Nat.eq_dec n1 (enum_p_list p f (S m) n s)); [apply IHs|].
            specialize (IHs m) as (L & ?H & ?H & ?H).
            destruct L as [|?x [|]]; cbn in *; [| |lia].
            - exists [n1]. cbn. repeat apply conj; [intuition|intuition|intuition|constructor].
              2: easy.
              destruct H2 as [_ ?H].
              intro.
              specialize (H2 n1 H4).
              easy.
            - assert (H4 := NoDup_equiv_length_eq Nat.eq_dec ((enum_p_list p f (S m) n s)) (x :: enum_p_list p f m n s) (enum_p_list_NoDup p f (S m) n s) H3 H2).
              cbn in H4.
              lia.
        }
        {
            destruct (f(S s)); [|apply IHs].
            destruct (Nat.eq_dec (length (encode n2)) n); [|apply IHs].
            destruct (in_dec Nat.eq_dec n2 (enum_p_list p f (S m) n s)), (in_dec Nat.eq_dec n2 (enum_p_list p f m n s)); try apply IHs; specialize (IHs m) as (?L & ?H & ?H & ?H).
            {
                destruct L as [|?x [|]]; cbn in *; [| |lia].
                - destruct H2 as [?H _].
                  exfalso.
                  apply n3, H2.
                  easy.
                - destruct (Nat.eq_dec x n2).
                  + exists nil; cbn; intuition.
                  + destruct H2 as [?H _].
                    specialize (H2 n2 i) as [|]; contradiction.
            }
            {
                destruct L as [|?x [|]]; cbn in *; [| |lia].
                - destruct H2 as [_ ?H].
                  specialize (H2 n2 i); contradiction.
                - destruct (Nat.eq_dec x n2) as [->|].
                  + depelim H3. contradiction.
                  + destruct H2 as [_ ?H].
                    specialize (H2 n2 (or_intror i)).
                    contradiction.
            }
            {
                destruct L as [|?x [|]]; cbn in *; [| |lia].
                - exists nil; cbn.
                  repeat split; intuition.
                - destruct (Nat.eq_dec x n2).
                  + exists nil; cbn; repeat split; intuition.
                  + exists [x]; cbn; repeat split; [intuition| | |constructor; depelim H3].
                    * intros y [|].
                        { right; now left. }
                        {
                            destruct (Nat.eq_dec x y); [now left|].
                            right.
                            destruct H2 as [?H _].
                            destruct (H2 y H4); [easy|].
                            now right.
                        } 
                    * intros y [|].
                        { right. destruct H2 as [_ ?H]. apply H2. now left. }
                        {
                            destruct (Nat.eq_dec n2 y); [now left|].
                            right.
                            destruct H2 as [_ ?H].
                            apply H2.
                            right.
                            depelim H4; [easy|].
                            easy.
                        } 
                    * intros [|]; [firstorder|contradiction].
                    * constructor; easy.
            }
        }
    }
Qed.

Lemma enum_p_m_step_length (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    length (enum_p_list p f (S m) n s) = S m -> length (enum_p_list p f m n s) = m.
Proof.
    intros.
    destruct (enum_p_m_Sm p f n s m) as [L (?H & ?H & ?H)].
    assert (H3 := NoDup_equiv_length_eq Nat.eq_dec (enum_p_list p f (S m) n s) (L ++ enum_p_list p f m n s) (enum_p_list_NoDup p f (S m) n s) H2 H1).
    assert (H4 := enum_p_list_length p f m n s).
    destruct L as [|x [|]]; cbn in *; lia.
Qed.

Lemma enum_p_m_equiv (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    length (enum_p_list p f (S m) n s) <= m -> equiv (enum_p_list p f m n s) (enum_p_list p f (S m) n s).
Proof.
    induction s; intros.
    {
        cbn in *.
        destruct (f 0); [|easy].
        destruct (Nat.eq_dec (length (encode n0)) n), m; cbn in *; easy.
    }
    {
        cbn in *.
        destruct (Nat.eq_dec (length (enum_p_list p f (S m) n s)) (S m)) as [|_]; [lia|].
        destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m).
        {
            destruct (f (S s)); [|apply IHs; lia].
            destruct (Nat.eq_dec (length (encode n0)) n); [|apply IHs; lia].
            destruct (in_dec Nat.eq_dec n0 (enum_p_list p f (S m) n s)); [apply IHs; lia|].
            cbn in *.
            assert (length (enum_p_list p f (S m) n s) <= m) by lia.
            specialize (IHs H0).
            assert (H1 := NoDup_equiv_length_eq Nat.eq_dec (enum_p_list p f m n s) (enum_p_list p f (S m) n s) (enum_p_list_NoDup p f m n s) (enum_p_list_NoDup p f (S m) n s) IHs).
            lia.
        }
        {
            destruct (f (S s)); [|apply IHs; lia].
            destruct (Nat.eq_dec (length (encode n1)) n); [|apply IHs; lia].
            destruct (in_dec Nat.eq_dec n1 (enum_p_list p f (S m) n s)).
            {
                destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); [now apply IHs|].
                rewrite (IHs) in *; easy.
            }
            {
                destruct (in_dec Nat.eq_dec n1 (enum_p_list p f m n s)); rewrite <- IHs; cbn in *; try lia; try easy.
                assert (length (enum_p_list p f (S m) n s) <= m) by lia.
                specialize (IHs H0) as [?H _].
                specialize (H1 n1 i).
                easy.
            }
        }
    }
Qed.

Lemma enum_p_m_eq_length (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    length (enum_p_list p f (S m) n s) <= m -> length (enum_p_list p f m n s) = length (enum_p_list p f (S m) n s).
Proof.
    intros.
    assert (H0 := enum_p_m_equiv p f m n s H).
    now apply (NoDup_equiv_length_eq Nat.eq_dec _ _ (enum_p_list_NoDup p f m n s) (enum_p_list_NoDup p f (S m) n s)).
Qed.

Lemma enum_p_m_length' (p : nat -> Prop) (f : nat -> option nat) (n s : nat) :
    forall m m', m' >= m -> length (enum_p_list p f m' n s) = m' -> length (enum_p_list p f m n s) = m.
Proof.
    intros.
    induction m'.
    { assert (m = 0) as -> by lia. assert (H1 := enum_p_list_length p f 0 n s). lia. }
    {
        assert (m' >= m \/ S m' = m) as [|] by lia.
        - apply enum_p_m_step_length in H0. apply IHm'; easy.
        - now rewrite <- H1. 
    }
Qed.

Lemma enum_p_m_length (p : nat -> Prop) (f : nat -> option nat) (n s : nat) :
    forall m' m, length (enum_p_list p f m' n s) >= m -> length (enum_p_list p f m n s) = m.
Proof.
    intros.
    assert (m' >= m) by (pose (enum_p_list_length p f m' n s); lia).
    induction m'.
    { assert (m = 0) as -> by lia. assert (H1 := enum_p_list_length p f 0 n s). lia. }
    {
        assert (H1 := enum_p_list_length p f (S m') n s).
        assert (m = S m' \/ m <= m') as [->|] by lia; [lia|].
        assert (length (enum_p_list p f m' n s) = length (enum_p_list p f (S m') n s) \/ length (enum_p_list p f m' n s) = m') as [|].
        {
            assert (length (enum_p_list p f (S m') n s) = S m' \/ length (enum_p_list p f (S m') n s) <= m') as [|] by lia.
            { right. apply enum_p_m_step_length. easy. }
            { left. apply enum_p_m_eq_length. easy. }
        }
        {
            apply IHm'; lia.
        }
        {
            apply (enum_p_m_length' p f n s m m'); [easy|].
            easy.
        }
    }
Qed.

Fact enum_p_m0_nil (p : nat -> Prop) (f : nat -> option nat) (n s : nat) :
    enum_p_list p f 0 n s = nil.
Proof.
    assert (length (enum_p_list p f 0 n s) = 0) by (pose (enum_p_list_length p f 0 n s); lia).
    destruct (enum_p_list p f 0 n s); [easy|].
    now cbn in H.
Qed.

Lemma enum_p_m_step_length_iff (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    length (enum_p_list p f (S m) n s) = S m \/ length (enum_p_list p f (S m) n s) = m <-> length (enum_p_list p f m n s) = m.
Proof.
    split; intros.
    {
        destruct H; [now apply enum_p_m_step_length|].
        destruct (enum_p_m_Sm p f n s m) as (L & ?H & ?H & ?H).
        assert (H3 := NoDup_equiv_length_eq Nat.eq_dec (enum_p_list p f (S m) n s) (L ++ enum_p_list p f m n s) (enum_p_list_NoDup p f (S m) n s) H2 H1).
        assert (H4 := enum_p_list_length p f m n s).
        destruct L as [|x [|]]; cbn in *; try lia.
        rewrite enum_p_m_eq_length; lia.
    }
    {
        assert (H0 := enum_p_list_length p f (S m) n s).
        assert (length (enum_p_list p f (S m) n s) = S m \/ length (enum_p_list p f (S m) n s) = m \/ length (enum_p_list p f (S m) n s) < m) as [|[|]] by lia; [lia|lia|].
        assert (length (enum_p_list p f (S m) n s) <= m) by lia.
        assert (H3 := enum_p_m_eq_length p f m n s H2).
        lia.
    }
Qed.

Lemma enum_p_m_step_incl (p : nat -> Prop) (f : nat -> option nat) (n : nat) :
    forall s m, incl (enum_p_list p f m n s) (enum_p_list p f (S m) n s).
Proof.
    induction s; intros m x ?H.
    {
        unfold enum_p_list in *.
        destruct (f 0) as [y|] eqn:?H; [|destruct H].
        destruct (Nat.eq_dec (length (encode y)) n), m; easy.
    }
    {
        cbn in *.
        destruct (Nat.eq_dec (length (enum_p_list p f (S m) n s)) (S m)).
        {
            assert (H1 := enum_p_m_step_length p f m n s e).
            destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m); [|lia]; clear e0.
            now apply IHs.
        }
        {
            destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m).
            {
                destruct (f (S s)); [|now apply IHs].
                destruct (Nat.eq_dec (length (encode n1)) n); [|now apply IHs].
                destruct (in_dec Nat.eq_dec n1 (enum_p_list p f (S m) n s)); [now apply IHs|].
                right.
                now apply IHs.
            }
            {
                destruct (f (S s)); [|now apply IHs].
                destruct (Nat.eq_dec (length (encode n2)) n); [|now apply IHs].
                destruct (in_dec Nat.eq_dec n2 (enum_p_list p f (S m) n s)), (in_dec Nat.eq_dec n2 (enum_p_list p f m n s)).
                { now apply IHs. }
                {
                    destruct H as [->|].
                    { exact i. }
                    { now apply IHs. }
                }
                { right. now apply IHs. }
                {
                    destruct H as [->|].
                    { now left. }
                    { right. now apply IHs. }
                }
            }
        }
    }
Qed.

Lemma enum_p_m_mono_incl (p : nat -> Prop) (f : nat -> option nat) (n s : nat) :
    forall m' m, m' >= m -> incl (enum_p_list p f m n s) (enum_p_list p f m' n s).
Proof.
    intros; induction m'.
    {
        assert (m = 0) as -> by lia.
        easy.
    }
    {
        destruct m.
        {
            intros x ?H.
            rewrite (enum_p_m0_nil p f n s) in H0.
            destruct H0.
        }
        {
            assert (m' = m \/ m' >= S m) as [<-|] by lia; [easy|].
            specialize (IHm' H0).
            apply (incl_transitive _ (enum_p_list p f m' n s) _ IHm').
            apply enum_p_m_step_incl.
        }
    }
Qed.

Lemma enum_p_list_correct (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    enumerator f p -> forall s', s' <= s -> forall y, f s' = Some y -> length(encode y) = n ->
    In y (enum_p_list p f m n s) \/ length (enum_p_list p f m n s) = m /\ m <= s.
Proof.
    intros.
    induction s.
    {
        assert (s' = 0) as -> by lia.
        unfold enum_p_list.
        rewrite H1.
        destruct (Nat.eq_dec (length (encode y)) n); [|contradiction].
        destruct m; [right|left]; cbn.
        all: auto.
    }
    {
        assert (s' <= s \/ s' = S s) as [|] by lia.
        {
            specialize (IHs H3) as [|].
            { left. apply enum_p_list_incl_step. easy. }
            { right; split; [|lia]. apply (enum_p_list_max_length p f m n s); [lia|easy]. }
        }
        {
            assert (length (enum_p_list p f m n s) < m \/ length (enum_p_list p f m n s) = m) as [|] by (pose (enum_p_list_length p f m n s); lia).
            {
                left.
                unfold enum_p_list; fold enum_p_list.
                destruct (Nat.eq_dec (length (enum_p_list p f m n s)) m).
                - assert (H5 := enum_p_list_mono_length p f m n s (S s)). lia.
                -  rewrite -> H3 in *; clear H3.
                   rewrite H1.
                   destruct (Nat.eq_dec (length (encode y)) n) as [_|]; [|lia].
                   destruct (in_dec Nat.eq_dec y (enum_p_list p f m n s)); [easy|].
                   now left.
            }
            {
                assert (m <= S s \/ m > S s) as [|] by lia.
                - right; apply conj; [|easy].
                  apply enum_p_list_max_length with (s := s).
                  all: lia.
                - assert (H6 := enum_p_list_length_s p f m n s).
                  lia.
            }
        }
    }
Qed.

Lemma enum_p_list_exists (p : nat -> Prop) (f : nat -> option nat) (m n : nat) :
    enumerator f p -> forall L, NoDup L /\ length L = m /\ (forall x : nat, In x L -> compose length encode x = n /\ p x) ->
        exists s, length (enum_p_list p f m n s) = m.
Proof.
    intros ?H L (?H & ?H & ?H).
    assert (forall x : nat, In x L -> p x) as tmp.
    { intros. now apply H2. }
    destruct (enumerator_list_NoDup p f H L H0 tmp) as [L' [?H ?H]]; clear tmp.
    exists (list_numbers.max_list_with (fun x => x) L').
    apply (enum_p_m_length p f n (list_numbers.max_list_with (fun x => x) L') (S(list_numbers.max_list_with (fun x : nat => x) L'))).
    rewrite <- H1.
    apply pigeonhole_length; [lia|easy|].
    enough (forall a, incl (firstn a L) (enum_p_list p f (S(list_numbers.max_list_with (fun x => x) L')) n (list_numbers.max_list_with (fun x => x) L'))).
    {
        specialize (H5 (length L)).
        rewrite firstn_all in H5. 
        easy.
    }
    induction a; intros x ?H.
    { rewrite firstn_O in H5. destruct H5. }
    {
        assert (length L <= a /\ length L <= S a \/ length L > a /\ length L >= S a) as [[?H ?H]|[?H ?H]] by lia.
        {
            rewrite (list.take_ge L (S a) H7) in H5.
            rewrite (list.take_ge L a H6) in IHa.
            apply (IHa x H5).
        }
        {
            apply (firstn_In x 0) in H5 as [|]; [| |lia].
            { now apply IHa. }
            {
                specialize (H2 _ (nth_In L 0 H6)) as [?H ?H].
                rewrite <- H5 in *.
                destruct H4 as [?H _].
                specialize (H4 (Some x)).
                assert (In (Some x) (map Some L)).
                {
                    apply in_map_iff.
                    exists x; split; [easy|].
                    rewrite H5.
                    now apply nth_In.
                }
                specialize (H4 H9).
                apply in_map_iff in H4 as [y [?H ?H]].
                assert (H11 := enum_p_list_correct p f (S(list_numbers.max_list_with (fun x0 : nat => x0) L')) n (list_numbers.max_list_with (fun x0 : nat => x0) L') H y (max_list_with_spec y L' id H10) x H4 H2).
                destruct H11 as [|[?H ?H]].
                - unshelve eassert (H12 := enum_p_list_incl p f (S(list_numbers.max_list_with (fun x0 : nat => x0) L')) n (list_numbers.max_list_with (fun x0 : nat => x0) L') (list_numbers.max_list_with (fun x0 : nat => x0) L') _); [lia|].
                  now apply H12.
                - lia.  
            }
        }
    }
Qed.

Lemma enum_p_list_least (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    m < 2^n -> {x : nat | mu_nat.least (fun x => ~ In x (enum_p_list p f m n s) /\ length(encode x) = n) 0 x }.
Proof.
    intros.
    apply mu_nat.mu_nat_dep_least.
    {
        intros x.
        destruct (in_dec Nat.eq_dec x (enum_p_list p f m n s)); [right;easy|].
        destruct (Nat.eq_dec (length (encode x)) n); [|right;easy].
        left.
        easy.
    }
    {
        assert (length (enum_p_list p f m n s) < 2^n) by (pose (enum_p_list_length p f m n s); lia).
        assert (H1 := enum_p_list_sat_len_n p f m n s).
        assert (forall x1 x2 : nat, x1 <> x2 \/ ~ x1 <> x2) as temp by lia.
        assert (length (map decode (n_list n)) > length (enum_p_list p f m n s)).
        {
            rewrite map_length.
            rewrite n_list_length.
            assert (H3 := enum_p_list_length p f m n s).
            lia.
        }
        destruct (pigeonhole (map decode (n_list n)) (enum_p_list p f m n s) temp (map_n_list_NoDup n) H2) as [x ?H]; clear temp.
        exists x.
        apply conj; [easy|].
        destruct H3 as [H3 _].
        apply in_map_iff in H3 as [l [<- H3]].
        rewrite encodeDecode.
        apply n_list_In.
        exact H3.
    }
Qed.

Lemma enum_p_list_option_least (p : nat -> Prop) (f : nat -> option nat) (m n s : nat) :
    {o : option nat | (m < 2^n  /\ length (enum_p_list p f m n s) = m  /\ if o is Some x then mu_nat.least (fun x => ~ In x (enum_p_list p f m n s) /\ length(encode x) = n) 0 x else False)
                   \/ (~m < 2^n \/ length (enum_p_list p f m n s) < m) /\ o = None}.
Proof.
    intros.
    assert ({length (enum_p_list p f m n s) < m} + {length (enum_p_list p f m n s) = m}) as [|] by (pose enum_p_list_length; now apply le_lt_eq_dec).
    {
        exists None.
        right; intuition.
    }
    {
        destruct (lt_dec m (2 ^ n)) as [H|]; [|exists None; right; intuition].
        exists (Some (proj1_sig (enum_p_list_least p f m n s H))).
        left.
        apply conj; [easy|apply conj]; [easy|].
        destruct (enum_p_list_least p f m n s H) as [l ?H].
        cbn.
        exact H0.
    }
Qed.

Lemma enum_p_list_option_exists (p : nat -> Prop) (f : nat -> option nat) (n : nat) :
    enumerator f p -> forall x (H : 2 ^ n - x < 2^n) L, NoDup L /\ length L = 2 ^ n - x /\ (forall x : nat, In x L -> compose length encode x = n /\ p x) ->
        exists s, option.is_Some (proj1_sig (enum_p_list_option_least p f (2 ^ n - x) n s)).
Proof.
    intros.
    destruct (enum_p_list_exists p f (2 ^ n - x) n H L H1) as [s ?H].
    exists s.
    destruct (enum_p_list_option_least p f (2 ^ n - x) n s) as [y [(?H & ?H & ?H)|]]; [|lia].
    destruct y; [|contradiction].
    exists n0.
    now cbn.
Qed.

Lemma enum_p_list_option_least_monotonic (p : nat -> Prop) (f : nat -> option nat) (m n : nat) :
    monotonic (fun s => proj1_sig (enum_p_list_option_least p f m n s)).
Proof.
    intros s x H s' H0.
    destruct (enum_p_list_option_least p f m n s) as [?x [(?H & ?H & ?H)|[?H ?H]]], (enum_p_list_option_least p f m n s') as [?x [(?H & ?H & ?H)|[?H ?H]]]; cbn in *; try congruence.
    {
        destruct x1; [|contradiction].
        rewrite H in H3.
        f_equal.
        destruct (enum_p_list_equiv p f m n s s') as [?H ?H]; [lia|].
        unshelve eapply (least_unique n0 x _ H3); destruct H6 as (?H & (?H & ?H) & ?H).
        repeat apply conj; [lia| |lia|]; intuition.
    }
    {
        exfalso.
        enough (length (enum_p_list p f m n s') >= length (enum_p_list p f m n s)) by lia.
        apply pigeonhole_length.
        - lia.
        - apply enum_p_list_NoDup.
        - apply (enum_p_list_incl p f m n s s' H0).
    }
Qed.

Fact decode_v_lt_pow2 (d : nat) (v_prefixed: list bool) :
    2 ^ (length v_prefixed + 2 * d + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed)) < 2 ^ (length v_prefixed + 2 * d + 2).
Proof.
    enough (2 ^ (length v_prefixed + 2 * d + 2) <> 0) by lia.
    now apply Nat.pow_nonzero.
Qed.

Lemma R_length_min c :
    LEM -> univ c -> exists d, forall k l', NoDup l' ->
    (forall x : nat, In x l' <-> R c x /\ In x (map decode (n_list k))) -> length l' >= (2^k) / d.
Proof.
    intros xm H.
    enough (exists f : nat -> nat -> option nat, (forall x, monotonic (f x)) /\ forall d, 
        forall v, let n := (length v) + 2*d+2 in (exists z s, f(decode((list.replicate d false) ++ true :: v)) s = Some z /\ (compose length encode) z = n /\ exists L : list nat, NoDup L /\ length L = 2^n - S(decode (skipn (S(num_first_false v)) v)) /\ ~ In z L /\ forall x, In x L -> (compose length encode) x = n /\ nonR c x)
                                              \/ (forall s, f(decode((list.replicate d false) ++ true :: v)) s = None /\ ~ exists L : list nat, NoDup L /\  length L = 2^n - S(decode (skipn (S(num_first_false v)) v)) /\  forall x, In x L -> (compose length encode) x = n /\ nonR c x)).
    {
        destruct H0 as (f & H0 & H1).
        destruct (PCT f H0) as [c' H2].
        destruct (InvarianceTheorem c c' H) as [d H3].
        exists (2^(2*d+2)).
        intros.
        specialize (H1 d).
        enough (~ length l' < 2 ^ k / (2^(2*d+2))) by lia.
        intro.
        unshelve eassert (H7 := R_non_empty c k l' _ H H5); [intro; destruct (xm (exists n : nat, f0 n = true)); easy|].
        unshelve eassert (H8 := pow_div_ge_1 k (2 * d + 2) _); [lia|].
        specialize (H1 (list.replicate ((k - 2 * d - 2) - S((compose length encode) (length l' - 1))) false ++ true::(encode (length l' - 1)))).
        assert (S(length (encode (length l' - 1))) <= k - (d + d) - 2) as H_k.
        {
            rewrite <- Nat.pow_sub_r in H6; [|lia|lia].
            cbn in H6, H8.
            unshelve eassert (H10 := pow2_length_encode (k - (d + (d + 0) + 2)) (length l' - 1) _).
            all: lia.
        }
        assert (length (list.replicate (k - 2 * d - 2 - S (compose length encode (length l' - 1))) false ++ true :: encode (length l' - 1)) + 2 * d + 2 = k).
        {
            cbn.
            rewrite app_length, list.replicate_length, Nat.add_0_r.
            rewrite Nat.sub_add; [lia|].
            cbn.
            easy.
        } 
        rewrite H9 in H1.
        cbn in H1.
        destruct H1.
        2:{
            specialize (H1 0) as [_ H1].
            apply H1.
            rewrite first_false_replicate, Nat.add_0_r, skipn_replicate_app_cons, decodeEncode.
            eexists (list.list_difference (map decode (n_list k)) l'); repeat apply conj.
            {
                apply base.NoDup_ListNoDup, list.NoDup_list_difference, base.NoDup_ListNoDup.
                apply Injective_map_NoDup; [apply decode_injective|apply n_list_NoDup].
            }
            {
                rewrite list_difference_noDup_length.
                - rewrite map_length, n_list_length. lia.
                - apply Injective_map_NoDup; [apply decode_injective|apply n_list_NoDup].
                - exact H4.
                - intros x ?H. apply H5. exact H10.
            }
            {
                intros.
                apply base.elem_of_list_In, list.elem_of_list_difference in H10 as [?H ?H].
                apply base.elem_of_list_In in H10.
                assert (~ In x l').
                { intro. apply base.elem_of_list_In in H12. contradiction. }
                clear H11.
                apply conj.
                {
                    apply in_map_iff in H10 as [y [<- ?H]].
                    rewrite encodeDecode.
                    now apply n_list_In.
                }
                {
                    apply R_nonR.
                    { intro. destruct (xm (exists n : nat, f0 n = true)); tauto. }
                    {
                        intro.
                        apply H12, H5.
                        easy.
                    }
                }
            }
        }
        destruct H1 as (?z & ?s & ?H & ?H & L & ?H & ?H & ?H & ?H).
        rewrite first_false_replicate, skipn_replicate_app_cons, decodeEncode in H12.
        assert (exists s', T c'
        (decode (list.replicate d false ++ true  :: list.replicate (k - (d + (d + 0)) - 2 - S (length (encode (length l' - 1))))
                 false ++ true :: encode (length l' - 1))) s' = Some z) as [s' ?H].
        {
            specialize (H2 (decode (list.replicate d false ++ true :: list.replicate (k - (d + (d + 0)) - 2 - S (length (encode (length l' - 1)))) false ++ true :: encode (length l' - 1))) z) as [_ ?H].
            assert (exists s : nat, T c' (decode (list.replicate d false ++ true :: list.replicate (k - (d + (d + 0)) - 2 - S (length (encode (length l' - 1)))) false ++ true :: encode (length l' - 1))) s = Some z) as [?s ?H] by eauto.
            now exists s0.
        }
        apply (N_imp (exists k : nat, kol c z k) (univ_exists_kol c H z)); intros [kc ?H].
        apply (N_imp _ (exists_kol_le c' (decode (list.replicate d false ++ true :: list.replicate
              (k - (d + (d + 0)) - 2 - S (length (encode (length l' - 1))))
              false ++ true :: encode (length l' - 1))) z s' H15)); intros (kc' & ?H & ?H).
        rewrite encodeDecode in H18.
        repeat (rewrite app_length, list.replicate_length in H18; cbn in H18).
        specialize (H3 z kc kc' H16 H17).
        assert (kc < k) by lia. (* Follows from H3 and (H18 : kc' <= k - d - 1) *)
        apply H13.
        assert (forall x : nat, In x L <-> length (encode x) = k /\ nonR c x).
        {
            split; [now apply H14|]; intros [?H%n_list_In ?H%R_nonR1].
            assert (forall x, In (encode x) (n_list k) -> In x l' \/ In x L). (* TODO : auslagern *)
            {
                intros.
                apply or_comm, in_app_or.
                apply (NoDup_partition Nat.eq_dec (map decode (n_list k)) L l' (Injective_map_NoDup (decode_injective) (n_list_NoDup k)) H11 H4).
                - intros a ?H.
                    apply in_map_iff.
                    exists (encode a); apply conj; [apply decodeEncode|].
                    apply n_list_In, H14, H23.
                - intros a ?H.
                    apply H5, H23.
                - intros a [?H%H14 ?H%H5].
                    now apply (R_nonR_contradiction c a).
                - rewrite map_length, n_list_length.
                    rewrite H12.
                    enough (2 ^ k = 2 ^ k - length l' + length l') by lia.
                    apply eq_sym, Nat.sub_add.
                    enough (2 ^ k / 2 ^ (2 * d + 2) <= 2^k) by lia.
                    rewrite <- Nat.div_1_r.
                    apply Nat.div_le_compat_l, conj; [constructor|].
                    assert (H27 := Nat.pow_nonzero 2 (2 * d + 2)).
                    lia.
                - apply in_map_iff.
                    exists (encode x0); split; [apply decodeEncode|easy].
            }
            specialize (H20 x H21) as [|].
            { apply H5 in H20. easy. }
            { exact H20. }
        }
        apply H20, conj.
        { exact H10. }
        {
            destruct H16 as (?i & ?s & ?H & ?H & _).
            exists i, s0.
            apply conj; [exact H16|].
            rewrite H21, H10.
            exact H19.   
        }
    }
    {
        destruct (nonR_enumerator c H) as [g ?H].
        evar (f : nat -> nat -> option nat).
        exists f.
        Unshelve.
        2:{
            intros x s.
            set (num_first_false (encode x)) as d.
            set (length (skipn (S(num_first_false (encode x))) (encode x)) + 2*d + 2) as n.
            set (skipn (S(num_first_false (encode x))) (encode x)) as v_prefixed.
            set (skipn (S(num_first_false v_prefixed)) v_prefixed) as v.
            apply (proj1_sig (enum_p_list_option_least (nonR c) g (2^n - S(decode v)) n s)).
        }
        {
            apply conj.
            {
                intros x s y ?H s' ?H.
                unfold f in *.
                apply (enum_p_list_option_least_monotonic (nonR c) g _ _ s y H1 s' H2).
            }
            {
                intros d v_prefixed n.
                destruct (xm (exists z s : nat, f (decode (list.replicate d false ++ true :: v_prefixed)) s = Some z)).
                {
                    left.
                    destruct H1 as (z & s & ?H).
                    exists z, s.
                    repeat apply conj; [easy| |].
                    {
                        unfold f in H1; rewrite encodeDecode, first_false_replicate, skipn_replicate_app_cons in H1.
                        destruct (enum_p_list_option_least (nonR c) g (2 ^ (length v_prefixed +  2 * d + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed : list bool))) (length v_prefixed +  2 * d + 2) s).
                        cbn in H1 |- *.
                        destruct x; [inversion H1; clear H1|congruence].
                        destruct o as [(_ & _ & (_ & [_ ?H] & _))|[_ ?H]]; [|congruence].
                        unfold n.
                        intuition.
                    }
                    {
                        unfold f in H1; rewrite encodeDecode, first_false_replicate, skipn_replicate_app_cons in H1.
                        destruct (enum_p_list_option_least (nonR c) g (2 ^ (length v_prefixed + 2 * d + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed))) (length v_prefixed + 2 * d + 2) s).
                        cbn in H1 |- *.
                        destruct x; [inversion H1; clear H1|congruence].
                        destruct o as [(_ & ?H & (_ & [?H _] & _))|[_ ?H]]; [|congruence].
                        unfold n.
                        exists ((enum_p_list (nonR c) g (2 ^ (length v_prefixed + (d + (d + 0)) + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed))) (length v_prefixed + (d + (d + 0)) + 2) s)); repeat apply conj.
                        { apply enum_p_list_NoDup. }
                        { apply H1. }
                        { intro. rewrite H3 in H2. now apply H2. }
                        {
                            split.
                            { now apply (enum_p_list_sat_len_n (nonR c) g (2 ^ (length v_prefixed + (d + (d + 0)) + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed))) (length v_prefixed + (d + (d + 0)) + 2) s). }
                            { now apply (enum_p_list_sat_p (nonR c) (2 ^ (length v_prefixed + (d + (d + 0)) + 2) - S(decode (skipn (S (num_first_false v_prefixed)) v_prefixed))) (length v_prefixed + (d + (d + 0)) + 2) s g H0). }
                        }
                    }
                }
                {
                    right; intros.
                    assert (forall s z : nat, f (decode (list.replicate d false ++ true :: v_prefixed)) s <> Some z) by eauto.          
                    apply conj.
                    {
                        intros.
                        specialize (H2 s).
                        destruct (f (decode (list.replicate d false ++ true :: v_prefixed)) s) eqn:?H; [|easy].
                        specialize (H2 n0).
                        contradiction.
                    }
                    {
                        clear H2.
                        intros (L & ?H & ?H & ?H).
                        assert (H7 := enum_p_list_option_exists (nonR c) g n H0 (S (decode (skipn (S (num_first_false v_prefixed)) v_prefixed))) (decode_v_lt_pow2 d v_prefixed) L).
                        specialize (H7 (conj H2 (conj H3 H4))) as [?s [?z ?H]].
                        apply H1.
                        cbv delta [f].
                        exists z, s0.
                        rewrite encodeDecode, first_false_replicate, skipn_replicate_app_cons.
                        exact H5.
                    }
                }
            }
        }
    }
Qed.