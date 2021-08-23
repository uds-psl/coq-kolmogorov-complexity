From Undecidability.Synthetic Require Import truthtables.
From Undecidability.Shared Require Import Pigeonhole.
Require Import List Arith Lia FinFun.
From Equations Require Import Equations.
From Kolmogorov Require Import listFacts.
Import ListNotations.

Axiom encode : nat -> list bool.
Axiom decode : list bool -> nat.
Axiom encodeDecode : forall l, encode (decode l) = l.
Axiom decodeEncode : forall n, decode (encode n) = n.
Axiom encode_logarithmic : forall n, length (encode n) <= S(Nat.log2 n).
Axiom encode_monotone : forall x y, x <= y -> length (encode x) <= length (encode y).

Fact encode_monotone2 : forall x y, length (encode x) < length (encode y) -> x < y.
Proof.
    intros.
    enough (~ x >= y) by lia.
    intro.
    enough (length (encode x) >= length (encode y)) by lia.
    now apply encode_monotone.
Qed.

Lemma decode_monotone : forall L L', length L < length L' -> decode L < decode L'.
Proof.
    intros.
    rewrite <- (encodeDecode L), <- (encodeDecode L') in H.
    now apply encode_monotone2 in H.
Qed.

Fact encode_surjective : forall L, exists x, encode x = L.
Proof.
    intros.
    exists (decode L).
    apply encodeDecode.
Qed.

Fact decode_surjective : forall x, exists L, decode L = x.
Proof.
    intros.
    exists (encode x).
    apply decodeEncode.
Qed.

Fact encode_injective : Injective encode.
Proof.
    intros x y H.
    apply (f_equal decode) in H.
    now do 2 rewrite decodeEncode in H.
Qed.

Fact decode_injective : Injective decode.
Proof.
    intros x y H.
    apply (f_equal encode) in H.
    now do 2 rewrite encodeDecode in H.
Qed.

Fact l_encode_unbounded :
    forall n, {m | length (encode m) > n}.
Proof.
    intros.
    exists (decode (list.replicate (S n) true)).
    rewrite encodeDecode.
    rewrite list.replicate_length.
    lia.
Qed.


Fact decode_nil_O : decode [] = 0.
Proof.
    unshelve eassert (H := encode_monotone 0 (decode nil) _); [lia|].
    rewrite encodeDecode in H.
    cbn in H.
    assert (length(encode 0) = 0) by lia.
    apply list.nil_length_inv in H0.
    apply (f_equal decode) in H0.
    rewrite decodeEncode in H0.
    easy.
Qed.


Fixpoint n_list (n : nat) : list (list bool) :=
    match n with
    | 0 => [[]]
    | S n0 =>
	   let L := n_list n0 in
       map (fun x : list bool => false :: x) L ++
       map (fun x : list bool => true :: x) L
    end.

Lemma n_list_In n :
    forall L, length L = n <-> In L (n_list n).
Proof.
    induction n.
    { 
        cbn; intros.
        split.
        { left. destruct L; cbn in *; [|lia]. easy. }
        { intros. destruct H; [|easy]. rewrite <- H. cbn. constructor. }
    }
    {
        intros.
        cbn.
        destruct L.
        {
            cbn.
            split; intros.
            { inversion H. }
            { 
                apply in_app_or in H.
                destruct H.
                all: apply in_map_iff in H.
                all: do 2 destruct H.
                all: inversion H.
            }
        }
        {
            split; intros.
            {
                specialize (IHn L) as [IHn _].
                cbn in H.
                inversion H.
                specialize (IHn H1).
                apply in_or_app.
                destruct b.
                {
                    right.
                    apply in_map_iff.
                    exists L.
                    rewrite H1.
                    easy.
                }
                {
                    left.
                    apply in_map_iff.
                    exists L.
                    rewrite H1.
                    easy.
                }
            }
            {
                specialize (IHn L) as [_ IHn].
                cbn.
                apply eq_S.
                apply IHn.
                apply in_app_or in H.
                destruct H.
                all: apply in_map_iff in H.
                all: do 2 destruct H.
                all: inversion H.
                all: rewrite H3 in H0.
                all: easy.
            }
        }   
    }
Qed.

Lemma n_list_NoDup n :
    NoDup (n_list n).
Proof.
    induction n; cbn.
    {
        repeat constructor.
        intro.
        destruct H.
    }
    {
        apply NoDup_app.
        1,2: apply Injective_map_NoDup.
        1,3: now intros x y [=->].   
        1,2: exact IHn.
        intros x H H0.
        apply in_map_iff in H; apply in_map_iff in H0.
        destruct H as [l1 [?H ?H]], H0 as [l2 [?H ?H]].
        rewrite <- H in H0.
        inversion H0.
    }
Qed.

Lemma map_n_list_NoDup n :
    NoDup (map decode (n_list n)).
Proof.
    apply Injective_map_NoDup; [apply decode_injective|].
    apply n_list_NoDup.
Qed.

Lemma n_list_length n :
    length (n_list n) = 2^n.
Proof.
    induction n; cbn; [easy|].
    rewrite app_length.
    do 2 rewrite map_length.
    lia.
Qed.

Fixpoint le_n_list (n : nat) : list (list bool) :=
    match n with
    | 0 => n_list n 
    | S n' => le_n_list n' ++ n_list n 
    end.

Lemma le_n_list_In n :
    forall L, length L <= n <-> In L (le_n_list n).
Proof.
    induction n.
    { 
        cbn; intros.
        split.
        { left. destruct L; cbn in *; [|lia]. easy. }
        { intros. destruct H; [|easy]. rewrite <- H. cbn. constructor. }
    }
    {
        intros.
        cbn [le_n_list].
        split; intros.
        {
            assert (length L <= n \/ length L = S n) as [|] by lia; apply in_app_iff.
            { left. now apply IHn. }
            { right. now apply n_list_In. }
        }
        {
            apply in_app_iff in H as [|].
            { enough (length L <= n) by lia. now apply IHn. }
            { enough (length L = S n) by lia. now apply n_list_In. }
            }
        }
Qed.

Lemma le_n_list_NoDup n :
    NoDup (le_n_list n).
Proof.
    induction n; cbn [le_n_list].
    {
        repeat constructor.
        intro.
        destruct H.
    }
    {
        apply NoDup_app.
        { apply IHn. }
        { apply n_list_NoDup. }
        {
            intros x H H1.
            apply le_n_list_In in H; apply n_list_In in H1.
            lia.
        }
    }
Qed.

Lemma le_n_list_length n :
    length (le_n_list n) = 2^(S n) - 1.
Proof.
    induction n; [cbn; easy|].
    cbn [le_n_list].
    rewrite app_length.
    rewrite n_list_length, IHn.
    rewrite <- Nat.add_sub_swap.
    {
        f_equal.
        enough (2 * (2 ^ S n) = 2 ^ S (S n)) by lia.
        now cbn.
    }
    {
        rewrite <- (Nat.pow_1_l (S n)) at 1.
        apply (Nat.pow_le_mono_l 1 2 (S n)).
        repeat constructor.
    }
Qed.

Lemma le_n_list_lt_n_list n :
    length (le_n_list n) < length (n_list (S n)).
Proof.
    rewrite le_n_list_length, n_list_length.
    apply Nat.sub_lt.
    {
        rewrite <- (Nat.pow_1_l (S n)) at 1.
        apply (Nat.pow_le_mono_l 1 2 (S n)).
        repeat constructor.
    }
    {
        repeat constructor.
    }
Qed.

Lemma encode_finite :
    forall l, {L | forall x, length (encode x) = l <-> In x L}. 
Proof.
    intros l.
    exists (map decode (n_list l)).
    intros.
    destruct (n_list_In l (encode x)).
    split; intros.
    {   
        apply in_map_iff.
        exists (encode x); split.
        { apply decodeEncode. }
        { tauto. }
    }
    {
        apply H0.
        apply in_map_iff in H1.
        destruct H1 as (y & ?H & ?H).
        apply (f_equal encode) in H1.
        rewrite encodeDecode in H1.
        intuition.
    }
Qed.

Lemma encode_finite_all :
    forall l, {L | forall x, length (encode x) <= l <-> In x L}.
Proof.
    induction l as [|l (L & IH)].
    {
        exists [decode nil].
        split; intros.
        {
            apply le_n_0_eq in H.
            destruct (encode x) eqn:H0.
            { rewrite <- H0, decodeEncode. now constructor. }
            { cbn in H. lia. }
        }
        {
            destruct H; [|easy].
            rewrite <- H, encodeDecode.
            cbn; lia.
        }
    }
    {
        destruct (encode_finite (S l)) as [L' H].
        exists (L++L').
        split; intros.
        {
            apply in_or_app.
            assert (length (encode x) <= l \/ length (encode x) = S l) by lia.
            destruct H1.
            { left. now apply IH. }
            { right. now apply H. }
        }
        {
            specialize (IH x) as [_ IH]; specialize (H x) as [_ H].
            enough (length (encode x) <= l \/ length (encode x) = S l) by lia.
            apply in_app_or in H0.
            destruct H0; intuition.
        }
    }
Qed.

Lemma exp_superlinear :
    forall k, exists n, 2 ^ n > n + k.
Proof.
    induction k.
    {
        exists 1; cbn.
        constructor.
    }
    {
        destruct IHk as [n IH].
        exists (S(S(n))). 
        cbn.
        repeat rewrite Nat.add_0_r.
        assert (forall x, x + x + (x + x) = 4 * x) by lia; rewrite H; clear H.
        rewrite Nat.add_succ_r.
        lia.
    }
Qed.

Lemma l_sublinear:
    ~ exists c, forall n, n <= length (encode n) + c.
Proof.
    intros (?c & ?H).
    assert (H0 := encode_logarithmic).
    assert (forall n, 2^n <= n + S c).
    {
        intros.
        specialize (H (2 ^ n)); specialize (H0 (2 ^ n)).
        rewrite Nat.log2_pow2 in H0.
        all: lia.
    }
    assert (H2 := exp_superlinear).
    specialize (H2 (S c)) as [n ?H].
    specialize (H1 n).
    lia.
Qed.

Lemma le_list n :
    forall y, n > y -> exists L, NoDup L /\ length L = y /\ forall x, In x L -> x <= n.
Proof.
    induction n; intros; [lia|].
    unfold gt, lt in H.
    assert (y < n \/ y = n) as [|] by lia.
    {
        specialize (IHn y H0) as [L (?H & ?H & ?H)].
        exists L; repeat apply conj; [easy|easy|].
        intros.
        enough (x <= n) by lia.
        now apply H3.
    }
    {
        destruct y; cbn.
        {
            exists nil; repeat apply conj.
            - constructor.
            - now cbn.
            - intros _ [].
        }
        {
            destruct (IHn y) as [L (?H & ?H & ?H)]; [lia|].
            exists (S n::L); repeat apply conj.
            - constructor; [intro|easy]. specialize (H3 (S n) H4). lia.
            - cbn; lia.
            - intros. destruct H4; [lia|]. enough (x <= n) by lia. now apply H3.
        }
    }
Qed.

Lemma le_list_encode n :
    forall y, n > y -> exists L, NoDup L /\ length L = y /\ forall x, In x L -> length(encode x) <= length(encode n).
Proof.
    intros.
    destruct (le_list n y H) as [L (?H & ?H & ?H)].
    exists L; repeat apply conj; [easy|easy|].
    intros.
    apply encode_monotone.
    now apply H2.
Qed.

Lemma pow_ge_1 a b :
    a <> 0 -> a^b >= 1.
Proof.
    intros.
    assert (H0 := Nat.pow_le_mono_r a 0 b H).
    rewrite Nat.pow_0_r in H0.
    apply H0.
    lia.
Qed.

Lemma decode_pow2 : forall L, decode L <= 2^S(length L).
Proof.
    intros.
    assert (H := le_n_list_length (length L)).
    assert (H0 := le_n_list_In (length L)).
    enough (~decode L > 2 ^ S (length L)) by lia; intro.
    destruct (le_list_encode (decode L) (2 ^ S (length L)) H1) as (L' & ?H & ?H & ?H).
    assert (incl (map encode L') (le_n_list (length L))).
    {
        intros x ?H.
        apply H0.
        apply in_map_iff in H5 as [y [?H ?H]].
        specialize (H4 y H6).
        rewrite <- H5.
        now rewrite encodeDecode in H4.
    }
    assert (forall x1 x2 : list bool, x1 <> x2 \/ ~ x1 <> x2).
    {
        intros.
        destruct (list_eq_dec Bool.bool_dec x1 x2); tauto.
    }
    assert (length (map encode L') > length (le_n_list (length L))).
    {
        rewrite map_length, H3, H.
        unshelve eassert (H7 := pow_ge_1 2 (S(length L)) _); [lia|].
        lia.
    }
    destruct (pigeonhole (map encode L') (le_n_list (length L)) H6 (Injective_map_NoDup encode_injective H2) H7) as [x [?H ?H]].
    rewrite encodeDecode in H4.
    apply in_map_iff in H8 as [y [<- ?H]].
    specialize (H4 y H8).
    apply H9.
    apply le_n_list_In.
    exact H4.
Qed.


Fact log2_pow2_lt a b :
    a <> 0 -> a < 2^b -> log2 a < log2 (2^b).
Proof.
    intros.
    destruct b; [cbn in * |-; lia|].
    rewrite Nat.log2_pow2; [|lia].
    assert (2 ^ b <= a \/ 2 ^ b > a) as [|] by lia.
    - rewrite (Nat.log2_unique a b).
      all: lia.
    - assert (H2 := Nat.log2_le_mono a (2^b)).
      enough (log2(2^b) < S b) by lia.
      rewrite Nat.log2_pow2.
      all: lia.
Qed.

Lemma In_le_n_list :
    forall x n, decode x < 2^S n - 1 -> In x (le_n_list n).
Proof.
    induction n; intros.
    {
        cbn in *.
        assert (decode x = 0) by lia.
        rewrite <- decode_nil_O in H0.
        apply decode_injective in H0.
        now left.
    }
    {
        assert (decode x < 2 ^ S n - 1 \/ 2 ^ S n - 1<= decode x < 2 ^ S (S n) - 1) as [|] by lia.
        - cbn.
          apply in_app_iff.
          left.
          now apply IHn.
        - apply le_n_list_In.
          enough (~length x > S n) by lia; intro.
          assert (forall y, In y (le_n_list (S n)) -> decode y < decode x).
          {
              intros.
              apply decode_monotone.
              apply le_n_list_In in H2.
              lia.
          }
          unshelve eassert (H3 := lt_length_list' (map decode (le_n_list (S n))) (decode x) _ _).
          + apply Injective_map_NoDup; [apply decode_injective|apply le_n_list_NoDup].
          + intros.
            apply in_map_iff in H3 as (y & <- & ?H).
            now apply H2.
          + rewrite map_length, le_n_list_length in H3.
            lia.
    }
Qed.

Lemma not_In_le_n_list :
    forall x n, ~ In x (le_n_list n) -> decode x >= 2^S n - 1.
Proof.
    intros.
    enough (~decode x < 2 ^ S n - 1) by lia; intro.
    apply H.
    now apply In_le_n_list.
Qed.

Lemma pow2_length_encode : 
    forall k n, n < 2^k - 1 -> length(encode n) <= k - 1.
Proof.
    destruct k; intros.
    - cbn in *.
      assert (n = 0) by lia.
      rewrite <- decode_nil_O in H0.
      rewrite H0, encodeDecode.
      cbn.
      constructor.
    - cbn.
      enough (~length (encode n) > k) by lia.
      intro.
      assert (~In (encode n) (le_n_list k)).
      { intro. apply le_n_list_In in H1. lia. }
      apply not_In_le_n_list in H1.
      rewrite decodeEncode in H1.
      lia.
Qed.