From Undecidability.Axioms Require Import axioms.
From Undecidability.Shared Require Import partial Dec.
Require Import Init.Nat Arith.PeanoNat Lia FinFun Program.Basics List.
Import ListNotations.
From Kolmogorov Require Import binaryEncoding preliminaries listFacts preliminaries.

Definition kol (n : nat) (x : nat) (c : nat) : Prop :=
    exists y s, T n y s  = Some x /\ length (encode y) = c /\ (forall y' s, T n y' s = Some x -> length (encode y') >= length (encode y)).

Definition univ (n : nat) :=
    forall f, exists g, forall x, agree (T f x) (T n (decode (g ++ (encode x)))).

Lemma kol_alt c x k :
    kol c x k <-> mu_nat.least (fun k => exists y s, length (encode y) = k /\ T c y s = Some x) 0 k.
Proof.
    split.
    {
        intros (y & s & ?H & ?H & ?H).
        repeat apply conj.
        { lia. }
        { now exists y, s. }
        { 
            intros k' _ (y' & s' & ?H & ?H).
            rewrite <- H0, <- H2.
            exact (H1 y' s' H3).
        }
    }
    {
        intros (_ & (?y & ?s & ?H & ?H) & ?H).
        exists y, s.
        repeat apply conj.
        { exact H0. }
        { exact H. }
        { 
            intros y' s' ?H.
            rewrite H.
            apply (H1 (length (encode y')) (le_0_n (length (encode y')))).
            now exists y', s'.
        }
    }
Qed.

Lemma kol_functional c : 
    forall x kc kc', kol c x kc -> kol c x kc' -> kc = kc'.
Proof.
    intros x kc kc' (y & s & ?H & <- & ?H) (y' & s' & ?H' & <- & ?H').
    specialize (H0 y' s' H').
    specialize (H'0 y s H).
    lia.
Qed.

Lemma InvarianceTheorem (n m : nat) :
    univ n -> exists d, forall x c c', kol n x c -> kol m x c' -> c <= c' + d.
Proof.
    intro.
    specialize (H m) as [p H].
    exists (length p).
    intros.
    destruct H0 as (?y & ?s & ?H & ?H & ?H), H1 as (?y & ?s & ?H & ?H & ?H).
    rewrite <- H2, <- H4.
    specialize (H y0 x) as [H _].
    assert (exists s : nat, T n (decode (p ++ encode y0)) s = Some x) as [?s ?H] by eauto.
    specialize (H3 (decode (p ++ encode y0)) s1 H6).
    apply (Nat.le_trans (length (encode y)) (length (encode (decode (p ++ encode y0)))) (length (encode y0) + length p) H3).
    rewrite encodeDecode.
    rewrite app_length.
    rewrite Nat.add_comm.
    constructor.
Qed.

Lemma univ_upper_bound c f :
    univ c -> exists k, forall x, exists i s, T c i s = Some (f x) /\ length (encode i) <= length (encode x) + k.
Proof.
    intros.
    destruct (CT f) as [c' ?H].
    specialize (H c') as [g ?H].
    exists (length g).
    intros x; specialize (H0 x) as [?s H0]; specialize (H x).
    exists (decode (g ++ encode x)).
    specialize (H (f x)) as [H _].
    assert (exists s : nat, T c (decode (g ++ encode x)) s = Some (f x)) as [?s ?H] by eauto.
    exists s0.
    apply conj; [intuition|].
    rewrite encodeDecode, app_length, Nat.add_comm.
    reflexivity.
Qed.

Lemma exists_univ :
    exists n, univ n.
Proof.
    intros.
    unfold univ.
    assert (H := PCT (fun x s => let size := num_first_false (encode x) in let program := decode (firstn size (skipn (S size) (encode x))) in let input := decode (skipn (S(2 * size)) (encode x)) in T program input s)).
    cbv beta in H.
    assert ((forall x : nat,
        monotonic
            (fun s : nat =>
            let size := num_first_false (encode x) in
            let program := decode (firstn size (skipn (S size) (encode x))) in
            let input := decode (skipn (S (2 * size)) (encode x)) in
            T program input s))) by (intros; apply T_mono).      
    specialize (H H0) as [c H]; clear H0.
    exists c.
    intros.
    exists (list.replicate (length (encode f)) false ++ true :: encode f).
    intros.
    specialize (H (decode ((list.replicate (length (encode f)) false ++ true :: encode f) ++ encode x))).
    cbn in H.
    assert (firstn (length (encode f))(skipn (S (length (encode f)))(list.replicate (length (encode f)) false ++ true :: encode f ++ encode x)) = encode f).
        {
            change (S (length (encode f))) with (1 + (length (encode f))).
            rewrite Nat.add_comm.
            rewrite <- list.drop_drop.
            rewrite skipn_replicate_app.
            cbn; unfold skipn.
            now rewrite list.take_app.
        }
    assert ((skipn (S (length (encode f) + length (encode f)))(list.replicate (length (encode f)) false ++ true :: encode f ++ encode x)) = encode x).
        {
            change (S (length (encode f) + length (encode f))) with (1 + (length (encode f) + length (encode f))).
            rewrite Nat.add_assoc, Nat.add_comm, <- list.drop_drop, skipn_replicate_app.
            cbn.
            now rewrite list.drop_app.
        }
    rewrite encodeDecode, <- app_assoc, <- app_comm_cons, Nat.add_0_r in H.
    rewrite (first_false_replicate) in *.
    rewrite H0, H1, decodeEncode in H.
    rewrite decodeEncode in H.
    rewrite <- app_assoc.
    apply agree_ref.
    apply H.
Qed.

Lemma exists_kol n i x :
    forall s, T n i s = Some x -> ~~ exists c, kol n x c.
Proof.
    intros.
    assert (~~ exists j, mu_nat.least (fun j => exists s, T n j s = Some x) 0 j).
    {
        apply constructive_least_witness.
        apply DN_intro.
        exists i, s.
        easy.
    }
    apply (DN_imp H0); intros [j H1].
    apply DN_intro.
    exists (length (encode j)).
    destruct H1 as (_ & (?s & ?H) & ?H).
    exists j, s0.
    repeat apply conj; [easy|easy|].
    intros.
    apply encode_monotone.
    apply (H2 y' (Nat.le_0_l y')).
    now exists s1.
Qed.

Lemma univ_exists_kol c :
    univ c -> forall x, ~~ exists k, kol c x k.
Proof.
    intros.
    destruct (CT (fun x => x)) as [c' ?H].
    specialize (H0 x) as [s ?H].
    specialize (H c') as [g ?H].
    specialize (H x x) as [H _].
    assert (exists s : nat, T c (decode (g ++ encode x)) s = Some x) as [?s ?H] by eauto.
    now apply (exists_kol c (decode (g ++ encode x)) x s0).
Qed.

Lemma exists_kol_le n i x :
    forall s, T n i s = Some x -> ~~ exists c, kol n x c /\ length(encode i) >= c.
Proof.
    intros.
    apply (DN_imp (exists_kol n i x s H)); intros [c ?H].
    apply DN_intro.
    exists c.
    apply conj; [exact H0|].
    destruct H0 as (?i & ?s & ?H & <- & ?H).
    exact (H1 i s H).
Qed.

Lemma upper_bound n f:
    univ n -> exists c, forall m, forall k, kol n (f m) k -> k <= length (encode m) + c.
Proof.
    intros.
    destruct (univ_upper_bound n f H) as [d H2].
    exists d; intros m kc (i & s & ?H & <- & ?H).
    specialize (H2 m) as (i' & s' & ?H & ?H).
    specialize (H1 i' s' H2).
    lia.
Qed.