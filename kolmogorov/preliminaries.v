From Undecidability.Axioms Require Import axioms.
From Undecidability.Shared Require Import partial Dec mu_nat.
From Undecidability.Synthetic Require Import FinitenessFacts Definitions.
Require Import Init.Nat Arith.PeanoNat Lia FinFun Program.Basics List.
Import ListNotations.
From Kolmogorov Require Import binaryEncoding listFacts.

Lemma DN_LM (Q P : Prop): ((Q \/ ~ Q) -> ~~P) -> ~~P. Proof. tauto. Qed.
Lemma DN_imp {P Q : Prop} : ~~Q -> (Q -> ~~ P) -> ~~ P. Proof. tauto. Qed.
Lemma DN_intro (P : Prop) : P -> ~~ P. Proof. tauto. Qed.

Lemma N_imp (Q : Prop) : ~~Q -> (Q -> False) -> False. Proof. tauto. Qed.

(* Result by Yannick Forster *)
Lemma p_sublist :
    forall X, forall p : X -> Prop, forall l, ~~ exists l', forall x, In x l' <-> p x /\ In x l.
Proof.
  intros X p l. induction l as [ | x l IH].
  - eapply DN_intro. exists nil. firstorder.
  - eapply (DN_imp IH); clear IH. intros [l' IH].
    eapply (DN_LM (p x)). intros [H | H]; eapply DN_intro.
    + exists (x :: l'). now firstorder subst.
    + exists l'. now firstorder subst.
Qed.

Fact p_sublist_NoDup :
    forall X, eq_dec X -> forall p : X -> Prop, forall l, ~~ exists l', NoDup l' /\ forall x, In x l' <-> p x /\ In x l.
Proof.
    intros X Xdec p l.
    apply (DN_imp (p_sublist X p l)); intros [l1 H].
    apply DN_intro.
    exists (nodup Xdec l1).
    split; [apply NoDup_nodup|].
    split; intros.
    {
        apply H.
        now apply (nodup_In Xdec).
    }
    {
        destruct (H x) as [_ ?H].
        specialize (H1 H0).
        now apply (nodup_In Xdec).
    }
Qed.

(* modified version of proof from MPCCT script by Gert Smolka *)
Lemma constructive_least_witness p : ~~ ex p -> ~~ ex (mu_nat.least p 0).
Proof.
    intros; apply (DN_imp H); clear H; intros [y H].
    enough (forall (n k : nat), p(n+k) -> (forall n, p n -> n >= k) -> ~~(exists y, mu_nat.least p 0 y)).
        {
            apply (H0 y 0).
            { now rewrite Nat.add_0_r. }
            { lia. }
        }
        {
            induction n; intros.
            {
                apply DN_intro.
                exists k.
                repeat split.
                { lia. }
                { now cbn in H0. }
                { intros. now apply H1. }
            }
            {
                apply (DN_LM (p (k))).
                intros [|].
                {       
                    apply DN_intro.             
                    exists k.
                    repeat split.
                    { lia. }
                    { easy. }
                    { intros. now apply H1. }
                }
                {
                    apply (IHn (S k)).
                    { rewrite Nat.add_succ_r. now cbn in H0. }
                    {
                        intros.
                        specialize (H1 n0 H3).
                        enough (n0 <> k) by lia.
                        intro.
                        rewrite H4 in H3.
                        contradiction.
                    }
                }
            }
        }
Qed.

Lemma p_infinite_unbounded (q : nat -> Prop) :
    ~ exhaustible q -> forall m, ~~ exists n : nat, q n /\ (length (encode n)) > m.
Proof.
    intros.
    assert (forall x1 x2 : nat, x1 = x2 \/ x1 <> x2) by lia.
    destruct (non_finite_spec q H0) as [?H _]; clear H0.
    specialize (H1 H).
    destruct (l_encode_unbounded m) as [x ?H].
    apply (DN_imp (H1 (map decode (le_n_list (length (encode x)))))); clear H1; intros (y & ?H & ?H).
    apply DN_intro.
    exists y; split; [easy|].
    enough (~ (length (encode y)) <= m) by lia.
    intro.
    apply H2.
    apply in_map_iff; exists (encode y).
    split; [now apply decodeEncode|].
    apply le_n_list_In.
    lia.
Qed.

Lemma p_enumerable_infinite_unbounded (q : nat -> Prop) (f : nat -> option nat) :
    enumerator f q -> ~ exhaustible q -> forall m, ~~ exists n : nat, if f n is Some x then (length (encode x)) > m else False.
Proof.
    intros.
    assert (forall x1 x2 : nat, x1 = x2 \/ x1 <> x2) by lia.
    destruct (non_finite_spec q H1) as [?H _]; clear H1.
    specialize (H2 H0).
    destruct (l_encode_unbounded m) as [x ?H].
    apply (DN_imp (H2 (map decode (le_n_list (length (encode x)))))); clear H2; intros (y & ?H & ?H).
    apply DN_intro.
    apply (H y) in H2 as [n H2].
    exists n.
    rewrite H2.
    enough (~ (length (encode y)) <= m) by lia.
    intro.
    apply H3.
    apply in_map_iff; exists (encode y).
    split; [now apply decodeEncode|].
    apply le_n_list_In.
    lia.
Qed.

Context {model : model_of_computation}.

Definition agree (T : nat -> option nat) (T' : nat -> option nat) := forall a, (exists s, T s = Some a) <-> (exists s, T' s = Some a).

Fact agree_ref T T' : agree T T' -> agree T' T.
Proof.
    intros H a; apply iff_sym, (H a).
Qed.

Axiom SCT : forall f : nat -> nat, exists c, forall x, exists s, T c x s = Some (f x).
Axiom PSCT : (forall (f : nat -> nat -> option nat), (forall x, monotonic (f x)) -> exists c : nat, forall (x : nat), agree (T c x) (f x)).

Lemma monotonic_eq {X : Type} (H : eq_dec X) (f : nat -> option X) :
    monotonic f -> forall n n' x x', f n = Some x -> f n' = Some x' -> x = x'.
Proof.
    intros.
    destruct (H x x'); [easy|].
    assert (n <= n' \/ n' <= n) by lia.
    destruct H3.
    {
        specialize (H0 n x H1 n' H3).
        rewrite H0 in H2.
        now inversion H2.
    }
    {
        specialize (H0 n' x' H2 n H3).
        rewrite H0 in H1.
        now inversion H1.
    }
Qed.

Lemma least_unique {p : nat -> Prop} :
    forall x y, mu_nat.least p 0 x -> mu_nat.least p 0 y -> x = y.
Proof.
    intros x y (?Hx & ?Hx & ?Hx) (?Hy & ?Hy & ?Hy).
    specialize (Hx1 y Hy Hy0); specialize (Hy1 x Hx Hx0).
    lia.
Qed.

Definition ONat_eqb (x y : option nat) := match x, y with Some x, Some y => eqb x y | None, None => true | _, _ => false end.

Lemma ONat_eqb_eq x y :
    ONat_eqb x y = true <-> x = y.
Proof.
    destruct x,y; cbn; try easy.
    split.
    { intros H%Nat.eqb_eq; congruence. }
    { intros [=H]. now apply Nat.eqb_eq. }
Qed.

Lemma ONat_eqb_neq x y :
    ONat_eqb x y = false <-> x <> y.
Proof.
    destruct x,y; cbn; try easy.
    split.
    { intros H%Nat.eqb_neq. intros [=]. contradiction. }
    { intros H. apply Nat.eqb_neq. intro. apply H. now rewrite H0. }
Qed.

Fact pow_div_ge_1 k k' :
    1 < 2 ^ k / 2 ^ k' -> k > k'.
Proof.
    intros.
    enough (~k <= k') by lia; intro.
    unshelve eapply (Nat.pow_le_mono_r_iff 2 k k' _) in H0; [lia|].
    unshelve eassert (H1 := Nat.div_le_mono (2 ^ k) (2 ^ k') (2 ^ k') _ H0).
    { apply Nat.pow_nonzero. lia. }
    rewrite Nat.div_same in H1.
    - lia.
    - apply Nat.pow_nonzero. lia.
Qed.