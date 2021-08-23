From Undecidability.Axioms Require Import axioms principles.
Require Import Init.Nat Arith.
From Coq Require Import Lia FinFun Program.Basics.
Require Import List.
Import ListNotations.
From Kolmogorov Require Import binaryEncoding preliminaries listFacts kolmogorov.

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

Lemma kol_list_eq n :
    forall l, ~~ exists L, forall x, kol n x l -> In x L.
Proof.
    intros l.
    enough (forall m, ~~exists L, forall x, In x (firstn m (n_list l)) -> forall s r, T n (decode x) s = Some r -> In r L).
    {
        apply (DN_imp (H (length (n_list l)))); clear H; intros [L H].
        rewrite firstn_all in H.
        apply DN_intro.
        exists L.
        intros x (?p & ?s & ?H & ?H & _).
        apply n_list_In in H1.
        specialize (H (encode p) H1 s x).
        rewrite decodeEncode in H.
        now specialize (H H0).
    }
    {
        induction m.
        {
            apply DN_intro.
            exists nil.
            rewrite firstn_O.
            intros _ [].
        }
        {
            apply (DN_imp IHm); clear IHm; intros [L IH].
            assert (length (n_list l) <= m /\ length (n_list l) <= S m \/ length (n_list l) > m /\ length (n_list l) >= S m) as [[?H ?H]|[?H ?H]] by lia.
            {
                apply DN_intro.
                rewrite (list.take_ge (n_list l) m H) in IH.
                rewrite (list.take_ge (n_list l) (S m) H0).
                now exists L.
            }
            {
                apply (DN_LM (exists s r, T n (decode (nth m (n_list l) [])) s = Some r)).
                intros [(s & r & ?H)|]; apply DN_intro.
                {
                    exists (r::L); intros.
                    destruct (Nat.eq_dec r0 r); [now left|right].
                    rewrite (firstn_app nil) in H2; [|easy].
                    apply in_app_or in H2 as [|[<-|[]]].
                    - now apply (IH x H2 s0 r0).
                    - exfalso.
                      apply n0.
                      exact (monotonic_eq Nat.eq_dec (T n (decode (nth m (n_list l) []))) (T_mono _ _) s0 s r0 r H3 H1).
                }
                {
                    exists L.
                    intros.
                    rewrite (firstn_app nil) in H2; [|easy].
                    apply in_app_or in H2 as [|[<-|[]]].
                    - apply (IH x H2 s r H3).
                    - exfalso; apply H1.
                      exists s, r.
                      exact H3.
                }
            }
        }
    }
Qed.

Lemma kol_list_le n :
    forall l, ~~ exists L, forall l', l' <= l -> forall x, kol n x l' -> In x L.
Proof.
    intros l.
    induction l.
    {
        apply (DN_imp (kol_list_eq n 0)).
        intros [L H].
        apply DN_intro.
        exists L.
        intros.
        assert (l' = 0) by lia.
        rewrite H2 in H1.
        now apply H.
    }
    {
        apply (DN_imp IHl).
        clear IHl; intros [L IH].
        apply (DN_imp (kol_list_eq n (S l))); intros [L' H].
        apply DN_intro.
        exists (L ++ L').
        intros.
        apply in_or_app.
        assert (l' <= l \/ l' = S l) by lia.
        destruct H2.
        {
            specialize (IH l' H2 x H1).
            now left.   
        }
        {
            right.
            rewrite <- H2 in H.
            specialize (H x H1).
            easy.   
        }
    }
Qed.

(* Proof by Gert Smolka *)
Lemma nat_infinite :
    forall L : list nat, exists n, ~(In n L).
Proof.
    enough (forall A, exists n, forall x, In x A -> x < n) as H.
        { intros A. specialize (H A) as [n H]. exists n. intros H1%H. lia. }
    induction A as [|x A IH]; cbn.
     - exists 0. intros x [].
     - destruct IH as [n IH]. exists (S n + x).
    intros y [<-|H%IH]; lia.
Qed.

Lemma kol_unbounded c :
    univ c -> forall m, ~~exists x kc : nat, kol c x kc /\ m <= kc.
Proof.
    intros.
    apply (DN_imp (kol_list_le c m)); intros [L H1].
    destruct (nat_infinite L).
    apply (DN_imp (univ_exists_kol c H x)); intros [kc ?H].
    apply DN_intro.
    exists x, kc.
    apply conj; [exact H2|].
    assert (kc <= m \/ kc >= m) as [|] by lia; [|lia].
    specialize (H1 kc H3 x H2).
    contradiction.
Qed.

Lemma uncomputability n :
    MP -> univ n -> ~(exists f, forall x, kol n x (f x)).
Proof.
    intros mp H [f H1].
    assert (forall m, {x | mu_nat.least (fun x => m <= f x) 0 x}).
    {
        intros.
        apply mu_nat.mu_nat_dep_least.
        {
            intros.
            apply le_dec.
        }
        {
            assert (H2 := kol_unbounded n H m).
            enough (exists n1 : nat, m <=? f n1 = true).
            {
                destruct H0.
                exists x.
                now apply Nat.leb_le.
            }
            {
                apply (mp (fun x => m <=? f x)).
                apply (DN_imp H2); intros (x & kc & ?H & ?H); apply DN_intro.
                rewrite (kol_functional n x kc (f x) H0 (H1 x)) in H3.
                exists x.
                now apply Nat.leb_le.
            }
        }
    }
    assert (forall m, m <= f(proj1_sig (H0 m))).
    {
        intros.
        destruct (proj2_sig (H0 m)) as (_ & ?H & _).
        exact H2. 
    }
    destruct (upper_bound n (fun m => proj1_sig (H0 m)) H) as [c ?H].
    assert (forall m, m <= (length (encode m)) + c).
    {
        intros.
        specialize (H2 m); specialize (H3 m).
        specialize (H1 (proj1_sig (H0 m))); specialize (H3 (f (proj1_sig (H0 m)))).
        specialize (H3 H1).
        cbn in H3.
        lia.
    }
    {
        apply l_sublinear.
        now exists c.
    }
Qed.