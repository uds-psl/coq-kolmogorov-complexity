From Undecidability.Axioms Require Import principles.
From Undecidability.Shared Require Import partial Dec Pigeonhole.
From Undecidability.Synthetic Require Import Definitions.
From Equations Require Import Equations.
Require Import Lia List FinFun.
Import ListNotations.

Definition equiv {X : Type} (A B : list X) := incl A B /\ incl B A.

Lemma firstn_app {X : Type} (x : X) n L :
    length L > n -> (firstn (S n) L) = (firstn n L) ++ [nth n L x].
Proof.
    revert L.
    induction n; intros.
    {
        destruct L; cbn.
        {
            cbn in H.
            lia.
        }
        {
            now rewrite firstn_O.
        }
    }
    {
        destruct L eqn:HL; cbn in *; [lia|].
        assert ((length l) > n) by lia.
        destruct l eqn:Hl; [cbn in H0; lia|].
        assert (l <> []) by congruence; rewrite <- Hl in *.
        specialize (IHn l H0).
        now rewrite IHn.
    }
Qed.

Lemma firstn_In {X : Type} (x y : X) n L :
    length L > n -> In x (firstn (S n) L) -> In x (firstn n L) \/ x = nth n L y.
Proof.
    intros.
    pose (firstn_app y n L H).
    rewrite e in H0.
    apply in_app_or in H0.
    cbn in H0.
    firstorder.
Qed.

Lemma NoDup_remove {X : Type} (eqdec : eq_dec X) (x : X) (L : list X) :
    NoDup L -> NoDup (remove eqdec x L).
Proof.
    intros.
    induction L.
    { now cbn. }
    {
        cbn.
        destruct (eqdec x a).
        { apply IHL. depelim H. easy. }
        {
            depelim H.
            specialize (IHL H0).
            constructor; [|easy].
            intro.
            apply H.
            now apply (in_remove eqdec L a x).
        }
    }
Qed.

Lemma NoDup_remove_length {X : Type} (eqdec : eq_dec X) (x : X) (L : list X) :
    NoDup L -> In x L -> length L = S(length (remove eqdec x L)).
Proof.
    intros.
    induction L.
    { easy. }
    {
        cbn.
        destruct (eqdec x a).
        {
            depelim H.
            rewrite notin_remove; intuition.
        }
        {
            f_equal.
            cbn.
            apply IHL.
            { now depelim H. }
            { destruct H0; intuition. }
        }
    }
Qed.

Lemma Forall_remove {X : Type} (eqdec : eq_dec X) (p : X -> Prop) (x : X) (L : list X) :
    Forall p L -> Forall p (remove eqdec x L).
Proof.
    do 2 rewrite Forall_forall.
    intros.
    destruct (in_remove eqdec L x0 x H0) as [?H _].
    now specialize (H x0 H1).
Qed. 

Fixpoint num_first_false (L : list bool) : nat :=
    match L with
    | [] => 0
    | b :: L0 => if b then 0 else S (num_first_false L0)
    end.

Lemma first_false_replicate x L :
    (num_first_false ((list.replicate x false) ++ true :: L)) = x.
Proof.
    induction x; cbn; [easy|].
    now rewrite IHx.
Qed.

Lemma skipn_replicate_app {X : Type} (x : X) n L :
    (skipn n ((list.replicate n x) ++ L)) = L.
Proof.
    rewrite <- (list.replicate_length n x) at 1.
    apply list.drop_app.
Qed.

Lemma skipn_replicate_app_cons {X : Type} (x y : X) n L :
    (skipn (S n) ((list.replicate n x) ++ y :: L)) = L.
Proof.
    rewrite <- (list.replicate_length n x) at 1.
    rewrite list.drop_app_ge; [|lia].
    assert ((S (length (list.replicate n x)) - length (list.replicate n x)) = 1) as -> by lia.
    cbn.
    now rewrite skipn_O.
Qed.

Lemma incl_transitive {X : Type} (A B C : list X) :
    incl A B -> incl B C ->  incl A C.
Proof.
    intros H H0 x H1.
    specialize (H x H1).
    apply (H0 x H).
Qed.

Lemma NoDup_partition {X : Type} (eqdec : eq_dec X) (L l l' : list X) :
    NoDup L -> NoDup l -> NoDup l' -> incl l L -> incl l' L -> (forall x, ~(In x l /\ In x l')) -> length L = length l + length l' -> equiv (l++l') L.
Proof.
    revert L l; induction l'; intros; cbn in *.
    { rewrite app_nil_r. split; [easy|]. apply NoDup_length_incl; [easy|lia|easy]. }
    {
        split.
        {
            apply incl_app.
            all: easy.
        }
        {
            rewrite list.cons_middle, app_assoc.
            depelim H1.
            unshelve erewrite (IHl' L (l ++ [a]) H _ H2 _ _ _ _).
            - apply truthtables.NoDup_app; [easy|repeat constructor; intros []|intros].
              intros [|[]].
              apply (H5 x).
              intuition.
            - intros x ?H.
              destruct (eqdec x a).
              + apply H4.
                now left.
              + apply H3.
                apply in_app_or in H7 as [|[|[]]]; [easy|].
                exfalso; now apply n.
            - intros x ?H.
              apply H4.
              now right.
            - intros x [?H%in_app_or ?H]; destruct H8.
              + apply (H5 x).
                intuition.
              + destruct H8 as [|[]].
                rewrite <- H8 in H7.
                contradiction.
            - rewrite app_length, H6.
              cbn.
              lia.
            - easy.
        }
    }
Qed.

Lemma nodup_length {X : Type} (Xeqdec : eq_dec X) (L : list X) :
    length L >= length (nodup Xeqdec L).
Proof.
    induction L; cbn; [constructor|].
    {
        destruct (in_dec Xeqdec a L); cbn.
        all: lia.
    }
Qed.

Fixpoint rev_seq (start : nat) : list nat := 
    if start is S x then start :: (rev_seq x) else [start].

Lemma skipn_incl {X : Type} (n : nat) :
    forall L : list X, incl (skipn n L) L.
Proof.
    induction n; intros L x H.
    { now rewrite skipn_O in H. }
    {
        destruct L; cbn in *; [easy|].
        right.
        now apply IHn.
    }
Qed.

Lemma skipn_incl_le {X : Type} (n : nat) :
    forall n' (L : list X), n <= n' -> incl (skipn n' L) (skipn n L).
Proof.
    induction n; cbn; intros.
    { rewrite skipn_O; apply skipn_incl. }
    {
        destruct L; cbn in *.
        { rewrite skipn_nil. easy. }
        {
            destruct n'; cbn in *; [lia|].
            apply IHn.
            lia.
        }
    }
Qed.

Lemma firstn_incl_le {X : Type} (n' : nat) :
    forall n (L : list X), n' <= n -> incl (firstn n' L) (firstn n L).
Proof.
    induction n'; cbn; intros.
    { rewrite firstn_O. intros _ []. }
    {
        destruct L; cbn in *.
        { rewrite firstn_nil. easy. }
        {
            destruct n; cbn in *; [lia|].
            intros y [|]; [now left|right].
            apply IHn'; [lia|easy].
        }
    }
Qed.

Lemma firstn_incl {X : Type} :
    forall n (L : list X), incl (firstn n L) L.
Proof.
    induction n; cbn; intros.
    { rewrite firstn_O. intros _ []. }
    {
        destruct L; cbn in *.
        { easy. }
        {
            intros y [|]; [now left|right].
            now apply IHn.
        }
    }
Qed.


Lemma NoDup_skipn {X : Type} (n : nat) :
    forall L : list X, NoDup L -> NoDup (skipn n L).
Proof.
    induction n; intros.
    { now rewrite skipn_O. }
    {
        destruct L; cbn; [easy|].
        apply IHn.
        now depelim H.   
    }
Qed.

Lemma NoDup_firstn {X : Type} (n : nat) :
    forall L : list X, NoDup L -> NoDup (firstn n L).
Proof.
    induction n; intros.
    { rewrite firstn_O. constructor. }
    {
        destruct L; cbn; [easy|constructor]; depelim H.
        - intro. apply firstn_incl in H1. easy.
        - now apply IHn.
    }
Qed.

Lemma rev_seq_not_nil :
    forall n, rev_seq n <> nil.
Proof.
    induction n; discriminate.
Qed.

Lemma rev_seq_last_O :
    forall n x, last (rev_seq n) x = 0.
Proof.
    induction n; intros; cbn; [easy|].
    assert (H := rev_seq_not_nil n).
    destruct (rev_seq n); [easy|]; clear H.
    apply IHn.
Qed.

Lemma rev_rev_seq :
    forall n , rev (rev_seq n) = seq 0 (S n).
Proof.
    induction n; [easy|].
    cbn [rev rev_seq] in *.
    rewrite IHn.
    rewrite (seq_S (S n)).
    now cbn.
Qed.

Lemma Injective_rev {X : Type} :
    Injective (@rev X).
Proof.
    intro L; induction L; cbn; intros.
    {
        apply (f_equal (@rev X)) in H.
        rewrite rev_involutive in H.
        now cbn in H.
    }
    {
        apply (f_equal (@rev X)) in H.
        rewrite rev_involutive in H.
        rewrite <- H.
        rewrite rev_app_distr.
        cbn.
        now rewrite rev_involutive.
    }
Qed.

Lemma rev_seq_rev :
    forall n , (rev_seq n) = rev (seq 0 (S n)).
Proof.
    induction n; [easy|].
    apply Injective_rev.
    rewrite rev_involutive.
    apply rev_rev_seq.
Qed.

Lemma last_rev_first {X : Type} (x y : X) (L : list X) :
    last (rev(x::L)) y = x.
Proof.
    cbn.
    now rewrite last_last.
Qed.


Lemma Injective_rev_seq :
    Injective rev_seq.
Proof.
    intro x.
    induction x; intros; destruct y; cbn in *; try discriminate; try easy.
    now inversion H.
Qed.
    
Lemma In_skipn {X : Type} (Xeqdec : eq_dec X) (x : X) (L : list X) :
    forall n L', In x (skipn n L) -> In x (skipn n (L'++L)).
Proof.
    induction n; intros; cbn in *.
    { rewrite skipn_O in *. apply in_or_app. now right. }
    {
        destruct L; cbn in *; [contradiction|].
        assert (S n <= length L' \/ S n > length L') as [|] by lia.
        {
            rewrite list.drop_app_le; [|easy].
            apply in_or_app.
            right.
            destruct (Xeqdec x x0); [now left|right].
            now apply (skipn_incl n L).
        }
        {
            assert (S n = length L' + (S n - length L')) by lia.
            rewrite H1.
            rewrite <- list.drop_drop, list.drop_app.
            assert (S n - length L' = S(n - length L')) by lia.
            rewrite H2.
            cbn.
            apply (skipn_incl_le (n - length L') n L).
            { lia. }
            { exact H. }
        }
    }
Qed.

Lemma enumerator_list (p : nat -> Prop) (f : nat -> option nat) :
    enumerator f p -> forall L, (forall x : nat, In x L -> p x)
    -> exists L', equiv (map Some L) (map f L').
Proof.
    enough (enumerator f p -> forall n L, (forall x : nat, In x L -> p x) -> exists L', equiv (map Some (firstn n L)) (map f L')).
    {
        intros.
        specialize (H H0 (length L) L H1).
        rewrite firstn_all in H.
        destruct H as [L' ?H].
        now exists L'.
    }
    intro.
    induction n; intros.
    { exists nil; rewrite firstn_O; cbn; apply conj; easy. }
    {
        destruct L.
        { exists nil; cbn. easy. }
        {
            cbn.
            assert (forall x : nat, In x L -> p x).
            { intros. apply H0. now right. }
            specialize (IHn L H1) as [L' IHn].
            specialize (H n0) as [H _].
            destruct H.
            { apply H0. now left. }
            {
                exists (x :: L').
                apply conj; intros y ?H.
                {
                    apply in_map_iff.
                    destruct H2.
                    { exists x. apply conj; [now rewrite <- H2|now left]. }
                    {
                        destruct IHn as [IHn _]; specialize (IHn y H2).
                        apply in_map_iff in IHn as [?x [?H ?H]].
                        exists x0; apply conj; [easy|now right].
                    }
                }
                {
                    apply in_map_iff in H2 as [?x [?H ?H]].
                    destruct H3 as [<-|].
                    { left. now rewrite <- H. }
                    {
                        right.
                        apply in_map_iff.
                        destruct IHn as [_ IHn].
                        assert (In (f x0) (map f L')) by eauto.
                        specialize (IHn (f x0) H4).
                        destruct (f x0) eqn:?H.
                        {
                            exists n1; apply conj.
                            { easy. }
                            { apply in_map_iff in IHn as [?x [[=<-] ?H]]. easy. }
                        }
                        { apply in_map_iff in H4; apply in_map_iff in IHn as [z [?H ?H]]. discriminate. }
                    }
                }
            }
        }
    }
Qed.

Lemma enumerator_list_NoDup (p : nat -> Prop) (f : nat -> option nat) :
    enumerator f p -> forall L, NoDup L -> (forall x : nat, In x L -> p x)
    -> exists L', NoDup L' /\ equiv (map Some L) (map f L').
Proof.
    enough (enumerator f p -> forall n L, NoDup L -> (forall x : nat, In x L -> p x) -> exists L', NoDup L' /\ equiv (map Some (firstn n L)) (map f L')).
    {
        intros.
        specialize (H H0 (length L) L H1 H2).
        rewrite firstn_all in H.
        destruct H as [L' ?H].
        now exists L'.
    }
    intro.
    induction n; intros.
    { exists nil; split; [constructor|rewrite firstn_O; cbn; apply conj; easy]. }
    {
        destruct L.
        { exists nil; cbn; split; [constructor|easy]. }
        {
            cbn.
            assert (forall x : nat, In x L -> p x).
            { intros. apply H1. now right. }
            depelim H0.
            specialize (IHn L H1 H3) as [L' [?H IHn]].
            specialize (H n0) as [H _].
            destruct H.
            { apply H2. now left. }
            {
                exists (x :: L').
                repeat apply conj.
                {
                    constructor; [intro|easy].
                    apply H0.
                    destruct IHn as [_ IHn].
                    specialize (IHn (f x)).
                    enough (In (f x) (map f L')).
                    {
                        specialize (IHn H6).
                        apply in_map_iff in IHn as [y [?H ?H]].
                        apply firstn_incl in H8.
                        rewrite H in H7.
                        inversion H7.
                        now rewrite <- H10.
                    }
                    apply in_map_iff.
                    exists x; split; easy.
                }
                {
                    intros y ?H.
                    apply in_map_iff.
                    destruct H5.
                    { exists x. apply conj; [now rewrite <- H5|now left]. }
                    {
                        destruct IHn as [IHn _]; specialize (IHn y H5).
                        apply in_map_iff in IHn as [?x [?H ?H]].
                        exists x0; apply conj; [easy|now right].
                    }
                }
                {
                    intros y ?H.
                    apply in_map_iff in H5 as [?x [?H ?H]].
                    destruct H6 as [<-|].
                    { left. now rewrite <- H. }
                    {
                        right.
                        apply in_map_iff.
                        destruct IHn as [_ IHn].
                        assert (In (f x0) (map f L')) by eauto.
                        specialize (IHn (f x0) H7).
                        destruct (f x0) eqn:?H.
                        {
                            exists n1; apply conj.
                            { easy. }
                            { apply in_map_iff in IHn as [?x [[=<-] ?H]]. easy. }
                        }
                        { apply in_map_iff in H7; apply in_map_iff in IHn as [z [?H ?H]]. discriminate. }
                    }
                }
            }
        }
    }
Qed.

Fact lt_length_list :
    forall n, {L | NoDup L /\ (forall x, In x L <-> x < n) /\ length L <= n}.
Proof.
    induction n.
    {
        exists nil; cbn; repeat apply conj; [constructor| |lia].
        split; intros; lia.
    }
    {
        destruct IHn as [L (?H & ?H & ?H)].
        exists (n :: L); repeat apply conj.
        {
            constructor; [intro|easy].
            specialize (H0 n) as [H0 _].
            specialize (H0 H2).
            lia.
        }
        {
            split.
            {
                intros [?H|?H]; [lia|].
                enough (x < n) by lia.
                now apply H0.
            }
            {
                intros.
                assert (x < n \/ x = n) as [|] by lia; [right; now apply H0| now left].
            }
        }
        { cbn; lia. }
    }
Qed.

Fact lt_length_list' :
    forall L n, NoDup L -> (forall x, In x L -> x < n) -> length L <= n.
Proof.
    induction L; intros; cbn; [lia|].
    depelim H.
    destruct n.
    { specialize (H1 a (or_introl eq_refl)). lia. }
    {
        enough (~ (length L) > n) by lia; intro.
        destruct (lt_length_list (S n)) as [L' (?H & ?H & ?H)].
        unshelve eassert (H6 := pigeonhole_length (a::L) _ _ L' _); [lia| now constructor | |].
        { intros x ?H. apply H4, H1. easy. }
        cbn in *.
        lia.
    }
Qed.


Fact nat_list_NoDup_size (L : list nat) :
    NoDup L -> S(list_numbers.max_list_with (fun x : nat => x) L) >= length L.
Proof.
    induction L; intros; cbn; [lia|].
    destruct L; [cbn; lia|].
    destruct (Nat.max_dec a (list_numbers.max_list_with (fun x : nat => x) (n :: L))); rewrite e.
    {   
        depelim H.
        specialize (IHL H0).
        enough (a > (list_numbers.max_list_with (fun x : nat => x) (n :: L))) by lia.
        assert (H1 := Max.le_max_r a (list_numbers.max_list_with (fun x : nat => x) (n :: L))).
        enough (a <> list_numbers.max_list_with (fun x : nat => x) (n :: L)) by lia; clear H1.
        intros ->.
        apply H.
        apply (max_list_spec' (n :: L)).
        congruence.
    }
    {
        apply le_n_S.
        enough (~length (n :: L) > list_numbers.max_list_with (fun x : nat => x) (n :: L)) by lia.
        intro.
        depelim H.
        specialize (IHL H0).
        assert (length (n :: L) = S (list_numbers.max_list_with (fun x : nat => x) (n :: L))) by lia.
        enough (~forall x, In x (a::n::L) -> x < length (n :: L)).
        { apply H3. intros. assert (H5 := max_list_with_spec x (a :: n :: L) (fun x => x) H4). rewrite H2. cbn in *; lia. }
        intro.
        unshelve eassert (H4 := lt_length_list' (a :: n :: L) (length (n :: L)) _ H3); [now constructor|].
        cbn in H4.
        lia.
    }
Qed.

Fact NoDup_equiv_length_eq {X : Type} (eqdec : eq_dec X) (L L' : list X) :
    NoDup L -> NoDup L' -> equiv L L' -> length L = length L'.
Proof.
    intros ?HL ?HL' [?H ?H].
    assert (forall x1 x2 : X, x1 <> x2 \/ ~ x1 <> x2) by firstorder.
    assert (P1 := pigeonhole_length L H1 HL L' H).
    assert (P2 := pigeonhole_length L' H1 HL' L H0).
    lia.
Qed.

Fact list_differece_not_in_eq {A : Type} {EqDecision0 : base.RelDecision eq} (L : list A) :
    forall L' x, ~ In x L -> list.list_difference L L' = list.list_difference L (remove EqDecision0 x L').
Proof.
    induction L; intros; cbn; [easy|].
    destruct (base.decide_rel base.elem_of a L'), (base.decide_rel base.elem_of a (remove EqDecision0 x L')).
    - erewrite (IHL L' x); [easy|intro].
      apply H; now right.
    - destruct (EqDecision0 x a) as [->|].
      * exfalso; apply H. now left.
      * exfalso; apply n.
        apply base.elem_of_list_In in e. apply base.elem_of_list_In.
        apply in_in_remove.
        all: intuition.
    - exfalso; apply n.
      apply base.elem_of_list_In in e; apply base.elem_of_list_In.
      apply (in_remove EqDecision0 L' a x).
      easy.
    - f_equal.
      apply IHL; intro; apply H.
      now right.
Qed.

Fact list_difference_noDup_length {A : Type} {EqDecision0 : base.RelDecision eq} (L : list A):
    forall L', NoDup L -> NoDup L' -> incl L' L -> length (list.list_difference L L') = length L - length L'.
Proof.
    induction L; cbn; intros; [lia|].
    unfold base.decide_rel, base.elem_of.
    destruct (list.elem_of_list_dec a L').
    { 
        rewrite base.elem_of_list_In in e.
        depelim H.
        rewrite (NoDup_remove_length EqDecision0 a L'); [|easy|easy].
        rewrite (list_differece_not_in_eq L L' a); [|easy].
        apply IHL; [easy|now apply NoDup_remove|].
        intros x ?H.
        apply in_remove in H3 as [?H ?H].
        specialize (H2 x H3).
        destruct H2; try easy.
        exfalso.
        now apply H4.
    }
    {
        cbn.
        depelim H.
        assert (incl L' L).
        { intros x ?H. rewrite base.elem_of_list_In in n. destruct (EqDecision0 x a) as [->|]; [easy|]. specialize (H2 x H3); destruct H2; firstorder. exfalso. apply n0. easy. }
        rewrite IHL; [|easy|easy|exact H3].
        {
            enough (length L >= length L') by lia.
            apply pigeonhole_length; [|easy|exact H3].
            { intros. destruct (EqDecision0 x1 x2); tauto. }
        }
    }
Qed.

Fact skipn_length {X : Type} n (L : list X) :
    length (skipn n L) <= length L.
Proof.
    revert L; induction n; intros; cbn.
    - rewrite skipn_O. constructor.
    - destruct L; cbn; [constructor|]. specialize (IHn L). lia.
Qed.