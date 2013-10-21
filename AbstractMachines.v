Require Import Arith.EqNat.
Require Import List.
Import ListNotations.
Require Import Omega.

(* ###################################################################### *)

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive multi {X : Type} (R : relation X) : X -> X -> Prop :=
  | multi_refl : forall (x : X),
                   multi R x x
  | multi_step : forall (x y z : X),
                   R x y ->
                   multi R y z ->
                   multi R x z.

Inductive multi_n {X : Type} (R : relation X) : X -> X -> nat -> Prop :=
  | multi_n_refl : forall x,
                     multi_n R x x 0
  | multi_n_step : forall x y z n,
                     multi_n R x y n ->
                     R y z ->
                     multi_n R x z (1 + n).

Hint Constructors multi_n.

(* ###################################################################### *)

Definition id : Type := nat.

Inductive expr : Type :=
  | e_var : id -> expr
  | e_app : expr -> expr -> expr
  | e_abs : id -> expr -> expr.

Inductive val : Type :=
  | v_abs : id -> expr -> val.

(* ###################################################################### *)

Module CEK.

Inductive env : Type :=
  | env_empty : env
  | env_extend : env -> id -> (val * env) -> env.

Fixpoint env_lookup p x :=
  match p with
    | env_empty => None
    | env_extend q y vp' =>
      if beq_nat x y then Some vp' else env_lookup q x
  end.

Lemma env_lookup_deterministic :
  forall p x v1 p1' v2 p2',
    env_lookup p x = Some (v1, p1') ->
    env_lookup p x = Some (v2, p2') ->
    (v1, p1') = (v2, p2').
Proof.
  intros p. induction p as [| p IHp y (v, p')]; intros x v1 p1' v2 p2' H1 H2.
  - inversion H1.
  - remember (beq_nat x y) as b.
    destruct b; simpl in H1; simpl in H2;
    rewrite <- Heqb in H1; rewrite <- Heqb in H2;
    rewrite H1 in H2; inversion H2; reflexivity.
Qed.

Inductive kont : Type :=
  | mt : kont
  | ar : expr -> env -> kont -> kont
  | fn : val -> env -> kont -> kont.

Inductive state : Type :=
  | ev : expr -> env -> kont -> state
  | ap : val -> env -> kont -> state.

Definition inj : expr -> state :=
  fun e => ev e env_empty mt.

Reserved Notation "s1 '==>' s2" (at level 40).

Inductive step : state -> state -> Prop :=
  | cek0 :
      forall x e p k,
        ev (e_abs x e) p k
        ==>
        ap (v_abs x e) p k
  | cek1 :
      forall x p k v p',
        env_lookup p x = Some (v, p') ->
        ev (e_var x) p k
        ==>
        ap v p' k
  | cek2 :
      forall e0 e1 p k,
        ev (e_app e0 e1) p k
        ==>
        ev e0 p (ar e1 p k)
  | cek3 :
      forall v p e p' k,
        ap v p (ar e p' k)
        ==>
        ev e p' (fn v p k)
  | cek4 :
      forall v p x e p' k,
        ap v p (fn (v_abs x e) p' k)
        ==>
        ev e (env_extend p' x (v, p)) k

where "s1 '==>' s2" := (step s1 s2).

Hint Constructors step.

Notation "s1 '==>*' s2" := (multi step s1 s2) (at level 40).

Lemma step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros s1 s2 s2' H1 H2.
  destruct H1; inversion H2; auto.
  apply (env_lookup_deterministic p x v p' v0 p'0) in H5;
    inversion H5; auto.
Qed.

Example ex1 :
  forall x y,
    inj (e_app (e_abs x (e_var x)) (e_abs y (e_var y)))
    ==>*
    ap (v_abs y (e_var y)) env_empty mt.
Proof.
  intros. unfold inj.
  eapply multi_step. apply cek2.
  eapply multi_step. apply cek0.
  eapply multi_step. apply cek3.
  eapply multi_step. apply cek0.
  eapply multi_step. apply cek4.
  eapply multi_step. apply cek1.
    simpl. rewrite <- beq_nat_refl. reflexivity.
  apply multi_refl.
Qed.

End CEK.

(* ###################################################################### *)

Module CESK.

Definition addr : Type := nat.
       
Inductive env : Type :=
  | env_empty : env
  | env_extend : env -> id -> addr -> env.

Definition storable : Type := (val * env)%type.

Definition store : Type := list storable.

Fixpoint env_lookup p x :=
  match p with
    | env_empty => None
    | env_extend q y a =>
      if beq_nat x y then Some a else env_lookup q x
  end.

Lemma env_lookup_deterministic :
  forall p x a1 a2,
    env_lookup p x = Some a1 ->
    env_lookup p x = Some a2 ->
    a1 = a2.
Proof.
  intros p.
  induction p as [| p IHp y a]; intros x a1 a2 H1 H2.
  - inversion H1.
  - remember (beq_nat x y) as b.
    destruct b;
      simpl in H1; simpl in H2;
      rewrite <- Heqb in H1; rewrite <- Heqb in H2;
      inversion H1; inversion H2;
      subst; auto; eapply IHp; eauto.
Qed.

Fixpoint store_lookup (s : store) (a : addr) : option storable :=
  match a with
    | 0 => match s with
             | [] => None
             | (v, p') :: _ => Some (v, p')
           end
    | S n' => match s with
                | [] => None
                | _ :: s' => store_lookup s' n'
              end
  end.

Lemma store_lookup_deterministic :
  forall s a v1 p1' v2 p2',
    store_lookup s a = Some (v1, p1') ->
    store_lookup s a = Some (v2, p2') ->
    (v1, p1') = (v2, p2').
Proof.
  intros s.
  induction s as [| (v, p) s']; intros a v1 p1' v2 p2' H1 H2.
  - destruct a; inversion H1.
  - destruct a; simpl in H1; simpl in H2.
    + rewrite H1 in H2. inversion H2. reflexivity.
    + eapply IHs'; eauto.
Qed.

Definition store_extend s x : store := s ++ [x].

Definition alloc (s : store) := length s.

Lemma store_lookup_alloc_none :
  forall s,
    store_lookup s (alloc s) = None.
Proof.
  induction s; auto.
Qed.

Lemma store_lookup_alloc_some :
  forall s v p',
    store_lookup (store_extend s (v, p')) (alloc s) = Some (v, p').
Proof.
  induction s; auto.
Qed.

Lemma store_lookup_length_inv :
  forall s n v p',
    store_lookup s n = Some (v, p') ->
    n < length s.
Proof.
  intros s n. generalize dependent s.
  induction n as [| n']; intros;
  destruct s; inversion H; simpl; try apply IHn' in H1; omega.
Qed.

Lemma store_lookup_length_app :
  forall s1 s2 n,
    n < length s1 ->
    store_lookup (s1 ++ s2) n = store_lookup s1 n.
Proof.
  intros. generalize dependent s2. generalize dependent s1.
  induction n as [| n']; intros;
  destruct s1; inversion H; auto; apply IHn'; omega.
Qed.

Lemma store_lookup_alloc_pres :
  forall s a v1 p1' v2 p2',
    store_lookup s a = Some (v1, p1') ->
    store_lookup (store_extend s (v2, p2')) a = Some (v1, p1').
Proof.
  intros.
  destruct a as [| n'].
  - destruct s; inversion H. reflexivity.
  - destruct s as [| (v, p') s']; inversion H. simpl. 
    apply store_lookup_length_app.
    eapply store_lookup_length_inv.
    eassumption.
Qed.

Inductive kont : Type :=
  | mt : kont
  | ar : expr -> env -> kont -> kont
  | fn : val -> env -> kont -> kont.

Inductive state : Type :=
  | ev : expr -> env -> store -> kont -> state
  | ap : val -> env -> store -> kont -> state.

Definition inj : expr -> state :=
  fun e => ev e env_empty [] mt.

Reserved Notation "s1 '==>' s2" (at level 40).

Inductive step : state -> state -> Prop :=
  | cesk0 :
      forall x e p s k,
        ev (e_abs x e) p s k
        ==>
        ap (v_abs x e) p s k
  | cesk1 :
      forall x p s k a v p',
        env_lookup p x = Some a ->
        store_lookup s a = Some (v, p') ->
        ev (e_var x) p s k
        ==>
        ap v p' s k
  | cesk2 :
      forall e0 e1 p s k,
        ev (e_app e0 e1) p s k
        ==>
        ev e0 p s (ar e1 p k)
  | cesk3 :
      forall v p s e p' k,
        ap v p s (ar e p' k)
        ==>
        ev e p' s (fn v p k)
  | cesk4 :
      forall v p s x e p' k,
        ap v p s (fn (v_abs x e) p' k)
        ==>
        ev e (env_extend p' x (alloc s)) (store_extend s (v, p)) k

where "s1 '==>' s2" := (step s1 s2).

Hint Constructors step.

Notation "s1 '==>*' s2" := (multi step s1 s2) (at level 40).

Lemma step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros s1 s2 s2' H1 H2.
  destruct H1; inversion H2; subst; auto.
  apply (env_lookup_deterministic p x a a0) in H7. subst.
  apply (store_lookup_deterministic s a0 v0 p'0 v p') in H0.
    inversion H0. reflexivity.
  assumption. assumption.
Qed.

Example ex1 :
  forall x y,
    inj (e_app (e_abs x (e_var x)) (e_abs y (e_var y)))
    ==>*
    ap (v_abs y (e_var y)) env_empty [(v_abs y (e_var y), env_empty)] mt.
Proof.
  intros. unfold inj.
  eapply multi_step. apply cesk2.
  eapply multi_step. apply cesk0.
  eapply multi_step. apply cesk3.
  eapply multi_step. apply cesk0.
  eapply multi_step. apply cesk4.
  eapply multi_step. eapply cesk1.
    simpl. rewrite <- beq_nat_refl. reflexivity. reflexivity.
  apply multi_refl.
Qed.

End CESK.

(* ###################################################################### *)

Inductive cek_sim_cesk_env : CEK.env -> CESK.env -> CESK.store -> Prop :=
  | empty_sim :
      forall s2,
        cek_sim_cesk_env CEK.env_empty CESK.env_empty s2
  | extend_sim :
      forall q1 x v p1,
        forall q2 a p2 s2,
          cek_sim_cesk_env q1 q2 s2 ->
          cek_sim_cesk_env p1 p2 s2 ->
          CESK.store_lookup s2 a = Some (v, p2) ->
          cek_sim_cesk_env
            (CEK.env_extend q1 x (v, p1)) (CESK.env_extend q2 x a) s2.

Hint Constructors cek_sim_cesk_env.

Lemma cek_sim_cesk_env_store_empty_inv :
  forall p1 p2,
    cek_sim_cesk_env p1 p2 [] ->
    p1 = CEK.env_empty /\ p2 = CESK.env_empty.
Proof.
  intros p1 p2 H.
  inversion H; subst.
  - split; reflexivity.
  - destruct a; inversion H2.
Qed.

Lemma cek_sim_cesk_env_store_weakening :
  forall p1 p2 s2,
    cek_sim_cesk_env p1 p2 s2 ->
    forall v p',
      cek_sim_cesk_env p1 p2 (CESK.store_extend s2 (v, p')).
Proof.
  intros p1 p2 s2 H v p'.
  induction H.
  - apply empty_sim.
  - eapply extend_sim.
    assumption.
    eassumption.
    apply CESK.store_lookup_alloc_pres. assumption.
Qed.

Lemma cek_sim_cesk_env_lookup_cek :
  forall p1 p2 s2,
    cek_sim_cesk_env p1 p2 s2 ->
    forall x v p1',
      CEK.env_lookup p1 x = Some (v, p1') ->
      exists a p2',
        CESK.env_lookup p2 x = Some a /\
        CESK.store_lookup s2 a = Some (v, p2') /\
        cek_sim_cesk_env p1' p2' s2.
Proof.
  intros p1 p2 s2 H1.
  induction H1; intros.
  - inversion H.
  - remember (beq_nat x0 x) as b. destruct b.
    + simpl in H0. rewrite <- Heqb in H0. inversion H0. subst.
      apply ex_intro with a. apply ex_intro with p2.
      split. simpl. rewrite <- Heqb. reflexivity.
      split; assumption.
    + simpl in H0. rewrite <- Heqb in H0.
      simpl. rewrite <- Heqb.
      apply IHcek_sim_cesk_env1.
      assumption.
Qed.

Lemma cek_sim_cesk_env_lookup_cesk :
  forall p1 p2 s2,
    cek_sim_cesk_env p1 p2 s2 ->
    forall x a v p2',
      CESK.env_lookup p2 x = Some a ->
      CESK.store_lookup s2 a = Some (v, p2') ->
      exists p1',
        CEK.env_lookup p1 x = Some (v, p1') /\
        cek_sim_cesk_env p1' p2' s2.
Proof.
  intros p1 p2 s2 H1.
  induction H1; intros.
  - inversion H.
  - inversion H0. remember (beq_nat x0 x) as b. destruct b.
    + inversion H3. subst. rewrite H in H1. inversion H1. subst.
      simpl. rewrite <- Heqb. exists p1. split; auto.
    + simpl. rewrite <- Heqb. eapply IHcek_sim_cesk_env1; eauto.
Qed.

Inductive cek_sim_cesk_kont : CEK.kont -> CESK.kont -> CESK.store -> Prop :=
  | mt_sim :
      forall s2,
        cek_sim_cesk_kont CEK.mt CESK.mt s2
  | ar_sim :
      forall e p1 k1,
        forall p2 s2 k2,
          cek_sim_cesk_env p1 p2 s2 ->
          cek_sim_cesk_kont k1 k2 s2 ->
          cek_sim_cesk_kont (CEK.ar e p1 k1) (CESK.ar e p2 k2) s2
  | fn_sim :
      forall v p1 k1,
        forall p2 s2 k2,
          cek_sim_cesk_env p1 p2 s2 ->
          cek_sim_cesk_kont k1 k2 s2 ->
          cek_sim_cesk_kont (CEK.fn v p1 k1) (CESK.fn v p2 k2) s2.

Hint Constructors cek_sim_cesk_kont.

Lemma cek_sim_cesk_kont_store_weakening :
  forall k1 k2 s2,
    cek_sim_cesk_kont k1 k2 s2 ->
    forall v p',
      cek_sim_cesk_kont k1 k2 (CESK.store_extend s2 (v, p')).
Proof.
  intros k1 k2 s2 H v p'.
  induction H.
  - apply mt_sim.
  - apply ar_sim.
    + apply cek_sim_cesk_env_store_weakening. assumption.
    + assumption.
  - apply fn_sim.
    + apply cek_sim_cesk_env_store_weakening. assumption.
    + assumption.
Qed.

Inductive cek_sim_cesk_state : CEK.state -> CESK.state -> Prop :=
  | ev_sim :
      forall e p1 k1,
        forall p2 s2 k2,
          cek_sim_cesk_env p1 p2 s2 ->
          cek_sim_cesk_kont k1 k2 s2 ->
          cek_sim_cesk_state (CEK.ev e p1 k1) (CESK.ev e p2 s2 k2)
  | ap_sim :
      forall v p1 k1,
        forall p2 s2 k2,
          cek_sim_cesk_env p1 p2 s2 ->
          cek_sim_cesk_kont k1 k2 s2 ->
          cek_sim_cesk_state (CEK.ap v p1 k1) (CESK.ap v p2 s2 k2).

Hint Constructors cek_sim_cesk_state.

(* ###################################################################### *)

Lemma cek_sim_cesk_step :
  forall e s n,
    multi_n CEK.step (CEK.inj e) s n ->
    exists t,
      multi_n CESK.step (CESK.inj e) t n /\
      cek_sim_cesk_state s t.
Proof.
  intros e s n. generalize dependent s.
  induction n as [| n']; intros s H; inversion H; subst.
  - unfold CEK.inj in H. unfold CESK.inj.
    eapply ex_intro. split; [auto | unfold CEK.inj; auto].
  - apply IHn' in H1. inversion H1. inversion H0.
    inversion H4; subst; inversion H3; subst.
    + eapply ex_intro. split; eauto.
    + apply cek_sim_cesk_env_lookup_cek with p p2 s2 x0 v p' in H10.
      inversion H10. inversion H6. inversion H7. inversion H9.
      eapply ex_intro. split; eauto.
      assumption.
    + eapply ex_intro. split; eauto. 
    + inversion H10. subst.
      eapply ex_intro. split; eauto.
    + inversion H10. subst.
      apply cek_sim_cesk_env_store_weakening with p p2 s2 v p2 in H9.
      apply cek_sim_cesk_env_store_weakening with p' p0 s2 v p2 in H12.
      eapply ex_intro. split. eauto. 
      apply ev_sim. eapply extend_sim; eauto. 
      apply CESK.store_lookup_alloc_some.
      apply cek_sim_cesk_kont_store_weakening.
      assumption.
Qed.

Lemma cesk_sim_cek_step :
  forall e t n,
    multi_n CESK.step (CESK.inj e) t n ->
    exists s,
      multi_n CEK.step (CEK.inj e) s n /\
      cek_sim_cesk_state s t.
Proof.
  intros e t n. generalize dependent t.
  induction n as [| n']; intros t H; inversion H; subst.
  - unfold CESK.inj in H. unfold CEK.inj.
    eapply ex_intro. split; [auto | unfold CESK.inj; auto].
  - apply IHn' in H1. inversion H1. inversion H0.
    inversion H4; subst; inversion H3; subst.
    + eapply ex_intro. split; eauto.
    + apply cek_sim_cesk_env_lookup_cesk with p1 p s x0 a v p' in H10.
      inversion H10. inversion H7.
      eapply ex_intro. split; eauto.
      assumption. assumption.
    + eapply ex_intro. split; eauto.
    + inversion H11. subst.
      eapply ex_intro. split; eauto.
    + inversion H11. subst.
      apply cek_sim_cesk_env_store_weakening with p1 p s v p in H8.
      apply cek_sim_cesk_env_store_weakening with p0 p' s v p in H12.
      eapply ex_intro. split. eauto.
      apply ev_sim. eapply extend_sim; eauto.
      apply CESK.store_lookup_alloc_some.
      apply cek_sim_cesk_kont_store_weakening.
      assumption.
Qed.
