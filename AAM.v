(* Abstracting Abstract Machines (Van Horn and Might, ICFP'10) *)

Require Export SfLib.

Inductive id : Type := 
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof. destruct X. apply beq_nat_refl. Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros. destruct i1. destruct i2. unfold beq_id. apply beq_nat_sym.
Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros. destruct i1. destruct i2. unfold beq_id in H.
  apply beq_nat_eq in H. rewrite H. reflexivity.
Qed.

(* ###################################################################### *)

Inductive expr : Type :=
  | e_var : id -> expr
  | e_app : expr -> expr -> expr
  | e_abs : id -> expr -> expr.

Inductive val : Type :=
  | v_abs : id -> expr -> val.

Tactic Notation "expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "e_var" | Case_aux c "e_app" | Case_aux c "e_abs" ].

(* ###################################################################### *)

Module CEK.

Inductive env : Type :=
  | env_empty : env
  | env_extend : env -> id -> (val * env) -> env.

Fixpoint env_lookup p x :=
  match p with
    | env_empty => None
    | env_extend q y (v, p') =>
      if beq_id x y then Some (v, p') else env_lookup q x
  end.

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
    simpl. rewrite <- beq_id_refl. reflexivity.
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
      if beq_id x y then Some a else env_lookup q x
  end.

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
  induction n as [| n']; intros.
  Case "n = 0".
    destruct s as [| x s'].
    SCase "s = []".
      inversion H.
    SCase "s = x :: s'".
      simpl. omega.
  Case "n = S n'".
    destruct s as [| x s'].
    SCase "s = []".
      inversion H.
    SCase "s = x :: s'".
      inversion H. apply IHn' in H1. simpl. omega.
Qed.

Lemma store_lookup_length_app :
  forall s1 s2 n,
    n < length s1 ->
    store_lookup (s1 ++ s2) n = store_lookup s1 n.
Proof.
  intros. generalize dependent s2. generalize dependent s1.
  induction n as [| n']; intros.
  Case "n = 0".
    destruct s1 as [| x1 s1'].
    SCase "s1 = []".
      inversion H.
    SCase "s1 = x1 :: s1'".
      reflexivity.
  Case "n = S n'".
    destruct s1 as [| x1 s1'].
    SCase "s1 = []".
      inversion H.
    SCase "s1 = x1 :: s1'".
      simpl. apply IHn'. inversion H. auto. omega.
Qed.

Lemma store_lookup_alloc_pres :
  forall s a v1 p1' v2 p2',
    store_lookup s a = Some (v1, p1') ->
    store_lookup (store_extend s (v2, p2')) a = Some (v1, p1').
Proof.
  intros.
  destruct a as [| n'].
  Case "a = 0".
    destruct s; inversion H. reflexivity.
  Case "a = S n'".
    destruct s as [| (v, p') s']; inversion H. simpl. 
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
    simpl. rewrite <- beq_id_refl. reflexivity. reflexivity.
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
  Case "empty_sim".
    split; reflexivity.
  Case "extend_sim".
    destruct a; inversion H2.
Qed.

Lemma cek_sim_cesk_env_store_weakening :
  forall p1 p2 s2,
    cek_sim_cesk_env p1 p2 s2 ->
    forall v p',
      cek_sim_cesk_env p1 p2 (CESK.store_extend s2 (v, p')).
Proof.
  intros p1 p2 s2 H v p'.
  induction H.
  Case "empty_sim".
    apply empty_sim.
  Case "extend_sim".
    eapply extend_sim.
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
  Case "empty_sim".
    inversion H.
  Case "extend_sim".
    remember (beq_id x0 x) as b. destruct b.
    SCase "x0 = x".
      simpl in H0. rewrite <- Heqb in H0. inversion H0. subst.
      apply ex_intro with a. apply ex_intro with p2.
      split. simpl. rewrite <- Heqb. reflexivity.
      split; assumption.
    SCase "x0 <> x".
      simpl in H0. rewrite <- Heqb in H0.
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
  Case "empty_sim".
    inversion H. inversion H0.
  Case "extend_sim".
    remember (beq_id x0 x) as b. destruct b.
    SCase "x0 = x".
      inversion H3. subst. rewrite H in H1. inversion H1. subst.
      simpl. rewrite <- Heqb. apply ex_intro with p1.
      split. reflexivity. assumption.
    SCase "x0 <> x".
      simpl. rewrite <- Heqb.
      eapply IHcek_sim_cesk_env1. eassumption.
      assumption.
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
  Case "mt_sim".
    apply mt_sim.
  Case "ar_sim".
    apply ar_sim.
      apply cek_sim_cesk_env_store_weakening. assumption.
      assumption.
  Case "fn_sim".
    apply fn_sim.
      apply cek_sim_cesk_env_store_weakening. assumption.
      assumption.
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

Notation "s1 '~' t1" := (cek_sim_cesk_state s1 t1) (at level 40).

(* ###################################################################### *)

Inductive multi_n {X : Type} (R : relation X) : X -> X -> nat -> Prop :=
  | multi_n_refl : forall x,
                     multi_n R x x 0
  | multi_n_step : forall x y z n,
                     multi_n R x y n ->
                     R y z ->
                     multi_n R x z (1 + n).

Hint Constructors multi_n.

Lemma cek_sim_cesk_step :
  forall e s n,
    multi_n CEK.step (CEK.inj e) s n ->
    exists t,
      multi_n CESK.step (CESK.inj e) t n /\ s ~ t.
Proof.
  intros e s n. generalize dependent s.
  induction n as [| n']; (intros s H; inversion H; subst).
  Case "n = 0".
    unfold CEK.inj in H. unfold CESK.inj.
    eapply ex_intro. split; [auto | unfold CEK.inj; auto].
  Case "n = S n'".
    apply IHn' in H1. inversion H1. inversion H0.
    inversion H4; subst; inversion H3; subst.
    SCase "cek0".
      eapply ex_intro. split. eauto. auto.
    SCase "cek1".
      apply cek_sim_cesk_env_lookup_cek with p p2 s2 x0 v p' in H10.
        inversion H10. inversion H6. inversion H7. inversion H9.
        eapply ex_intro. split; eauto.
      assumption.
    SCase "cek2".
      eapply ex_intro. split. eauto. auto.
    SCase "cek3".
      inversion H10. subst.
      eapply ex_intro. split. eauto. auto.
    SCase "cek4".
      inversion H10. subst.
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
      multi_n CEK.step (CEK.inj e) s n /\ s ~ t.
Proof.
  Admitted. (* TODO *)
