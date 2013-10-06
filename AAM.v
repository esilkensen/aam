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

Definition addr : Type := id.
       
Inductive env : Type :=
  | env_empty : env
  | env_extend : env -> id -> addr -> env.

Definition storable : Type := (val * env)%type.

Inductive store : Type :=
  | store_empty : store
  | store_extend : store -> addr -> storable -> store.

Fixpoint env_lookup p x :=
  match p with
    | env_empty => None
    | env_extend q y a =>
      if beq_id x y then Some a else env_lookup q x
  end.

Fixpoint store_lookup s a :=
  match s with
    | store_empty => None
    | store_extend t b (v, p') =>
      if beq_id a b then Some (v, p') else store_lookup t a
  end.

Inductive kont : Type :=
  | mt : kont
  | ar : expr -> env -> kont -> kont
  | fn : val -> env -> kont -> kont.

Inductive state : Type :=
  | ev : expr -> env -> store -> kont -> nat -> state
  | ap : val -> env -> store -> kont -> nat -> state.

Definition inj : expr -> state :=
  fun e => ev e env_empty store_empty mt 0.

Reserved Notation "s1 '==>' s2" (at level 40).

Inductive step : state -> state -> Prop :=
  | cesk0 :
      forall x e p s k n,
        ev (e_abs x e) p s k n
        ==>
        ap (v_abs x e) p s k n
  | cesk1 :
      forall x p s k a v p' n,
        env_lookup p x = Some a ->
        store_lookup s a = Some (v, p') ->
        ev (e_var x) p s k n
        ==>
        ap v p' s k n
  | cesk2 :
      forall e0 e1 p s k n,
        ev (e_app e0 e1) p s k n
        ==>
        ev e0 p s (ar e1 p k) n
  | cesk3 :
      forall v p s e p' k n,
        ap v p s (ar e p' k) n
        ==>
        ev e p' s (fn v p k) n
  | cesk4 :
      forall v p s x e p' k n,
        ap v p s (fn (v_abs x e) p' k) n
        ==>
        ev e (env_extend p' x (Id n)) (store_extend s (Id n) (v, p)) k (n + 1)

where "s1 '==>' s2" := (step s1 s2).

Hint Constructors step.

Notation "s1 '==>*' s2" := (multi step s1 s2) (at level 40).

Example ex1 :
  forall x y,
    inj (e_app (e_abs x (e_var x)) (e_abs y (e_var y)))
    ==>*
    ap (v_abs y (e_var y)) env_empty (store_extend store_empty (Id 0) (v_abs y (e_var y), env_empty)) mt 1.
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

Tactic Notation "CEK.step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "cek0" | Case_aux c "cek1" | Case_aux c "cek2"
    | Case_aux c "cek3" | Case_aux c "cek4" | Case_aux c "cek5" ].

Tactic Notation "CESK.step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "cesk0" | Case_aux c "cesk1" | Case_aux c "cesk2"
    | Case_aux c "cesk3" | Case_aux c "cesk4" | Case_aux c "cesk5" ].

Fixpoint cesk_cek_env p s n :=
  match p with
    | CESK.env_empty => CEK.env_empty
    | CESK.env_extend q x a =>
      match n with
        | 0 => CEK.env_empty (* error *)
        | S n' =>
          match CESK.store_lookup s a with
            | None => CEK.env_empty (* error *)
            | Some (v, p') =>
              CEK.env_extend (cesk_cek_env q s n') x (v, (cesk_cek_env p' s n'))
          end
      end
  end.

Fixpoint cesk_cek_kont k s n :=
  match k with
    | CESK.mt => CEK.mt
    | CESK.ar e p k' =>
      CEK.ar e (cesk_cek_env p s n) (cesk_cek_kont k' s n)
    | CESK.fn v p k' =>
      CEK.fn v (cesk_cek_env p s n) (cesk_cek_kont k' s n)
  end.

Fixpoint cesk_cek_state st :=
  match st with
    | CESK.ev e p s k n =>
      CEK.ev e (cesk_cek_env p s n) (cesk_cek_kont k s n)
    | CESK.ap v p s k n =>
      CEK.ap v (cesk_cek_env p s n) (cesk_cek_kont k s n)
  end.

Theorem cesk_cek_inj_eq :
  forall e,
    cesk_cek_state (CESK.inj e) = CEK.inj e.
Proof. reflexivity. Qed.

Inductive cek_cesk_env_sim : CEK.env -> CESK.env -> CESK.store -> Prop :=
  | empty_sim :
      forall s2,
        cek_cesk_env_sim CEK.env_empty CESK.env_empty s2
  | extend_sim :
      forall q1 x1 v1 p1,
        forall q2 x2 a2 v2 p2 s2,
          x1 = x2 ->
          v1 = v2 ->
          cek_cesk_env_sim q1 q2 s2 ->
          cek_cesk_env_sim p1 p2 s2 ->
          CESK.store_lookup s2 a2 = Some (v2, p2) ->
          cek_cesk_env_sim
            (CEK.env_extend q1 x1 (v1, p1)) (CESK.env_extend q2 x2 a2) s2.

Inductive cek_cesk_kont_sim : CEK.kont -> CESK.kont -> CESK.store -> Prop :=
  | mt_sim :
      forall s2,
        cek_cesk_kont_sim CEK.mt CESK.mt s2
  | ar_sim :
      forall e1 p1 k1,
        forall e2 p2 s2 k2,
          e1 = e2 ->
          cek_cesk_env_sim p1 p2 s2 ->
          cek_cesk_kont_sim k1 k2 s2 ->
          cek_cesk_kont_sim (CEK.ar e1 p1 k1) (CESK.ar e2 p2 k2) s2
  | fn_sim :
      forall v1 p1 k1,
        forall v2 p2 s2 k2,
          v1 = v2 ->
          cek_cesk_env_sim p1 p2 s2 ->
          cek_cesk_kont_sim k1 k2 s2 ->
          cek_cesk_kont_sim (CEK.fn v1 p1 k1) (CESK.fn v2 p2 k2) s2.

Inductive cek_cesk_state_sim : CEK.state -> CESK.state -> Prop :=
  | ev_sim :
      forall e1 p1 k1,
        forall e2 p2 s2 k2 n2,
          e1 = e2 ->
          cek_cesk_env_sim p1 p2 s2 ->
          cek_cesk_kont_sim k1 k2 s2 ->
          cek_cesk_state_sim (CEK.ev e1 p1 k1) (CESK.ev e2 p2 s2 k2 n2)
  | ap_sim :
      forall v1 p1 k1,
        forall v2 p2 s2 k2 n2,
          v1 = v2 ->
          cek_cesk_env_sim p1 p2 s2 ->
          cek_cesk_kont_sim k1 k2 s2 ->
          cek_cesk_state_sim (CEK.ap v1 p1 k1) (CESK.ap v2 p2 s2 k2 n2).
