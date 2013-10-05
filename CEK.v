(* CEK: The CEK machine *)

Require Export SfLib.

(* ###################################################################### *)

Inductive expr : Type :=
| e_var : id -> expr
| e_app : expr -> expr -> expr
| e_abs : id -> expr -> expr.

Tactic Notation "e_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "e_var" | Case_aux c "e_app" | Case_aux c "e_abs" ].

Inductive val : Type :=
| v_clo : id -> expr -> (partial_map val) -> val.

Notation env := (partial_map val).

Inductive frame : Type :=
| app_r : expr -> frame
| app_l : val -> frame.

Notation kont := (list frame).

Inductive state : Type :=
| s_eval : expr -> env -> kont -> state
| s_apply : val -> kont -> state.

Inductive step : state -> state -> Prop :=
| CEK_var :
    forall x p k v,
      p x = Some v ->
      step (s_eval (e_var x) p k)
           (s_apply v k)
| CEK_abs :
    forall x e p k,
      step (s_eval (e_abs x e) p k)
           (s_apply (v_clo x e p) k)
| CEK_app1 :
    forall e1 e2 p k,
      step (s_eval (e_app e1 e2) p k)
           (s_eval e1 p (app_r e2 :: k))
| CEK_app2 :
    forall x e p e2 k,
      step (s_apply (v_clo x e p) (app_r e2 :: k))
           (s_eval e2 p (app_l (v_clo x e p) :: k))
| CEK_app3 :
    forall x e p v2 k,
      step (s_apply v2 (app_l (v_clo x e p) :: k))
           (s_eval e (extend p x v2) k).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CEK_var" | Case_aux c "CEK_abs" | Case_aux c "CEK_app1"
    | Case_aux c "CEK_app2" | Case_aux c "CEK_app3" ].

Hint Constructors step.

Notation "t1 '==>' t2" := (step t1 t2) (at level 40).

Notation "t1 '==>*' t2" := (multi step t1 t2) (at level 40).

(* Examples *)

Example example1 :
  forall x y,
    (s_eval (e_app (e_abs x (e_var x)) (e_abs y (e_var y))) empty [])
      ==>*
    (s_apply (v_clo y (e_var y) empty) []).
Proof.
  intros.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. apply CEK_var. apply extend_eq.
  apply multi_refl.
Qed.
