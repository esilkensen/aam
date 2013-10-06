(* Abstracting Abstract Machines (Van Horn and Might, ICFP'10) *)

Require Export SfLib.

(* ###################################################################### *)

Inductive expr : Type :=
  | var : id -> expr
  | app : expr -> expr -> expr
  | abs : id -> expr -> expr.

Tactic Notation "expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "var" | Case_aux c "app" | Case_aux c "abs" ].

(* ###################################################################### *)

Module CEK.

Inductive val : Type :=
  | clo : id -> expr -> partial_map val -> val.

Definition env : Type := partial_map val.

Inductive frame : Type :=
  | ar : expr -> frame
  | fn : val -> frame.

Definition kont : Type := list frame.

Inductive state : Type :=
  | ev : expr -> env -> kont -> state
  | ap : val -> kont -> state.

Definition inj : expr -> state :=
  fun e => ev e empty [].

Reserved Notation "s1 '==>' s2" (at level 40).

Inductive step : state -> state -> Prop :=
  | cek1 :
      forall x p k v,
        p x = Some v ->
        ev (var x) p k
        ==>
        ap v k
  | cek2 :
      forall x e p k,
        ev (abs x e) p k
        ==>
        ap (clo x e p) k
  | cek3 :
      forall e1 e2 p k,
        ev (app e1 e2) p k
        ==>
        ev e1 p (ar e2 :: k)
  | cek4 :
      forall x e p e2 k,
        ap (clo x e p) (ar e2 :: k)
        ==>
        ev e2 p (fn (clo x e p) :: k)
  | cek5 :
      forall x e p v2 k,
        ap v2 (fn (clo x e p) :: k)
        ==>
        ev e (extend p x v2) k

where "s1 '==>' s2" := (step s1 s2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "cek1" | Case_aux c "cek2" | Case_aux c "cek3"
    | Case_aux c "cek4" | Case_aux c "cek5" ].

Hint Constructors step.

Notation "s1 '==>*' s2" := (multi step s1 s2) (at level 40).

Example ex1 :
  forall x y,
    inj (app (abs x (var x)) (abs y (var y)))
    ==>*
    ap (clo y (var y) empty) [].
Proof.
  intros. unfold inj.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. apply cek1. apply extend_eq.
  apply multi_refl.
Qed.

End CEK.

(* ###################################################################### *)

Module CESK.

Definition addr : Type := id.
       
Inductive val : Type :=
  | clo : id -> expr -> partial_map addr -> val.

Definition env : Type := partial_map addr.

Definition storable : Type := val.

Definition store : Type := partial_map storable.

Inductive frame : Type :=
  | ar : expr -> frame
  | fn : val -> frame.

Definition kont : Type := list frame.

Inductive state : Type :=
  | ev : expr -> env -> store -> kont -> state
  | ap : val -> store -> kont -> state.

Definition inj : expr -> state :=
  fun e => ev e empty empty [].

Reserved Notation "s1 '==>' s2" (at level 40).

Inductive step : state -> state -> Prop :=
  | cesk1 :
      forall x p s k a v,
        p x = Some a ->
        s a = Some v ->
        ev (var x) p s k
        ==>
        ap v s k
  | cesk2 :
      forall x e p s k,
        ev (abs x e) p s k
        ==>
        ap (clo x e p) s k
  | cesk3 :
      forall e1 e2 p s k,
        ev (app e1 e2) p s k
        ==>
        ev e1 p s (ar e2 :: k)
  | cesk4 :
      forall x e p s e2 k,
        ap (clo x e p) s (ar e2 :: k)
        ==>
        ev e2 p s (fn (clo x e p) :: k)
  | cesk5 :
      forall x e p s v2 k a,
        s a = None ->
        ap v2 s (fn (clo x e p) :: k)
        ==>
        ev e (extend p x a) (extend s a v2) k

where "s1 '==>' s2" := (step s1 s2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "cesk1" | Case_aux c "cesk2" | Case_aux c "cesk3"
    | Case_aux c "cesk4" | Case_aux c "cesk5" ].

Hint Constructors step.

Notation "s1 '==>*' s2" := (multi step s1 s2) (at level 40).

Example ex1 :
  forall x y,
    inj (app (abs x (var x)) (abs y (var y)))
    ==>*
    ap (clo y (var y) empty) (extend empty (Id 0) (clo y (var y) empty)) [].
Proof.
  intros. unfold inj.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. auto.
  eapply multi_step. apply cesk5. auto.
  eapply multi_step. apply cesk1 with (Id 0). apply extend_eq.
    unfold extend. simpl. auto.
  apply multi_refl.
Qed.

End CESK.
