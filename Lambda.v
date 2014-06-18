Require Export Arith.
Require Export Omega.

Definition id : Type := nat.

Inductive expr : Type :=
  | e_var : id -> expr
  | e_app : expr -> expr -> expr
  | e_abs : id -> expr -> expr.

Inductive value : expr -> Prop :=
  | v_abs : forall x e,
              value (e_abs x e).

Inductive context : Type :=
  | hole : context
  | app_l : context -> expr -> context
  | app_r : expr -> context -> context.

Reserved Notation "E '[' e ']'" (at level 20).

Fixpoint plug (ectx : expr * context) : expr :=
  (fix plug' e ctx :=
     match ctx with
       | hole => e
       | app_l ctx' e2 =>
         e_app (plug' e ctx') e2
       | app_r v ctx' =>
         e_app v (plug' e ctx')
     end)
    (fst ectx) (snd ectx)

where "E '[' e ']'" := (plug (e, E)).

Fixpoint decomp (e : expr) : (expr * context) :=
  match e with
    | e_app (e_abs x e') (e_abs x1 e1') =>
      (e, hole)
    | e_app (e_abs x e') e2 =>
      (e2, app_r (e_abs x e') hole)
    | e_app e1 e2 =>
      (e1, app_l hole e2)
    | _ => (e, hole)
  end.

Lemma plug_decomp :
  forall (e : expr),
      plug (decomp e) = e.
Proof.
  intros.
  destruct e;
    try destruct e1; try destruct e2;
    reflexivity.
Qed.

Reserved Notation "'[' x ':=' e' ']' e" (at level 20).

Fixpoint subst (e : expr) (x : id) (e' : expr) : expr :=
  match e with
    | e_var x' =>
      if beq_nat x x' then e' else e
    | e_abs x' e1 =>
      e_abs x' (if beq_nat x x' then e1 else ([x:=e'] e1))
    | e_app e1 e2 =>
      e_app ([x:=e'] e1) ([x:=e'] e2)
  end

where "'[' x ':=' e' ']' e" := (subst e x e').

Reserved Notation "e '==>' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
  | E_App :
      forall x e' v,
        value v ->
        (e_app (e_abs x e') v) ==> [x:=v]e'

where "e '==>' e'" := (step e e').

Reserved Notation "e '-->' e'" (at level 40).

Inductive std_step : expr -> expr -> Prop :=
  | StdRed :
      forall (e : expr) (E : context) (e1 e1' : expr),
        (e1, E) = decomp e ->
        e1 ==> e1' ->
        E[e1] --> E[e1']

where "e '-->' e'" := (std_step e e').

Example ex1 :
  (e_app (e_abs 1 (e_abs 0 (e_var 1))) (e_abs 2 (e_var 2)))
    --> (e_abs 0 (e_abs 2 (e_var 2))).
Proof.
  remember (e_app (e_abs 1 (e_abs 0 (e_var 1))) (e_abs 2 (e_var 2))) as e.
  remember (e_abs 0 (e_abs 2 (e_var 2))) as e'.
  remember (hole) as E.
  assert (H1: e = E[e]) by (subst; reflexivity); rewrite H1.
  assert (H2: e' = E[e']) by (subst; reflexivity); rewrite H2.
  apply StdRed with (e:=e).
  - subst. reflexivity.
  - subst. apply E_App. apply v_abs.
Qed.
