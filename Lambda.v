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

Fixpoint plug (ectx : expr * context) : expr :=
  (fix plug' e ctx :=
     match ctx with
       | hole => e
       | app_l ctx' e2 =>
         e_app (plug' e ctx') e2
       | app_r v ctx' =>
         e_app v (plug' e ctx')
     end)
    (fst ectx) (snd ectx).

Fixpoint decomp (e : expr) : (expr * context) :=
  match e with
    | e_var x => (e, hole)
    | e_app (e_abs x e') e2 =>
      (e2, app_r (e_abs x e') hole)
    | e_app e1 e2 =>
      (e1, app_l hole e2)
    | e_abs x e' => (e, hole)
  end.

Lemma plug_decomp :
  forall (e : expr),
    plug (decomp e) = e.
Proof.
  intros. induction e; try destruct e1; reflexivity.
Qed.
