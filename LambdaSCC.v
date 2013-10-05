(* LambdaSCC: A Calculus for Static Contract Checking *)

Require Export SfLib.

(* ###################################################################### *)

(* Syntax of LambdaSCC *)

(* Primitives *)
Inductive prim : Type :=
  | IsNumber : prim
  | IsFalse : prim
  | IsCons : prim
  | IsEmpty : prim
  | IsProc : prim
  | Car : prim
  | Cdr : prim
  | Add1 : prim
  | Cons : prim
  | Plus : prim
  | Eq : prim.

(* Primitive predicates *)
Inductive prim_pred : prim -> Prop :=
  | p_number : prim_pred IsNumber
  | p_false : prim_pred IsFalse
  | p_cons : prim_pred IsCons
  | p_empty : prim_pred IsEmpty
  | p_proc : prim_pred IsProc.

(* Primitive unary operators *)
Inductive prim_un : prim -> Prop :=
  | p_pred : forall p, prim_pred p -> prim_un p
  | p_car : prim_un Car
  | p_cdr : prim_un Cdr
  | p_add1 : prim_un Add1.

(* Primitive binary operators *)
Inductive prim_bin : prim -> Prop :=
  | p_plus : prim_bin Plus
  | p_eq : prim_bin Eq.

(* Expressions *)
Inductive expr : Type :=
  | Abs : id -> expr -> expr
  | BTrue : expr
  | BFalse : expr
  | BNum : nat -> expr
  | BEmpty : expr
  | Hole : expr
  | Var : id -> expr
  | App : expr -> expr -> expr
  | PApp : prim -> list expr -> expr
  | If : expr -> expr -> expr -> expr.

Inductive base : expr -> Prop :=
  | b_true : base BTrue
  | b_false : base BFalse
  | b_num : forall n, base (BNum n)
  | b_empty : base BEmpty.

Inductive value : expr -> Prop :=
  | v_abs : forall x e, value (Abs x e)
  | v_base : forall b, base b -> value b
  | v_hole : value Hole.

Inductive con : Type :=
  | Flat : forall e, value e -> con
  | Fun : con -> id -> con -> con
  | Disj : con -> con -> con
  | Conj : con -> con -> con
  | Pair : con -> con -> con
  | Rec : id -> con -> con.

Inductive mod : Type :=
  | Mod : id -> con -> forall e, value e -> mod.

Inductive prog : Type :=
  | Prog : list mod -> expr -> prog.

(* Run-time syntax of LambdaSCC *)
