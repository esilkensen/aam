Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Eval simpl in plus (S (S O)) (S (S (S O))).

Theorem plus_n_O : forall (n : nat), plus n O = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Source Language *)

Inductive expr : Set :=
| Const : nat -> expr
| Plus : expr -> expr -> expr.

Fixpoint exprDenote (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => plus (exprDenote e1) (exprDenote e2)
  end.

Definition two_plus_three_expr : expr :=
  Plus (Const (S (S O))) (Const (S (S (S O)))).

Eval simpl in exprDenote two_plus_three_expr.

(* Target Language *)

Require Import List.
Import ListNotations.

Inductive instr : Set :=
| iconst : nat -> instr
| iplus : instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iconst n => Some (n :: s)
  | iplus => match s with
             | n :: m :: s' => Some (plus n m :: s')
             | _ => None
             end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' => match instrDenote i s with
               | Some s' => progDenote p' s'
               | None => None
               end
  end.

Definition two_plus_three_prog : prog :=
  iconst (S (S O)) :: iconst (S (S (S O))) :: iplus :: nil.

Eval simpl in progDenote two_plus_three_prog nil.

(* Translation *)

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => iconst n :: nil
  | Plus e1 e2 => (compile e2) ++ (compile e1) ++ (iplus :: nil)
  end.

Eval simpl in progDenote (compile two_plus_three_expr) nil.

Lemma compile_correct' : forall (e : expr) (p : prog) (s : stack),
    progDenote (compile e ++ p) s = progDenote p (exprDenote e :: s).
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - rewrite app_assoc_reverse.
    rewrite IHe2.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    simpl.
    reflexivity.
Qed.

Theorem compile_correct : forall (e : expr),
    progDenote (compile e) nil = Some (exprDenote e :: nil).
Proof.
  intros.
  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.
  simpl.
  reflexivity.
Qed.
