Add LoadPath "cpdt".
Require Import List CpdtTactics.
Import ListNotations.

(* Source Language *)

Inductive expr : Set :=
| Const : nat -> expr
| Plus : expr -> expr -> expr.

Fixpoint exprDenote (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => exprDenote e1 + exprDenote e2
  end.

(* Target Language *)

Inductive instr : Set :=
| iconst : nat -> instr
| iplus : instr.

Definition prog := list instr.

Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iconst n => Some (n :: s)
  | iplus => match s with
             | n1 :: n2 :: s' => Some (n1 + n2 :: s')
             | _ => None
             end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | [] => Some s
  | i :: p' => match instrDenote i s with
               | Some s' => progDenote p' s'
               | _ => None
               end
  end.

(* Translation *)

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [iconst n]
  | Plus e1 e2 => compile e2 ++ compile e1 ++ [iplus]
  end.

Lemma semantic_preservation_gen : forall (e : expr) (p : prog) (s : stack),
    progDenote (compile e ++ p) s = progDenote p (exprDenote e :: s).
Proof.
  intro e.
  induction e; intros; simpl.
  - (* Base Case: e = Const n *)
    reflexivity.
  - (* Inductive Case: e = Plus e1 e2 *)
    rewrite app_assoc_reverse.
    rewrite IHe2.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    reflexivity.
Qed.


Theorem semantic_preservation : forall (e : expr),
    progDenote (compile e) [] = Some [exprDenote e].
Proof.
  intro e.
  rewrite (app_nil_end (compile e)).
  rewrite semantic_preservation_gen.
  reflexivity.
Qed.
