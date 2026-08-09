inductive binop : Type where
  | Plus
  | Times

inductive exp : Type where
  | Const : Nat → exp
  | Binop : binop → exp → exp → exp

def binop_denote (b : binop) : Nat → Nat → Nat :=
  match b with
  | binop.Plus => Nat.add
  | binop.Times => Nat.mul

def exp_denote (e : exp) : Nat :=
  match e with
  | exp.Const n => n
  | exp.Binop b e1 e2 => binop_denote b (exp_denote e1) (exp_denote e2)

def exp_denote' : exp → Nat
  | exp.Const n => n
  | exp.Binop b e1 e2 => binop_denote b (exp_denote' e1) (exp_denote' e2)

#eval exp_denote (exp.Const 42) -- 42
#eval exp_denote (exp.Binop binop.Plus (exp.Const 2) (exp.Const 3))
#eval exp_denote (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) (exp.Const 7))

inductive instr : Type where
  | iConst : Nat → instr
  | iBinop : binop → instr

abbrev prog := List instr
abbrev stack := List Nat

def instr_denote (i : instr) (s : stack) : Option stack :=
  match i with
  | instr.iConst n => some (n :: s)
  | instr.iBinop b =>
    match s with
    | n1 :: n2 :: s' => some (binop_denote b n1 n2 :: s')
    | _ => none

def prog_denote (p : prog) (s : stack) : Option stack :=
  match p with
  | [] => some s
  | i :: p' =>
    match instr_denote i s with
    | none => none
    | some s' => prog_denote p' s'

def compile (e : exp) : prog :=
  match e with
  | exp.Const n => [instr.iConst n]
  | exp.Binop b e1 e2 => compile e2 ++ (compile e1 ++ [instr.iBinop b]) -- Coqでは++が右結合なので、Leanでは明示的に括弧が必要

#eval prog_denote (compile (exp.Const 42)) [] -- some [42]
#eval prog_denote (compile (exp.Binop binop.Plus (exp.Const 2) (exp.Const 3))) [] -- some [5]
#eval prog_denote (compile (exp.Binop binop.Times (exp.Binop binop.Plus (exp.Const 2) (exp.Const 2)) (exp.Const 7))) [] --

theorem compile_correct (e : exp) :
  prog_denote (compile e) [] = some (exp_denote e :: []) := by

  have
    h : ∀ (p : List instr), ∀ (s : stack),
      prog_denote (compile e ++ p) s = prog_denote p (exp_denote e :: s) := by
        induction e
        case Const n =>
          intro p s
          -- CPDTに従って書き下すと…
          unfold compile
          unfold exp_denote
          conv =>
            lhs
            unfold prog_denote
            change prog_denote ([instr.iConst n] ++ p) s -- simpl; fold prog_denote
          rfl
          -- Leanではこう書けば済む
          -- simp [compile, prog_denote, instr_denote, exp_denote]
        case Binop b e1 e2 ih1 ih2 =>
          intro p s
          -- CPDTに従って書き下すと…
          unfold compile
          unfold exp_denote
          rw [List.append_assoc]
          rw [ih2]
          rw [List.append_assoc]
          rw [ih1]
          conv =>
            lhs
            unfold prog_denote
            change prog_denote ([instr.iBinop b] ++ p) (exp_denote e1 :: exp_denote e2 :: s)
          rfl
          -- Leanではこう書けば済む
          -- simp [compile, List.append_assoc, ih1, ih2, prog_denote, instr_denote, exp_denote]
  rw [← List.append_nil (compile e)] -- List.append_nilがxs ++ [] = xsなので
  rw [h]
  rfl
