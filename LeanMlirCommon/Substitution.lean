import LeanMlirCommon.Basic

namespace MLIR.Untyped

class Substitution (S : Type u) (Var : outParam (Type v)) (Var' : outParam (Type w)) where
  substitute : S → Var → Var'
  /-- `removeMappingFor v σ` is called whenever a variable with name `v` is bound, and should return
  a substitution which does not change occurences of the now-bound variable `v` -/
  removeMappingFor : VarName → S → S




-- def Substitution : Type := List (VarName × VarName)

-- /-- Remove all substitutions of variable `v` (i.e., where `v` is the variable being replaced) from
-- the substitution `σ` -/
-- def Substitution.removeMappingFor (σ : Substitution) (v : VarName) : Substitution :=
--   List.filter (·.fst != v) σ

-- /-- Apply a substution `σ` to a variable `v`, returning the `v` unchanged if the `σ` does not define
-- a mapping for `v` -/
-- def Substitution.apply (σ : Substitution) (v : VarName) : VarName :=
--   match σ.lookup v with
--     | some w => w
--     | none => v


mutual

open Substitution
variable {Op T Var Var' S} (σ : S) [Substitution S Var Var']

def Expr.substitute : Expr Op T Var → Expr Op T Var'
  | ⟨varName, op, args, regions⟩ =>
      let σ := removeMappingFor varName σ
      ⟨varName, op, args.map (substitute σ), regions.map (Region.substitute σ)⟩

def Program.substitute : Program Op T Var → Program Op T Var' := sorry

def BasicBlock.substitute : BasicBlock Op T Var → BasicBlock Op T Var' := sorry

def Region.substitute : Region Op T Var → Region Op T Var' := sorry

end
