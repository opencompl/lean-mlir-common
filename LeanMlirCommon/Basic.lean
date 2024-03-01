
namespace MLIR.Untyped

/- The datastructure is generic over the types of: `Op`erations, `T`erminators and `Var`iables -/
variable (Op T Var : Type)

/-- `VarName` is the type of (human-readable) variable names.
Variables names are primarily used at when binding new variables, whereas the `Var` generic type
is used

The name _might_ be semantically significant (in particular, when `Var = VarName`), or it might
be used only for pretty printing (for example, when we use De-Bruijn indices for `Var`). -/
def VarName : Type := String

/-- `BlockLabel` is the type of (human-readable) basic block labels. -/
def BlockLabel : Type := String

instance : DecidableEq VarName := by unfold VarName; infer_instance
instance : DecidableEq BlockLabel := by unfold BlockLabel; infer_instance

mutual

inductive Expr
  | mk (varName : VarName) (op : Op) (args : List Var) (regions : List Region)

inductive Program
  | mk (args : List VarName) (lets : List Expr) (terminator : T)

inductive BasicBlock
  | mk (label : BlockLabel) (program : Program)

inductive Region
  | mk (entry : Option Program) (blocks : List BasicBlock)

end







end MLIR.Untyped
