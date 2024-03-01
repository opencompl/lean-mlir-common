
namespace MLIR

--TODO: fix this doc now that `Var` is gone
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


namespace UnTyped

/- The datastructure is generic over the types of: `Op`erations, `T`erminators and `Var`iables -/
variable (Op T : Type)

mutual

/-- An `Expr` binds the result of a single operation to a new variable. Morally, it represents
`$varName = $op($args) { $regions }` -/
inductive Expr
  | mk (varName : VarName) (op : Op) (args : List VarName) (regions : List Region)

/-- `Lets` is a sequence of operations (without terminator) -/
inductive Lets
  | mk (lets : List Expr)

/-- `Program` is a sequence of operations, followed by a terminator -/
inductive Program
  | mk (lets : Lets) (terminator : T)

/-- A basic block has a label, a set of arguments, and then a program -/
inductive BasicBlock
  | mk (label : BlockLabel) (args : List VarName) (program : Program)

/-- A regions consists of one or more basic blocks, where the first basic block is known as the
entry block -/
inductive Region
  | mk (entry : BasicBlock) (blocks : List BasicBlock)

end


/-! ## Projections -/
namespace Expr

def varName : Expr Op T → VarName
  | ⟨varName, _, _, _⟩ => varName

end Expr
