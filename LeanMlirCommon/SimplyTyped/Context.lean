import LeanMlirCommon.UnTyped.Basic

namespace MLIR.SimplyTyped

def Context (Ty : Type) : Type :=
  List (VarName × Ty)

namespace Context

/-- `Γ.hasType v ty` holds if `Γ` maps variable `v` to type `ty` -/
def hasType (Γ : Context Ty) (v : VarName) (ty : Ty) : Prop :=
  Γ.lookup v = some ty

/-- `Γ.push v ty` returns a context which maps `v` to `ty`, and works like `Γ` on all other
variables -/
def push (Γ : Context Ty) (v : VarName) (ty : Ty) :=
  (v, ty) :: Γ

/-- `Γ.hasType v ty` is decidable when our type universe has decidable equality -/
instance {Γ : Context Ty} [DecidableEq Ty] {v ty} :
    Decidable (Γ.hasType v ty) := by
  unfold hasType; infer_instance
