
universe u

axiom Ctxt : Type u → Type u

/-
  # Classes
-/

class Splitable (Ctxt : Type u) where
  /-- `Split Γ Δ₁ Δ₂` means that `Γ` can be split into contexts `Δ₁` and `Δ₂` -/
  Split : Ctxt → Ctxt → Ctxt → Type u
  -- SplitAssoc : Split Γ Δ₁ Δ₂ → Split Δ₁ Δ'₁ Δ'₂ →
  --   ∃ Δ₃, Split Γ Δ₁ Δ₃ ∧

class HasVar (Ty : outParam (Type u)) (Ctxt : Type u) where
  Var : Ctxt → Ty → Type u

class Context (Ty : outParam (Type u)) (Ctxt : Type u) extends Splitable Ctxt, HasVar Ty Ctxt

variable (Op Ty Ctxt : Type u) [Context Ty Ctxt]

abbrev RegionSignature Ty := List (Ctxt × Ty)

structure Signature (Ty : Type) where
  sig     : List Ty
  regSig  : RegionSignature Ty
  outTy   : Ty

class OpSignature (Op : Type) (Ty : outParam (Type)) where
  signature : Op → Signature Ty
export OpSignature (signature)

section
variable {Op Ty} [s : OpSignature Op Ty]

def OpSignature.sig     := Signature.sig ∘ s.signature
def OpSignature.regSig  := Signature.regSig ∘ s.signature
def OpSignature.outTy   := Signature.outTy ∘ s.signature

end

/-
  # Datastructures
-/

variable (Op : Type) {Ty : Type} [OpSignature Op Ty]

mutual

/-- A very simple intrinsically typed expression. -/
inductive Expr : (Γ : Ctxt Ty) → (ty : Ty) → Type :=
  | mk {Γ} {ty} (op : Op)
    (ty_eq : ty = OpSignature.outTy op)
    (args : HVector (Var Γ) <| OpSignature.sig op)
    (regArgs : HVector (fun t : Ctxt Ty × Ty => Com t.1 t.2)
      (OpSignature.regSig op)) : Expr Γ ty

/-- A very simple intrinsically typed program: a sequence of let bindings. -/
inductive Program : Ctxt Ty → Ty → Type where
  | ret (v : Var Γ t) : Com Γ t
  | lete (e : Expr Γ α) (body : Com (Γ.snoc α) β) : Com Γ β

inductive Region :

end
