import LeanMlirCommon.UnTyped.Basic
import LeanMlirCommon.SimplyTyped.Context
import Std.Data.List

/-!
## Simple Intrinsically WellTyped MLIR programs
This module sets up a simple typesystem for MLIR programs, where the only terminator is
"return a value".

In particular:
  * This means there is no unstructured control flow (no jumping between basic blocks)
  * The type system assumes all variable are defined prior to usage (i.e., no graph regions)
  * We don't model dominance, only "closed from above" regions
  * The type system is structural
  * We define a concrete type for the context

We use `VarName` as the type of terminators, so that each terminator gives us exactly the variable
we should return.
-/

namespace MLIR.SimplyTyped

/-- The type of a regions specifies: the number and types of arguments to its entry block, and
the regions return type -/
structure RegionType (Ty : Type) where
  arguments : List Ty
  returnType : Ty
-- TODO: include a bool `closedFromAbove` field, to control variable inheritance

/-- The signature of a specific operation specifies:
* The number and types of its arguments,
* The number and types of its regions, and
* The type of it's return value -/
structure Signature (Ty : Type) where
  arguments : List Ty
  regions : List (RegionType Ty)
  returnType : Ty

/-- To implement `OpSignature` for a type of `Op`erations, we specify the signature of each
operation `op : Op` -/
class OpSignature (Op : Type) (Ty : outParam Type) where
  signature : Op → Signature Ty



/-!
# WellTyped
We define what it means for an untyped program to be well-formed under a specific context
-/
mutual

open OpSignature (signature)

variable {Op Ty : Type} [OpSignature Op Ty]

def Expr.WellTyped (Γ : Context Ty) : UnTyped.Expr Op VarName → Ty → Prop
  | ⟨varName, op, args, regions⟩, ty =>
    let ⟨argTys, rgnTys, retTy⟩ := signature op
    args.length = argTys.length
      ∧ ∀ x ∈ args.zip argTys, Γ.hasType x.fst x.snd
    ∧ regWT regions rgnTys
    ∧ ty = retTy
    -- HACK: `regWT` is morally:
    -- `regions.length = rgnTys.length ∧ ∀ r ∈ regions.zip rgnTys, Region.WellTyped r.fst r.snd`
    -- we inline the definition to make the termination checker happy.
    where regWT : List (UnTyped.Region Op VarName) → List (RegionType Ty) → Prop
      | [], [] => True
      | r :: rgns, rTy :: rgnTys => Region.WellTyped r rTy ∧ regWT rgns rgnTys
      | _, _ => False

/-- -/
def Lets.WellTyped (Γ_in : Context Ty) : UnTyped.Lets Op VarName → Context Ty → Prop
  | ⟨[]⟩, Γ_out       => ∀ v t, Γ_out.hasType v t ↔ Γ_in.hasType v t
  | ⟨e :: es⟩, Γ_out  => ∃ eTy, Expr.WellTyped Γ_in e eTy
                                ∧ Lets.WellTyped (Γ_in.push e.varName eTy) ⟨es⟩ Γ_out

def Program.WellTyped (Γ : Context Ty) : UnTyped.Program Op VarName → Ty → Prop
  | ⟨lets, v⟩, ty => ∃ Γ_out, Lets.WellTyped Γ lets Γ_out ∧ Γ_out.hasType v ty

def BasicBlock.WellTyped : UnTyped.BasicBlock Op VarName → RegionType Ty → Prop
  | ⟨_, args, prog⟩, ⟨argTys, retTy⟩ =>
      args.length = argTys.length ∧ Program.WellTyped (args.zip argTys) prog retTy

/-- Note that because we don't have branches between basic block, only the entry block to a region
actually matters. Any other blocks, if specified, are unreachable and may be ignored.
Also, regions are closed from above, so the well-formedness of a region does not depend on the
context of the outer region -/
def Region.WellTyped : UnTyped.Region Op VarName → RegionType Ty → Prop
  | ⟨entry, _⟩ => BasicBlock.WellTyped entry

end

/-- Justify the `regWT` hack -/
@[simp] theorem Expr.WellTyped.regWT_iff {Op Ty} [OpSignature Op Ty]
    (regions : List (UnTyped.Region Op VarName)) (regionTypes : List (RegionType Ty)) :
    regWT regions regionTypes
    ↔ regions.length = regionTypes.length
      ∧ ∀ r ∈ regions.zip regionTypes, Region.WellTyped r.fst r.snd := by
  induction regions generalizing regionTypes
  case nil =>
    cases regionTypes <;> simp [regWT]
  case cons r regions ih =>
    cases regionTypes
    case nil => simp [regWT]
    case cons rTy regionTypes =>
      simp only [regWT, ih, List.length_cons, Nat.succ.injEq, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor <;> (intro ⟨h₁, h₂, h₃⟩; simpa [h₁, h₂] using h₃)
