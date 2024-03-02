import LeanMlirCommon.SimplyTyped.WellTyped
import Mathlib.Data.Vector.Basic

namespace MLIR.SimplyTyped
open OpSignature (signature)

/-!
## Types
-/
section
variable (Op : Type) {Ty : Type} [OpSignature Op Ty]

/-- An instrinsically well-typed variable -/
def Var (Γ : Context Ty) (ty : Ty) : Type := { v : VarName // Γ.hasType v ty }

/-- A list of instrinsically well-typed variables -/
def VarList (Γ : Context Ty) (tys : List Ty) : Type :=
  { vs : List VarName // vs.length = tys.length ∧ ∀ v ∈ vs.zip tys, Γ.hasType v.fst v.snd }

/-- An `Expr` binds the result of a single operation to a new variable. Morally, it represents
`$varName = $op($args) { $regions }` -/
def Expr (Γ : Context Ty) (ty : Ty) : Type :=
  { expr : UnTyped.Expr Op VarName // Expr.WellTyped Γ expr ty }

/-- `Lets` is an intrinsically well-typed sequence of operations, which grows *downwards*.
That is, the head of the list represents the *first* operation to be executed -/
def Lets (Γ_in Γ_out : Context Ty) : Type :=
  { lets : UnTyped.Lets Op VarName // Lets.WellTyped Γ_in lets Γ_out }

/-- `RevLets` is an intrinsically well-typed sequence of operations, which grows *upwards*.
That is, the head of the list represents the *last* operation to be executed, and in particular,
may refer to any variables defined in the tail of the list -/
def RevLets (Γ_in Γ_out : Context Ty) : Type :=
  { lets : UnTyped.Lets Op VarName // Lets.WellTyped Γ_in ⟨List.reverse lets.inner⟩ Γ_out }

def Body (Γ : Context Ty) (ty : Ty) : Type :=
  { body : UnTyped.Body Op VarName // Body.WellTyped Γ body ty }

def BasicBlock (ty : RegionType Ty) : Type :=
  { block : UnTyped.BasicBlock Op VarName // BasicBlock.WellTyped block ty }

def Region (ty : RegionType Ty) : Type :=
  { region : UnTyped.Region Op VarName // Region.WellTyped region ty}

def RegionList (tys : List (RegionType Ty)) : Type :=
  { regions : List (UnTyped.Region Op VarName) // RegionList.WellTyped regions tys}

end

/-!
## Projections
-/
section
variable {Op Ty} [OpSignature Op Ty]

@[simp] abbrev Expr.varName (e : Expr Op Γ ty) : VarName := e.val.varName
@[simp] abbrev Expr.op (e : Expr Op Γ ty) : Op := e.val.op

theorem Expr.ty_eq (e : Expr Op Γ ty) : ty = (signature e.op).returnType := by
  rcases e with ⟨⟨⟩, h⟩
  unfold WellTyped at h
  simp_all

abbrev Lets.inner (l : Lets Op Γ_in Γ_out) : List (UnTyped.Expr Op VarName) := l.val.inner

def Lets.ofUnTyped (lets : UnTyped.Lets Op VarName) {Γ_in}
    (h : ∃ Γ_out, Lets.WellTyped Γ_in lets Γ_out) :
    Lets Op Γ_in (Lets.outContext lets Γ_in) :=
  ⟨lets, Lets.WellTyped.exists_iff.mp h⟩

theorem Lets.Γ_out_eq (l : Lets Op Γ_in Γ_out) : Γ_out.ExtEq (Lets.outContext l.val Γ_in) := by
  rcases l with ⟨⟨l⟩, h⟩
  induction l generalizing Γ_in
  case nil => exact h
  case cons e lets ih =>
    simp [WellTyped] at h
    apply ih h.right

/-- The context under which the return statement of a body is typed -/
def Body.returnContext : Body Op Γ ty → Context Ty
  | ⟨⟨lets, _⟩, _⟩ => Lets.outContext lets Γ

def Body.lets : (body : Body Op Γ ty) → Lets Op Γ body.returnContext
  | ⟨⟨lets, _⟩, h⟩ => ⟨lets, by unfold WellTyped at h; exact h.left⟩

def Body.return : (body : Body Op Γ ty) → Var body.returnContext ty
  | ⟨⟨_, ret⟩, h⟩ => ⟨ret, by unfold WellTyped at h; exact h.right⟩

end

/-!
## Constructors
-/

section
variable {Op Ty} [OpSignature Op Ty]

def Expr.mk {Γ} {ty}
    (varName : VarName)
    (op : Op) (ty_eq : ty = (signature op).returnType)
    (args : VarList Γ (signature op).arguments)
    (regions : RegionList Op (signature op).regions) :
    Expr Op Γ ty :=
  ⟨⟨varName, op, args.val, regions.val⟩, by
    simpa only [WellTyped, ty_eq, and_true, true_and, regions.prop] using args.prop
  ⟩

/-- The empty sequence of operations -/
def Lets.nil : Lets Op Γ Γ := ⟨⟨[]⟩, by simp [WellTyped]⟩

/-- Add a new operation to the top of the sequence, abstracting over a previously free variable -/
def Lets.lete (e : Expr Op Γ_in ty) (lets : Lets Op (Γ_in.push e.varName ty) Γ_out) :
    Lets Op Γ_in Γ_out :=
  ⟨⟨e.val :: lets.inner⟩, by
    rcases lets with ⟨⟨lets⟩, h⟩
    simpa [WellTyped, e.ty_eq] using And.intro e.prop h
  ⟩

def Body.mk (lets : Lets Op Γ_in Γ_out) (ret : Var Γ_out ty) : Body Op Γ_in ty :=
  ⟨⟨lets.val, ret.val⟩, by
    simp only [WellTyped]
    constructor
    · exact Lets.WellTyped_of_extEq Context.ExtEq.rfl lets.Γ_out_eq lets.prop
    · exact Context.hasType_of_extEq lets.Γ_out_eq.symm ret.prop
  ⟩

/-- Return an empty `Body`, whose terminator is "return `v`" -/
def Body.mkReturn (v : Var Γ ty) : Body Op Γ ty := .mk .nil v

/-- Add a new operation to the top of a `Body`, abstracting over a previously free variable -/
def Body.lete (e : Expr Op Γ eTy) : Body Op (Γ.push e.varName eTy) ty → Body Op Γ ty
  | ⟨⟨lets, ret⟩, h_lets⟩ =>
      let Γ_out := Lets.outContext lets Γ
      let lets : Lets Op _ Γ_out := ⟨lets, by
        simp only [WellTyped] at h_lets
        simp only [e.ty_eq] at *
        -- exact Lets.WellTyped_of_extEq Context.ExtEq.rfl _ h_lets.left
        sorry
      ⟩
      let ret : Var _ _ := ⟨ret, by
        simp only [WellTyped] at h_lets
        exact Context.hasType_of_extEq lets.Γ_out_eq h_lets.right
      ⟩
      Body.mk (lets.lete e) ret
