----------------------------------------------------------------------------------------------------
-- Propositional Dynamic Logic
----------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------
-- Syntax
----------------------------------------------------------------------------------------------------

-- We define propositions and instructions as aliases for strings.
abbrev Ψ := String

-- Mutual recursive syntax for formulae and programs.
mutual
  -- Abstract syntax tree for Formulae.
  inductive Φ where
    | prop : Ψ → Φ
    | false : Φ
    | imp : Φ → Φ → Φ
    | box : Ρ → Φ → Φ
    deriving BEq

  -- Abstract syntax tree for Programs.
  inductive Ρ where
    | atomic : Ψ → Ρ
    | star : Ρ → Ρ
    | choice : Ρ → Ρ → Ρ
    | seq : Ρ → Ρ → Ρ
    | test : Φ → Ρ
    deriving BEq
end

open Φ Ρ

-- Sugar syntax for primitive formulae.
notation "⊥" => false
infixr:90 "→" => imp
notation:50 "[" α "]" φ => box α φ

-- Sugar syntax for primitive programs.
postfix:max "⋆" => star
postfix:max "?" => test
infixl:80 ";" => seq
infixr:60 "∪" => choice

----------------------------------------------------------------------------------------------------
-- Basic Connectives Definitions
----------------------------------------------------------------------------------------------------
-- Def)   ⊤
--      ≡ ⊥ → ⊥
def true : Φ :=
  ⊥ → ⊥

notation "⊤" => true

-- Def)   ¬φ
--      ≡ φ → ⊥
def neg (φ : Φ) : Φ :=
  φ → ⊥

prefix:max "¬" => neg

-- Def)   φ₁ ∧ φ₂
--      ≡ ¬(φ₁ → ¬φ₂)
def and (φ₁ φ₂ : Φ) : Φ :=
  ¬ (φ₁ → ¬ φ₂)

infixr:70 "∧" => and

-- Def)   φ₁ ∨ φ₂
--      ≡ (¬φ₁) → φ₂
def or (φ₁ φ₂ : Φ) : Φ :=
  (¬ φ₁) → φ₂

infixr:60 "∨" => or

-- Def)   ⟨α⟩ φ
--      ≡ ¬[a] ¬φ
def diamond (α : Ρ) (φ : Φ) : Φ :=
  ¬ ([α] ¬ φ)

notation:50 "⟨" α "⟩" φ => diamond α φ

----------------------------------------------------------------------------------------------------
-- Control Structures Definitions
----------------------------------------------------------------------------------------------------
-- Def)   skip α
--      ≡ ⊤?
def skip : Ρ :=
  ⊤ ?

-- Def)   fail α
--      ≡ ⊥?
def fail : Ρ :=
  ⊥ ?

-- Def)   if φ₁ → φ₂ | ... | φₙ → αₙ fi
--      ≡  φ₁? ; α₁ ∪ ... ∪ φₙ? ; αₙ
def pdlIf (branches : List (Φ × Ρ)) : Ρ :=
  branches.foldr
    (λ (pair : Φ × Ρ) (acc : Ρ) =>
      let (φ, α) := pair
      ((φ ?) ; α) ∪ acc)
    skip

-- Def)   do φ₁ → α₁ | ... | φₙ → α₂ od
--      ≡ (φ₁? ; α₁ ∪ ... ∪ φₙ? ; αₙ)⋆ ; (¬φ₁ ∧ ... ∧ ¬φₙ)?
def pdlDo (branches : List (Φ × Ρ)) : Ρ :=
  let loop : Ρ := (pdlIf branches) ⋆
  let exit : Φ :=
    branches.foldr
      (λ (pair : Φ × Ρ) (acc : Φ) =>
        let (φ, _) := pair
        (¬ φ) ∧ acc)
      ⊤
  loop ; (exit ?)

-- Def)   if φ then α else β
--      ≡ φ? ; α ∪ ¬φ? ; β
def ifThenElse (φ : Φ) (α β : Ρ) : Ρ :=
  pdlIf [(φ, α), (¬ φ, β)]

notation "If" c:arg "{" t "}" => ifThenElse c t skip
notation "If" c:arg "{" t "}" "Else" "{" f "}" => ifThenElse c t f

def example₁ : Ρ :=
  If (prop "has_fuel") {
    atomic "move_robot";
    If (prop "task_complete") {
      skip
    } Else {
      atomic "move_robot"
    }
  } Else {
    fail     -- cannot proceed without fuel
  }

-- Def)   while φ do α
--      ≡ (φ? ; α)⋆ ; ¬φ?
def whileDo (φ : Φ) (α : Ρ) : Ρ :=
  pdlDo [(φ, α)]

notation "While" c:arg "{" b "}" => whileDo c b

def example₂ : Ρ :=
  While (prop "has_tasks") {
    If (prop "has_resources") {
      atomic "pick_and_place";
      If (prop "task_successful") {
        skip
      } Else {
        fail
      }
    } Else {
      fail
    }
  }

-- Def)   repeat α until φ
--      ≡ α ; (¬φ? ; α)⋆ ; φ?
def repeatUntil (α : Ρ) (φ : Φ) : Ρ :=
  α ; whileDo φ α

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

universe u

structure KripkeFrame where
  K : Type u
  mProp : Ψ → K → Prop         -- Interpretation of atomic formulae
  mInstr : Ψ → (K → K → Prop)  -- Interpretation of atomic programs

mutual
  def meaningFormula (κ : KripkeFrame) : Φ → κ.K → Prop
    | prop p => κ.mProp p
    | Φ.false => λ _ => False
    | imp φ₁ φ₂ => λ s => meaningFormula κ φ₁ s → meaningFormula κ φ₂ s
    | box α φ => λ s => ∀ t, meaningProgram κ α s t → meaningFormula κ φ t

  def meaningProgram (κ : KripkeFrame) : Ρ → κ.K → κ.K → Prop
    | atomic a => κ.mInstr a
    | star α => λ s t => Relation.TransGen (meaningProgram κ α) s t
    | choice α β => λ s t => meaningProgram κ α s t ∨ meaningProgram κ β s t
    | seq α β => λ s t => ∃ u, meaningProgram κ α s u ∧ meaningProgram κ β u t
    | test φ => λ s t => (s = t) ∧ (meaningFormula κ φ s)
end

def satisfies (κ : KripkeFrame) (s : κ.K) (φ : Φ) : Prop :=
  meaningFormula κ φ s

notation:50 κ "," s " ⊨ " φ => satisfies κ s φ

def exampleFrame : KripkeFrame where
  K := Nat              -- Worlds are natural numbers
  mProp := λ p s =>
    match p with
    | "p" => s % 2 = 0  -- p is true in even worlds
    | _ => False
  mInstr := λ a s t =>
    match a with
    | "inc" => t = s + 1  -- increment program
    | "dec" => t = s - 1  -- decrement program
    | _ => False
