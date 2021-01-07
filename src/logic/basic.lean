universes u v

/-- Ex falso, the nondependent eliminator for the `Empty` type. -/
def Empty.elim {C : Sort u} (t : Empty) : C := nomatch t

instance : Subsingleton Empty := ⟨λ a => a.elim⟩

instance {α : Type u} {β : Type v} [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => congr (congrArg _ $ Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

instance : DecidableEq Empty := λa => a.elim

instance instSortInhabited' : Inhabited (Inhabited.default : Sort u) := ⟨PUnit.unit⟩

instance decidableEqOfSubsingleton {α : Sort u} [Subsingleton α] : DecidableEq α :=
fun a b => isTrue (Subsingleton.elim a b)

@[simp] theorem eqIffTrueOfSubsingleton [Subsingleton α] (x y : α) : x = y ↔ true :=
⟨λ _ => ⟨_⟩, λ _ => Subsingleton.elim x y⟩

/-- Add an instance to "undo" coercion transitivity into a chain of coercions, because
   most simp lemmas are stated with respect to simple coercions and will not match when
   part of a chain. -/
@[simp] theorem coeCoe {α β γ} [Coe α β] [Coe β γ]
  (a : α) : (a : γ) = (a : β) := rfl

-- Translator's note: `coe_fn_coe_trans`, `coe_fn_coe_base`, and `coe_sort_coe_trans` are not
-- translated because the relavant instances do not exist.

set_option bootstrap.inductiveCheckResultingUniverse false in
/-- `PEmpty` is the universe-polymorphic analogue of `Empty`. -/
inductive PEmpty : Sort u

/-- Ex falso, the nondependent eliminator for the `PEmpty` type. -/
def PEmpty.elim {C : Sort v} (t : PEmpty.{u}) : C := nomatch t

instance : Subsingleton PEmpty := ⟨λ a => a.elim⟩

@[simp] theorem notNonemptyPEmpty : ¬ Nonempty PEmpty :=
λ ⟨h⟩ => h.elim

@[simp] theorem forallPEmpty {P : PEmpty → Prop} : (∀ x : PEmpty, P x) ↔ True :=
⟨λ h => trivial, λ h x => by cases x⟩

@[simp] theorem existsPEmpty {P : PEmpty → Prop} : (∃ x : PEmpty, P x) ↔ False :=
⟨λ ⟨w, hw⟩ => w.elim, False.elim⟩
