import HorizontalSum.Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 四つ組の結びと交わり — 一致するのは両端だけ

四つ組 `A^θ, i·A^θ, −A^θ, −i·A^θ` は、**途中では相異なる四本の軸に居る**。
等しくなるのは `𝓛`（半径 0）と `𝓦`（半径 ∞）だけ。

途中で成り立つのは等式ではなく、**結ぶと 𝓦・交わると 𝓛 で揃う**ことである。 -/

/-- `ℤ/4` では `k` と `k+1, k+2, k+3` はすべて相異なる。 -/
theorem zmod_four_ne (k : ZMod 4) : k ≠ k + 1 ∧ k ≠ k + 2 ∧ k ≠ k + 3 := by
  revert k; decide

/-- `×i` は名札を一つ進める。 -/
theorem rot_axis (k : ZMod 4) (a : α) :
    rot (E.axis k a : Four α) = E.axis (k + 1) a := rfl

/-- 両端では `×i` は何もしない。**四つが一致するのはここだけ。** -/
theorem rot_bot : rot (⊥ : Four α) = ⊥ := rfl

theorem rot_top : rot (⊤ : Four α) = ⊤ := rfl

/-- 途中では `A^θ ≠ i·A^θ`。**四つは別の元である。** -/
theorem rot_ne_self (k : ZMod 4) (a : α) :
    rot (E.axis k a : Four α) ≠ E.axis k a := fun h => by
  rw [rot_axis, E.axis.injEq] at h
  exact (zmod_four_ne k).1 h.1.symm

/-- **A^θ ⊔ (i·A^θ) = A^θ ⊔ (−A^θ) = A^θ ⊔ (−i·A^θ) = 𝓦。**
四つ組は、結ぶとどれも 𝓦 になる。 -/
theorem quad_join_to_world (k : ZMod 4) (a b : α) :
    ((E.axis k a : Four α) ⊔ E.axis (k + 1) b = ⊤) ∧
    ((E.axis k a : Four α) ⊔ E.axis (k + 2) b = ⊤) ∧
    ((E.axis k a : Four α) ⊔ E.axis (k + 3) b = ⊤) :=
  ⟨axes_join_to_world (zmod_four_ne k).1 a b,
   axes_join_to_world (zmod_four_ne k).2.1 a b,
   axes_join_to_world (zmod_four_ne k).2.2 a b⟩

/-- **A^θ ⊓ (i·A^θ) = A^θ ⊓ (−A^θ) = A^θ ⊓ (−i·A^θ) = 𝓛。**
四つ組は、交わるとどれも 𝓛 になる。 -/
theorem quad_meet_at_lmonad (k : ZMod 4) (a b : α) :
    ((E.axis k a : Four α) ⊓ E.axis (k + 1) b = ⊥) ∧
    ((E.axis k a : Four α) ⊓ E.axis (k + 2) b = ⊥) ∧
    ((E.axis k a : Four α) ⊓ E.axis (k + 3) b = ⊥) :=
  ⟨axes_meet_at_lmonad (zmod_four_ne k).1 a b,
   axes_meet_at_lmonad (zmod_four_ne k).2.1 a b,
   axes_meet_at_lmonad (zmod_four_ne k).2.2 a b⟩

/-- `×i` を使った形。`A ⊔ (i·A) = 𝓦`、`A ⊓ (i·A) = 𝓛`。 -/
theorem rot_join_meet (k : ZMod 4) (a : α) :
    ((E.axis k a : Four α) ⊔ rot (E.axis k a) = ⊤) ∧
    ((E.axis k a : Four α) ⊓ rot (E.axis k a) = ⊥) := by
  rw [rot_axis]
  exact ⟨axes_join_to_world (zmod_four_ne k).1 a a,
         axes_meet_at_lmonad (zmod_four_ne k).1 a a⟩

end HorizontalSum
