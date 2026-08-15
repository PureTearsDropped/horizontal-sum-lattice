import HorizontalSum.Family

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! # 代償 — この束が支払うもの -/

/-! ## 代償 — 分配でもモジュラでもない -/

/-- **分配律が破れる。**原因は別々の軸が 𝓦 まで飛ぶこと。 -/
theorem not_distributive {i j : ι} (hij : i ≠ j) {a c : α} (hac : ¬ a ≤ c) (b : α) :
    (E.axis i a : E ι α) ⊓ (E.axis j b ⊔ E.axis i c) ≠
      ((E.axis i a : E ι α) ⊓ E.axis j b) ⊔ ((E.axis i a : E ι α) ⊓ E.axis i c) := by
  rw [axes_join_to_world (Ne.symm hij), axes_meet_at_lmonad hij, same_axis_inf,
    inf_top_eq, bot_sup_eq]
  intro h
  rw [E.axis.injEq] at h
  exact hac ((le_of_eq h.2).trans inf_le_right)

/-- **モジュラ律も破れる。** -/
theorem not_modular {i j : ι} (hij : i ≠ j) {a c : α} (hac : a ≤ c) (hne : a ≠ c)
    (b : α) :
    (E.axis i a : E ι α) ⊔ ((E.axis j b : E ι α) ⊓ E.axis i c) ≠
      ((E.axis i a : E ι α) ⊔ E.axis j b) ⊓ E.axis i c := by
  rw [axes_meet_at_lmonad (Ne.symm hij), axes_join_to_world hij, sup_bot_eq,
    top_inf_eq]
  intro h
  rw [E.axis.injEq] at h
  exact hne h.2

end HorizontalSum
