import HorizontalSum.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! # 名札の対称性 — 回転・群・相対位相・四つ組・十六成分 -/

/-! ## 名札の対称性 — 回転 ×i と共役 -/

/-- 軸の名札の入れ替えは順序同型。`ZMod 4` に取れば
`×i`（回転）も共役 `k ↦ −k` もこれ。 -/
def ofAxisEquiv (e : ι ≃ ι) : E ι α ≃o E ι α where
  toFun x := match x with
    | .lmonad => .lmonad
    | .axis i a => .axis (e i) a
    | .world => .world
  invFun x := match x with
    | .lmonad => .lmonad
    | .axis i a => .axis (e.symm i) a
    | .world => .world
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_rel_iff' := by rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) <;> simp

@[simp] theorem ofAxisEquiv_lmonad (e : ι ≃ ι) :
    ofAxisEquiv (α := α) e E.lmonad = E.lmonad := rfl
@[simp] theorem ofAxisEquiv_axis (e : ι ≃ ι) (i : ι) (a : α) :
    ofAxisEquiv (α := α) e (E.axis i a) = E.axis (e i) a := rfl
@[simp] theorem ofAxisEquiv_world (e : ι ≃ ι) :
    ofAxisEquiv (α := α) e E.world = E.world := rfl

/-- 四方向 `1, i, −1, −i`。 -/
abbrev Four (α : Type v) := E (ZMod 4) α

/-- `×i`（一つ回す）。 -/
def rot : Four α ≃o Four α := ofAxisEquiv (Equiv.addRight (1 : ZMod 4))

/-- 共役 `k ↦ −k`。 -/
def conj : Four α ≃o Four α := ofAxisEquiv (Equiv.neg (ZMod 4))

/-- 共役は対合。 -/
theorem conj_involutive : Function.Involutive (conj : Four α → Four α) := by
  rintro (_ | ⟨i, a⟩ | _) <;> simp [conj]

/-- `×i` を四回で元に戻る。 -/
theorem rot_pow_four (x : Four α) : rot (rot (rot (rot x))) = x := by
  cases x with
  | lmonad => rfl
  | world => rfl
  | axis i a =>
      show E.axis (i + 1 + 1 + 1 + 1) a = E.axis i a
      congr 1
      revert i
      decide

end HorizontalSum
