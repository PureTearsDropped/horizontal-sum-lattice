import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

/-- 𝓛 を底、𝓦 を頂とし、その間を `ι` で名付けられた時間軸が渡る。
各軸は `α` の鎖。 -/
inductive E (ι : Type u) (α : Type v) where
  /-- 束の最小元 `⊥`。 -/
  | lmonad : E ι α
  /-- 時間軸 `i` の高さ `a`。 -/
  | axis : ι → α → E ι α
  /-- 束の最大元 `⊤`。 -/
  | world : E ι α

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-- 順序。別の軸どうしは比較できない。 -/
def E.le : E ι α → E ι α → Prop
  | .lmonad, _ => True
  | .axis _ _, .lmonad => False
  | .axis i a, .axis j b => i = j ∧ a ≤ b
  | .axis _ _, .world => True
  | .world, .lmonad => False
  | .world, .axis _ _ => False
  | .world, .world => True

/-- 結び。別の軸どうしは 𝓦 まで飛ぶ。 -/
def E.sup : E ι α → E ι α → E ι α
  | .lmonad, y => y
  | .axis i a, .lmonad => .axis i a
  | .axis i a, .axis j b => if i = j then .axis i (a ⊔ b) else .world
  | .axis _ _, .world => .world
  | .world, _ => .world

/-- 交わり。別の軸どうしは 𝓛 まで落ちる。 -/
def E.inf : E ι α → E ι α → E ι α
  | .lmonad, _ => .lmonad
  | .axis _ _, .lmonad => .lmonad
  | .axis i a, .axis j b => if i = j then .axis i (a ⊓ b) else .lmonad
  | .axis i a, .world => .axis i a
  | .world, y => y

@[simp] theorem lmonad_le (y : E ι α) : E.le E.lmonad y := trivial
@[simp] theorem le_world (x : E ι α) : E.le x E.world := by cases x <;> trivial
@[simp] theorem axis_le_axis {i j : ι} {a b : α} :
    E.le (E.axis i a) (E.axis j b) ↔ i = j ∧ a ≤ b := Iff.rfl
@[simp] theorem not_axis_le_lmonad {i : ι} {a : α} :
    ¬ E.le (E.axis i a : E ι α) E.lmonad := id
@[simp] theorem not_world_le_lmonad : ¬ E.le (E.world : E ι α) E.lmonad := id
@[simp] theorem not_world_le_axis {i : ι} {a : α} :
    ¬ E.le (E.world : E ι α) (E.axis i a) := id

@[simp] theorem lmonad_sup (y : E ι α) : E.sup E.lmonad y = y := rfl
@[simp] theorem sup_lmonad (x : E ι α) : E.sup x E.lmonad = x := by cases x <;> rfl
@[simp] theorem world_sup (y : E ι α) : E.sup E.world y = E.world := rfl
@[simp] theorem sup_world (x : E ι α) : E.sup x E.world = E.world := by cases x <;> rfl
@[simp] theorem axis_sup_axis {i j : ι} {a b : α} :
    E.sup (E.axis i a) (E.axis j b)
      = if i = j then E.axis i (a ⊔ b) else E.world := rfl

@[simp] theorem lmonad_inf (y : E ι α) : E.inf E.lmonad y = E.lmonad := rfl
@[simp] theorem inf_lmonad (x : E ι α) : E.inf x E.lmonad = E.lmonad := by cases x <;> rfl
@[simp] theorem world_inf (y : E ι α) : E.inf E.world y = y := rfl
@[simp] theorem inf_world (x : E ι α) : E.inf x E.world = x := by cases x <;> rfl
@[simp] theorem axis_inf_axis {i j : ι} {a b : α} :
    E.inf (E.axis i a) (E.axis j b)
      = if i = j then E.axis i (a ⊓ b) else E.lmonad := rfl

instance instLattice : Lattice (E ι α) where
  le := E.le
  le_refl x := by cases x <;> simp
  le_trans := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) (_ | ⟨k, c⟩ | _) h₁ h₂
    all_goals first
      | exact trivial
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim
      | (obtain ⟨rfl, hab⟩ := h₁; obtain ⟨rfl, hbc⟩ := h₂
         exact ⟨rfl, le_trans hab hbc⟩)
  le_antisymm := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) h₁ h₂
    all_goals first
      | rfl
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim
      | (obtain ⟨rfl, hab⟩ := h₁; obtain ⟨-, hba⟩ := h₂
         exact congrArg _ (le_antisymm hab hba))
  sup := E.sup
  le_sup_left := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) <;> simp
    split <;> simp_all
  le_sup_right := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) <;> simp
    split <;> simp_all
  sup_le := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) (_ | ⟨k, c⟩ | _) h₁ h₂ <;> simp_all
  inf := E.inf
  inf_le_left := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) <;> simp
    split <;> simp_all
  inf_le_right := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) <;> simp
    split <;> simp_all
  le_inf := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) (_ | ⟨k, c⟩ | _) h₁ h₂ <;> simp_all

instance instBoundedOrder : BoundedOrder (E ι α) where
  bot := E.lmonad
  bot_le _ := trivial
  top := E.world
  le_top x := by cases x <;> trivial

@[simp] theorem bot_def : (⊥ : E ι α) = E.lmonad := rfl
@[simp] theorem top_def : (⊤ : E ι α) = E.world := rfl

@[simp] theorem le_iff {x y : E ι α} : x ≤ y ↔ E.le x y := Iff.rfl
@[simp] theorem sup_def (x y : E ι α) : x ⊔ y = E.sup x y := rfl
@[simp] theorem inf_def (x y : E ι α) : x ⊓ y = E.inf x y := rfl

/-! # 土台と骨格 — 束を作り、W^θ = W^φ を出す -/

/-! ## W = W⁻¹ = W^i = W^(−i) -/

/-- **四つの方向はただ一つの 𝓦 を共有する。**
どの二つの時間軸も、上では同じ 𝓦 で出会う。これが
`W = W⁻¹ = W^i = W^(−i)` の内容。 -/
theorem axes_join_to_world {i j : ι} (h : i ≠ j) (a b : α) :
    (E.axis i a : E ι α) ⊔ E.axis j b = ⊤ := by simp [h]

/-- 双対。四つの方向は下では 𝓛 でだけ出会う。 -/
theorem axes_meet_at_lmonad {i j : ι} (h : i ≠ j) (a b : α) :
    (E.axis i a : E ι α) ⊓ E.axis j b = ⊥ := by simp [h]

/-- 同じ軸の上では、束の演算は軸の中で閉じる。 -/
theorem same_axis_sup (i : ι) (a b : α) :
    (E.axis i a : E ι α) ⊔ E.axis i b = E.axis i (a ⊔ b) := by simp

theorem same_axis_inf (i : ι) (a b : α) :
    (E.axis i a : E ι α) ⊓ E.axis i b = E.axis i (a ⊓ b) := by simp

/-! ### 台を既存の構成で書く — `WithBot (WithTop (Σ i, α))`

`E ι α` は独自の帰納型だが、**Mathlib の標準構成の合成**である。

    Σ _ : ι, α           軸ごとの直和。Mathlib の順序は
                         `⟨i,a⟩ ≤ ⟨j,b⟩ ↔ i = j ∧ a ≤ b`（`Sigma.instPartialOrder`）
                         ＝ §1.1 の「別の軸の元どうしは比較できない」そのもの
    WithTop (·)          `𝓦` を足す
    WithBot (WithTop ·)  `𝓛` を足す

つまり **`E ι α ≃o WithBot (WithTop (Σ _ : ι, α))`**。独自の演算子ではなく、
既存の三つの構成を重ねただけである。 -/

/-- 台の標準形への写像。 -/
def toStd : E ι α → WithBot (WithTop (Σ _ : ι, α))
  | .lmonad => ⊥
  | .axis i a => (((⟨i, a⟩ : Σ _ : ι, α) : WithTop (Σ _ : ι, α)) : WithBot _)
  | .world => ((⊤ : WithTop (Σ _ : ι, α)) : WithBot _)

/-- 逆写像。 -/
def ofStd : WithBot (WithTop (Σ _ : ι, α)) → E ι α
  | none => .lmonad
  | some none => .world
  | some (some p) => .axis p.1 p.2

@[simp] theorem ofStd_toStd (x : E ι α) : ofStd (toStd x) = x := by
  rcases x with _ | ⟨i, a⟩ | _ <;> rfl

@[simp] theorem toStd_ofStd (x : WithBot (WithTop (Σ _ : ι, α))) :
    toStd (ofStd x) = x := by
  rcases x with _ | x
  · rfl
  · rcases x with _ | p <;> rfl

/-- 順序が保たれること。`WithBot`/`WithTop` の標準補題だけで出る。 -/
theorem toStd_le_iff (x y : E ι α) : toStd x ≤ toStd y ↔ x ≤ y := by
  have hsig : ∀ (i j : ι) (a b : α),
      ((⟨i, a⟩ : Σ _ : ι, α) ≤ ⟨j, b⟩) ↔ (i = j ∧ a ≤ b) := by
    intro i j a b
    by_cases hij : i = j
    · subst hij
      refine ⟨fun h => ⟨rfl, ?_⟩, fun h => ?_⟩
      · exact (@Sigma.mk_le_mk_iff ι (fun _ => α) _ i a b).mp h
      · exact (@Sigma.mk_le_mk_iff ι (fun _ => α) _ i a b).mpr h.2
    · refine ⟨fun h => absurd ?_ hij, fun h => absurd h.1 hij⟩
      rw [Sigma.le_def] at h
      exact h.1
  rcases x with _ | ⟨i, a⟩ | _ <;> rcases y with _ | ⟨j, b⟩ | _ <;>
    simp [toStd, E.le, hsig]

/-- **台は標準構成そのもの。**`𝓛` と `𝓦` を足した軸の直和である。 -/
def stdEquiv : E ι α ≃o WithBot (WithTop (Σ _ : ι, α)) where
  toFun := toStd
  invFun := ofStd
  left_inv := ofStd_toStd
  right_inv := toStd_ofStd
  map_rel_iff' := toStd_le_iff _ _

theorem stdEquiv_lmonad : stdEquiv (E.lmonad : E ι α) = ⊥ := rfl
theorem stdEquiv_world :
    stdEquiv (E.world : E ι α) = ((⊤ : WithTop (Σ _ : ι, α)) : WithBot _) := rfl
theorem stdEquiv_axis (i : ι) (a : α) :
    stdEquiv (E.axis i a : E ι α)
      = (((⟨i, a⟩ : Σ _ : ι, α) : WithTop (Σ _ : ι, α)) : WithBot _) := rfl

end HorizontalSum
