import HorizontalSum.Bridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

/-! # 水平和 — Mathlib に無い構成を一般形で

§13.8 の棚卸しで、既存構成に落ちなかったのは `E.sup` / `E.inf` だけだった。
その正体は**水平和**（horizontal sum）である。ここでは軸ごとに型が違ってよい
一般形で定義し、束になる条件を証明する。

    Sigma に束のインスタンス   無い（直和は束でない。別成分に上限が無い）
    Sum.Lex（α ⊕ₗ β）         縦積み（α の全部が β の下）で別物
    WithTop.lattice           台が**既に束**であることを要求

⟹ 「束でない半順序に `⊥`,`⊤` を足して束にする」構成が Mathlib に無い。 -/

namespace Family

variable {ι : Type u} [DecidableEq ι] {P : ι → Type v}

/-- 水平和。軸ごとに型が違ってよい。 -/
inductive T (ι : Type u) (P : ι → Type v) where
  | bot : T ι P
  | mid : ∀ i, P i → T ι P
  | top : T ι P

section Order

variable [∀ i, PartialOrder (P i)]

/-- 順序。**別の軸の元どうしは比較できない。** -/
def le : T ι P → T ι P → Prop
  | .bot, _ => True
  | .mid _ _, .bot => False
  | .mid i a, .mid j b => ∃ h : i = j, (h ▸ a) ≤ b
  | .mid _ _, .top => True
  | .top, .bot => False
  | .top, .mid _ _ => False
  | .top, .top => True

instance : LE (T ι P) := ⟨le⟩

theorem le_refl' (x : T ι P) : le x x := by
  rcases x with _ | ⟨i, a⟩ | _
  · trivial
  · exact ⟨rfl, le_rfl⟩
  · trivial

theorem le_trans' {x y z : T ι P} (h₁ : le x y) (h₂ : le y z) : le x z := by
  rcases x with _ | ⟨i, a⟩ | _ <;> rcases y with _ | ⟨j, b⟩ | _ <;>
    rcases z with _ | ⟨k, c⟩ | _ <;>
    first
      | trivial
      | exact h₁.elim
      | exact h₂.elim
      | (obtain ⟨rfl, hab⟩ := h₁
         obtain ⟨rfl, hbc⟩ := h₂
         exact ⟨rfl, hab.trans hbc⟩)

theorem le_antisymm' {x y : T ι P} (h₁ : le x y) (h₂ : le y x) : x = y := by
  rcases x with _ | ⟨i, a⟩ | _ <;> rcases y with _ | ⟨j, b⟩ | _ <;>
    first
      | rfl
      | exact h₁.elim
      | exact h₂.elim
      | (obtain ⟨rfl, hab⟩ := h₁
         obtain ⟨e, hba⟩ := h₂
         have hba' : b ≤ a := by simpa using hba
         exact congrArg _ (le_antisymm hab hba'))

instance : PartialOrder (T ι P) where
  le := le
  le_refl := le_refl'
  le_trans := fun _ _ _ => le_trans'
  le_antisymm := fun _ _ => le_antisymm'

instance : OrderBot (T ι P) where
  bot := .bot
  bot_le := fun _ => trivial

instance : OrderTop (T ι P) where
  top := .top
  le_top := by
    rintro (_ | ⟨i, a⟩ | _) <;> trivial

instance : BoundedOrder (T ι P) := ⟨⟩

/-- **同じ軸なら軸の順序、別の軸なら比較不能。**これが「水平」の意味。 -/
theorem mid_le_mid_iff {i j : ι} (a : P i) (b : P j) :
    (T.mid i a : T ι P) ≤ T.mid j b ↔ ∃ h : i = j, (h ▸ a) ≤ b := Iff.rfl

theorem mid_incomparable {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    ¬ ((T.mid i a : T ι P) ≤ T.mid j b) := fun ⟨e, _⟩ => h e

/-- 同じ軸なら、順序はそのまま軸の順序。 -/
theorem mid_le_mid {i : ι} {a b : P i} :
    (T.mid i a : T ι P) ≤ T.mid i b ↔ a ≤ b := by
  constructor
  · rintro ⟨e, h⟩; simpa using h
  · intro h; exact ⟨rfl, h⟩

/-- 軸の元より上に在るのは、**同じ軸の上か `⊤` だけ**。 -/
theorem mid_le_iff {i : ι} {a : P i} {y : T ι P} :
    (T.mid i a : T ι P) ≤ y ↔ y = ⊤ ∨ ∃ c : P i, y = T.mid i c ∧ a ≤ c := by
  rcases y with _ | ⟨j, c⟩ | _
  · exact ⟨fun h => h.elim, by rintro (h | ⟨c, h, _⟩) <;> exact absurd h (by simp [Top.top])⟩
  · constructor
    · rintro ⟨rfl, h⟩; exact Or.inr ⟨c, rfl, by simpa using h⟩
    · rintro (h | ⟨d, h, hd⟩)
      · exact absurd h (by simp [Top.top])
      · cases h; exact mid_le_mid.2 hd
  · exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩

/-- 軸の元より下に在るのは、**同じ軸の下か `⊥` だけ**。 -/
theorem le_mid_iff {i : ι} {c : P i} {x : T ι P} :
    x ≤ (T.mid i c : T ι P) ↔ x = ⊥ ∨ ∃ a : P i, x = T.mid i a ∧ a ≤ c := by
  rcases x with _ | ⟨j, a⟩ | _
  · exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  · constructor
    · rintro ⟨rfl, h⟩; exact Or.inr ⟨a, rfl, by simpa using h⟩
    · rintro (h | ⟨d, h, hd⟩)
      · exact absurd h (by simp [Bot.bot])
      · cases h; exact mid_le_mid.2 hd
  · exact ⟨fun h => h.elim, by rintro (h | ⟨a, h, _⟩) <;> exact absurd h (by simp [Bot.bot])⟩

/-! ## 束になる条件 — 十分だが必要でない

上の `instLattice` は「各 `P i` が束」を仮定した。**これは必要条件ではない。**
上限が在るかどうかは `IsLUB`（Mathlib）で書ける。次の三つが全体を決める。 -/

/-- 同じ軸の上限は、軸の中の上限そのもの。**両向き。** -/
theorem mid_isLUB_iff (i : ι) (a b c : P i) :
    IsLUB {(T.mid i a : T ι P), T.mid i b} (T.mid i c) ↔ IsLUB {a, b} c := by
  constructor
  · rintro ⟨hub, hlst⟩
    refine ⟨?_, fun d hd => ?_⟩
    · rintro x (rfl | rfl)
      · exact mid_le_mid.1 (hub (by simp))
      · exact mid_le_mid.1 (hub (by simp))
    · refine mid_le_mid.1 (hlst ?_)
      rintro x (rfl | rfl)
      · exact mid_le_mid.2 (hd (by simp))
      · exact mid_le_mid.2 (hd (by simp))
  · rintro ⟨hub, hlst⟩
    refine ⟨?_, fun y hy => ?_⟩
    · rintro x (rfl | rfl)
      · exact mid_le_mid.2 (hub (by simp))
      · exact mid_le_mid.2 (hub (by simp))
    · rcases mid_le_iff.1 (hy (by simp : (T.mid i a : T ι P) ∈ _)) with h | ⟨d, rfl, hd⟩
      · subst h; exact le_top
      · exact mid_le_mid.2 (hlst (by
          rintro x (rfl | rfl)
          · exact hd
          · exact mid_le_mid.1 (hy (by simp))))

/-- **軸をまたぐと上限は必ず `⊤`。**軸の中身に依らない。 -/
theorem cross_isLUB {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    IsLUB {(T.mid i a : T ι P), T.mid j b} ⊤ := by
  refine ⟨fun x _ => le_top, fun y hy => ?_⟩
  rcases mid_le_iff.1 (hy (by simp : (T.mid i a : T ι P) ∈ _)) with rfl | ⟨c, rfl, _⟩
  · exact le_rfl
  · exact absurd (hy (by simp : (T.mid j b : T ι P) ∈ _)) (mid_incomparable (Ne.symm h) _ _)

/-- **軸をまたぐと下限は必ず `⊥`。** -/
theorem cross_isGLB {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    IsGLB {(T.mid i a : T ι P), T.mid j b} ⊥ := by
  refine ⟨fun x _ => bot_le, fun y hy => ?_⟩
  rcases le_mid_iff.1 (hy (by simp : (T.mid i a : T ι P) ∈ _)) with rfl | ⟨c, rfl, _⟩
  · exact le_rfl
  · exact absurd (hy (by simp : (T.mid j b : T ι P) ∈ _)) (mid_incomparable h _ _)

end Order

/-! ## 反例 — 「各成分が束」は必要でない

二元の反鎖 `Two` は束でない（`a`,`b` に上界が無い）。しかし水平和を取ると
四元のダイヤモンド `M2` になり、これは束である。**⊤ が上限を肩代わりする。**

正しい必要十分条件は「各 `P i` が束」ではなく

    **各 `P i` で、上界を持つ対には最小上界が在る**（下も同様）

である。上界が一つも無い対は `⊤` が引き受けるので、束である必要がない。 -/

/-- 二元の反鎖。 -/
inductive Two where
  | a : Two
  | b : Two
  deriving DecidableEq

instance : PartialOrder Two where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

/-- `Two` は束でない。`a` と `b` に上界が無い。 -/
theorem two_not_lattice : ¬ ∃ c : Two, IsLUB {Two.a, Two.b} c := by
  rintro ⟨c, hub, -⟩
  have h₁ : Two.a = c := hub (by simp)
  have h₂ : Two.b = c := hub (by simp)
  exact Two.noConfusion (h₁.trans h₂.symm)

/-- それでも水平和は上限を持つ。**`⊤` が肩代わりする。** -/
theorem two_hsum_has_lub :
    IsLUB {(T.mid () Two.a : T Unit fun _ => Two), T.mid () Two.b} ⊤ := by
  refine ⟨fun x _ => le_top, fun y hy => ?_⟩
  rcases mid_le_iff.1 (hy (by simp : (T.mid () Two.a : T Unit fun _ => Two) ∈ _)) with rfl | ⟨c, rfl, hc⟩
  · exact le_rfl
  · have := mid_le_mid.1 (hy (by simp : (T.mid () Two.b : T Unit fun _ => Two) ∈ _))
    exact Two.noConfusion ((hc : Two.a = c).trans (this : Two.b = c).symm)

section Lattice

variable [∀ i, Lattice (P i)]

/-- 結び。**同じ軸なら軸の中で、別の軸なら `⊤` まで飛ぶ。** -/
def sup : T ι P → T ι P → T ι P
  | .bot, y => y
  | .mid i a, .bot => .mid i a
  | .mid i a, .mid j b => if h : i = j then .mid j ((h ▸ a) ⊔ b) else .top
  | .mid _ _, .top => .top
  | .top, _ => .top

/-- 交わり。**別の軸なら `⊥` まで落ちる。** -/
def inf : T ι P → T ι P → T ι P
  | .bot, _ => .bot
  | .mid _ _, .bot => .bot
  | .mid i a, .mid j b => if h : i = j then .mid j ((h ▸ a) ⊓ b) else .bot
  | .mid i a, .top => .mid i a
  | .top, y => y

theorem sup_same (i : ι) (a b : P i) :
    sup (T.mid i a) (T.mid i b) = T.mid i (a ⊔ b) := by
  simp [sup]

theorem sup_diff {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    sup (T.mid i a) (T.mid j b) = T.top := by
  simp [sup, h]

theorem inf_same (i : ι) (a b : P i) :
    inf (T.mid i a) (T.mid i b) = T.mid i (a ⊓ b) := by
  simp [inf]

theorem inf_diff {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    inf (T.mid i a) (T.mid j b) = T.bot := by
  simp [inf, h]

theorem le_sup_left' (x y : T ι P) : le x (sup x y) := by
  rcases x with _ | ⟨i, a⟩ | _
  · trivial
  · rcases y with _ | ⟨j, b⟩ | _
    · exact le_refl' _
    · by_cases h : i = j
      · subst h; rw [sup_same]; exact ⟨rfl, le_sup_left⟩
      · rw [sup_diff h]; trivial
    · trivial
  · trivial

theorem le_sup_right' (x y : T ι P) : le y (sup x y) := by
  rcases x with _ | ⟨i, a⟩ | _
  · exact le_refl' _
  · rcases y with _ | ⟨j, b⟩ | _
    · trivial
    · by_cases h : i = j
      · subst h; rw [sup_same]; exact ⟨rfl, le_sup_right⟩
      · rw [sup_diff h]; trivial
    · trivial
  · rcases y with _ | ⟨j, b⟩ | _ <;> trivial

theorem sup_le' {x y z : T ι P} (h₁ : le x z) (h₂ : le y z) : le (sup x y) z := by
  rcases x with _ | ⟨i, a⟩ | _
  · exact h₂
  · rcases y with _ | ⟨j, b⟩ | _
    · exact h₁
    · rcases z with _ | ⟨k, c⟩ | _
      · exact h₁.elim
      · obtain ⟨rfl, hac⟩ := h₁
        obtain ⟨rfl, hbc⟩ := h₂
        rw [sup_same]
        exact ⟨rfl, sup_le (by simpa using hac) (by simpa using hbc)⟩
      · exact le_top (α := T ι P)
    · rcases z with _ | ⟨k, c⟩ | _
      · exact h₂.elim
      · exact h₂.elim
      · trivial
  · rcases z with _ | ⟨k, c⟩ | _
    · exact h₁.elim
    · exact h₁.elim
    · trivial

theorem inf_le_left' (x y : T ι P) : le (inf x y) x := by
  rcases x with _ | ⟨i, a⟩ | _
  · trivial
  · rcases y with _ | ⟨j, b⟩ | _
    · trivial
    · by_cases h : i = j
      · subst h; rw [inf_same]; exact ⟨rfl, inf_le_left⟩
      · rw [inf_diff h]; trivial
    · exact le_refl' _
  · exact le_top (α := T ι P)

theorem inf_le_right' (x y : T ι P) : le (inf x y) y := by
  rcases x with _ | ⟨i, a⟩ | _
  · trivial
  · rcases y with _ | ⟨j, b⟩ | _
    · trivial
    · by_cases h : i = j
      · subst h; rw [inf_same]; exact ⟨rfl, inf_le_right⟩
      · rw [inf_diff h]; trivial
    · trivial
  · exact le_refl' _

theorem le_inf' {x y z : T ι P} (h₁ : le x y) (h₂ : le x z) : le x (inf y z) := by
  rcases x with _ | ⟨i, a⟩ | _
  · trivial
  · rcases y with _ | ⟨j, b⟩ | _
    · exact h₁.elim
    · rcases z with _ | ⟨k, c⟩ | _
      · exact h₂.elim
      · obtain ⟨rfl, hab⟩ := h₁
        obtain ⟨rfl, hac⟩ := h₂
        rw [inf_same]
        exact ⟨rfl, le_inf (by simpa using hab) (by simpa using hac)⟩
      · exact h₁
    · rcases z with _ | ⟨k, c⟩ | _
      · exact h₂.elim
      · exact h₂
      · exact h₁
  · rcases y with _ | ⟨j, b⟩ | _
    · exact h₁.elim
    · exact h₁.elim
    · rcases z with _ | ⟨k, c⟩ | _
      · exact h₂.elim
      · exact h₂.elim
      · trivial

/-- **各成分が束なら、水平和も束。**これが Mathlib に無い構成である。

`Sigma` に束の構造は無く、`WithTop.lattice` は台が既に束であることを要求する。
「束でない半順序に `⊥`,`⊤` を足して束にする」構成はどちらでも作れない。 -/
instance instLattice : Lattice (T ι P) where
  sup := sup
  inf := inf
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := fun _ _ _ => sup_le'
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := fun _ _ _ => le_inf'

/-- **軸をまたぐ結びは `⊤`。**これが `W^θ ⊔ W^φ = 𝓦` の一般形。 -/
theorem sup_cross {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    (T.mid i a : T ι P) ⊔ T.mid j b = ⊤ := sup_diff h a b

/-- **軸をまたぐ交わりは `⊥`。** -/
theorem inf_cross {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    (T.mid i a : T ι P) ⊓ T.mid j b = ⊥ := inf_diff h a b

/-- 軸の中では、束の演算はそのまま軸の演算である。 -/
theorem sup_inside (i : ι) (a b : P i) :
    (T.mid i a : T ι P) ⊔ T.mid i b = T.mid i (a ⊔ b) := sup_same i a b

theorem inf_inside (i : ι) (a b : P i) :
    (T.mid i a : T ι P) ⊓ T.mid i b = T.mid i (a ⊓ b) := inf_same i a b

end Lattice

end Family


/-! ## `E ι α` は水平和の特殊形

軸の型が全部同じ（`P = fun _ => α`）ときが `E ι α` である。`stdEquiv` が
「台が `WithBot (WithTop (Σ))` である」ことを示したのに対し、こちらは
**束の構造まで込みで**一致することを示す。 -/

namespace Family

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-- `E ι α → T ι (fun _ => α)`。構造をそのまま写す。 -/
def ofE : E ι α → T ι (fun _ => α)
  | .lmonad => .bot
  | .axis i a => .mid i a
  | .world => .top

def toE : T ι (fun _ => α) → E ι α
  | .bot => .lmonad
  | .mid i a => .axis i a
  | .top => .world

theorem toE_ofE (x : E ι α) : toE (ofE x) = x := by cases x <;> rfl
theorem ofE_toE (x : T ι (fun _ => α)) : ofE (toE x) = x := by cases x <;> rfl

theorem ofE_le_iff (x y : E ι α) : ofE x ≤ ofE y ↔ x ≤ y := by
  rcases x with _ | ⟨i, a⟩ | _ <;> rcases y with _ | ⟨j, b⟩ | _
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact ⟨fun ⟨e, h⟩ => ⟨e, by simpa using h⟩, fun ⟨e, h⟩ => ⟨e, by simpa using h⟩⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- **`E ι α` は水平和の「全軸が同じ型」の場合。**順序同型であり、
`OrderIso` なので `⊔`,`⊓`,`⊥`,`⊤` はすべて自動で保たれる。 -/
def eEquiv : E ι α ≃o T ι (fun _ => α) where
  toFun := ofE
  invFun := toE
  left_inv := toE_ofE
  right_inv := ofE_toE
  map_rel_iff' := ofE_le_iff _ _

@[simp] theorem eEquiv_lmonad : eEquiv (E.lmonad : E ι α) = ⊥ := rfl
@[simp] theorem eEquiv_axis (i : ι) (a : α) :
    eEquiv (E.axis i a : E ι α) = T.mid i a := rfl
@[simp] theorem eEquiv_world : eEquiv (E.world : E ι α) = ⊤ := rfl

/-- 結びが写ること。`OrderIso.map_sup` の具体化。 -/
theorem eEquiv_sup (x y : E ι α) : eEquiv (x ⊔ y) = eEquiv x ⊔ eEquiv y :=
  eEquiv.map_sup x y

theorem eEquiv_inf (x y : E ι α) : eEquiv (x ⊓ y) = eEquiv x ⊓ eEquiv y :=
  eEquiv.map_inf x y

end Family

end HorizontalSum
