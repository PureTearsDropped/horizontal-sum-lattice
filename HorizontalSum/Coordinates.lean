import HorizontalSum.Trace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! # 座標 — 束を数で書く -/

/-! ### 橋 — 「まだ可能なもの」への写像

座標の行き先を確率分布に取ると、`⊔` を写す演算が見つからなかった。
**「まだ可能なもの」の指示関数**に取ると解ける。

    Φ(x) = ↑x = { y : x ⪯ y }        x 以降にまだ可能なもの

`𝓛` は**全体**（＝全1）に写り、`⊔` は**共通部分**（＝成分ごとの積）に写る。
向きは逆になる——**上に行くほど可能性が減る**（§10.6 の座標版）。

ただし `⊓` は写らない。`Φ(x ⊓ y) ⊇ Φ(x) ∪ Φ(y)` だが等号でなく、
**合併してから閉じる**必要がある。`⊔` が局所的（点ごと）なのに対し
`⊓` は大域的である。 -/

/-- まだ可能なもの。 -/
def Phi (x : E ι α) : Set (E ι α) := {y | x ≤ y}

/-- **𝓛 は全 1 に写る。**`Phi ⊥ = univ`。 -/
theorem Phi_bot : Phi (⊥ : E ι α) = Set.univ := by
  ext y; simp [Phi]

/-- **⊔ は共通部分に写る。**「潰す演算が無い」と思っていたものが、これ。 -/
theorem Phi_sup (x y : E ι α) : Phi (x ⊔ y) = Phi x ∩ Phi y := by
  ext z
  simp only [Phi, Set.mem_inter_iff, Set.mem_setOf_eq, sup_le_iff]

/-- **順序が逆になる。**上に行くほど可能性が減る。 -/
theorem Phi_antitone {x y : E ι α} : x ≤ y ↔ Phi y ⊆ Phi x := by
  constructor
  · intro h z hz; exact le_trans h hz
  · intro h; exact h (le_refl y)

/-- 単射。別の元は別の可能性をもつ。 -/
theorem Phi_injective : Function.Injective (Phi : E ι α → Set (E ι α)) := by
  intro x y h
  exact le_antisymm (Phi_antitone.mpr h.ge) (Phi_antitone.mpr h.le)

/-- **違う軸の可能性は 𝓦 でだけ重なる。**共通部分が自動的に潰れる。 -/
theorem Phi_cross_axis {i j : ι} (h : i ≠ j) (a b : α) :
    Phi (E.axis i a : E ι α) ∩ Phi (E.axis j b) = Phi (⊤ : E ι α) := by
  rw [← Phi_sup, axes_join_to_world h]

/-- `⊓` は**含むだけ**。 -/
theorem Phi_inf_superset (x y : E ι α) : Phi x ∪ Phi y ⊆ Phi (x ⊓ y) := by
  intro z hz
  simp only [Phi, Set.mem_union, Set.mem_setOf_eq] at hz ⊢
  rcases hz with hz | hz
  · exact le_trans inf_le_left hz
  · exact le_trans inf_le_right hz

/-- **等号は破れる。**`⊓` の側は点ごとの演算では書けない——
共通の過去まで戻ると、どちらも行かなかった道が開くからである。 -/
theorem Phi_inf_ne {i j : ι} (h : i ≠ j) (a b : α) :
    Phi ((E.axis i a : E ι α) ⊓ E.axis j b) ≠
      Phi (E.axis i a : E ι α) ∪ Phi (E.axis j b) := by
  rw [axes_meet_at_lmonad h, Phi_bot]
  intro hc
  have hb : (⊥ : E ι α) ∈ Phi (E.axis i a) ∪ Phi (E.axis j b) := by
    rw [← hc]; exact Set.mem_univ _
  rcases hb with hh | hh <;> simp [Phi] at hh

/-- 時計は「可能なもの」を並べ替える。 -/
theorem Phi_clock (f : ι → (α ≃o α)) (x y : E ι α) :
    y ∈ Phi (clock f x) ↔ (clockIso f).symm y ∈ Phi x :=
  ((clockIso f).le_symm_apply).symm



/-! ### 二つの記号を分けて繋ぐ — Mathlib の `Ici` / `Iic`

`⪯`（束の順序）と `⊆`（座標の包含）は**別の記号**である。両者を繋ぐのに
新しい公理は要らない——Mathlib の `Set.Ici` / `Set.Iic` の API が
そのまま繋ぎになる。

    ↑x = Set.Ici x = { y : x ⪯ y }        まだ可能なもの（未来側）
    ↓x = Set.Iic x = { y : y ⪯ x }        そこに至れたもの（過去側）

    x ⪯ y  ⟺  ↑y ⊆ ↑x                    未来側は **逆転**
    x ⪯ y  ⟺  ↓x ⊆ ↓y                    過去側は **そのまま**
    ↑(x ⊔ y) = ↑x ∩ ↑y                    ↑ が ⊔ を捉える
    ↓(x ⊓ y) = ↓x ∩ ↓y                    ↓ が ⊓ を捉える

**片方だけでは両方を捉えられない。**⊔ と ⊓ は別の向きを向いている。 -/

/-- `Φ` は Mathlib の `Set.Ici` そのもの。 -/
theorem Phi_eq_Ici (x : E ι α) : Phi x = Set.Ici x := rfl

/-- 過去側。そこに至れたもの。 -/
def Down (x : E ι α) : Set (E ι α) := Set.Iic x

/-- **𝓦 では過去が全体。**（未来側の 𝓛 と鏡） -/
theorem Down_top : Down (⊤ : E ι α) = Set.univ := by
  first
    | exact Set.Iic_top
    | (ext y; simp only [Down, Set.mem_Iic, Set.mem_univ, iff_true]; exact le_top)

/-- **𝓛 では過去が一点。** -/
theorem Down_bot : Down (⊥ : E ι α) = {⊥} := by
  first
    | exact Set.Iic_bot
    | (ext y
       simp only [Down, Set.mem_Iic, Set.mem_singleton_iff]
       exact le_bot_iff)

/-- **↓ は ⊓ を捉える。**（未来側が ⊔ を捉えるのと鏡） -/
theorem Down_inf (x y : E ι α) : Down (x ⊓ y) = Down x ∩ Down y := by
  first
    | exact (Set.Iic_inter_Iic).symm
    | (ext z; simp [Down, le_inf_iff])

/-- **過去側は順序がそのまま。** -/
theorem Down_monotone {x y : E ι α} : x ≤ y ↔ Down x ⊆ Down y := by
  first
    | exact (Set.Iic_subset_Iic).symm
    | (constructor
       · intro h z hz; exact le_trans hz h
       · intro h; exact h (le_refl x))

/-- 過去側は単射。 -/
theorem Down_injective : Function.Injective (Down : E ι α → Set (E ι α)) := by
  intro x y h
  exact le_antisymm (Down_monotone.mpr h.le) (Down_monotone.mpr h.ge)

/-- **⊔ は未来側で、⊓ は過去側で捉わる。**
片方だけでは両方を捉えられない——`⊔` と `⊓` は別の向きを向いている。 -/
theorem two_directions (x y : E ι α) :
    Phi (x ⊔ y) = Phi x ∩ Phi y ∧ Down (x ⊓ y) = Down x ∩ Down y :=
  ⟨Phi_sup x y, Down_inf x y⟩

/-- **𝓛 と 𝓦 は鏡。**未来側では 𝓛 が全体、過去側では 𝓦 が全体。 -/
theorem lmonad_world_mirror :
    Phi (⊥ : E ι α) = Set.univ ∧ Down (⊤ : E ι α) = Set.univ ∧
      Phi (⊤ : E ι α) = {⊤} ∧ Down (⊥ : E ι α) = {⊥} := by
  refine ⟨Phi_bot, Down_top, ?_, Down_bot⟩
  first
    | exact Set.Ici_top
    | (ext y
       simp only [Phi, Set.mem_setOf_eq, Set.mem_singleton_iff]
       exact top_le_iff)

/-! ### 星形 — 軸ごとにまとめた座標 Ψ

`Φ` は束の元ごとに成分をもつ（`|E|` 次元）。それを**軸ごとにまとめる**と、
名札の数だけの成分になる。

    Ψ(x)_g = { a : x ⪯ ⟨g, a⟩ }        軸 g の上で、まだ可能な高さ

こうすると `𝓛` は各成分が**全体**（＝全1）、`𝓦` は各成分が**空**（＝全0）に
なり、間の元は**腕が一本だけ**伸びた形になる。中心から名札の数だけ腕が出る
**星形**である。 -/

/-- 軸 `g` の上で、`x` 以降にまだ可能な高さ。 -/
def Psi (x : E ι α) (g : ι) : Set α := {a | x ≤ E.axis g a}

/-- **𝓛 では各成分が全体。**（＝全1） -/
theorem Psi_bot (g : ι) : Psi (⊥ : E ι α) g = Set.univ := by
  ext a; simp [Psi]

/-- **𝓦 では各成分が空。**（＝全0） -/
theorem Psi_top (g : ι) : Psi (⊤ : E ι α) g = ∅ := by
  ext a; simp [Psi]

/-- **⊔ は成分ごとの共通部分。** -/
theorem Psi_sup (x y : E ι α) (g : ι) :
    Psi (x ⊔ y) g = Psi x g ∩ Psi y g := by
  ext a
  simp only [Psi, Set.mem_inter_iff, Set.mem_setOf_eq, sup_le_iff]

/-- 順序が逆になる。 -/
theorem Psi_antitone {x y : E ι α} (h : x ≤ y) (g : ι) : Psi y g ⊆ Psi x g :=
  fun _ ha => le_trans h ha

/-- **同じ軸には腕が伸びる。** -/
theorem Psi_axis_self (i : ι) (b : α) : Psi (E.axis i b : E ι α) i = {a | b ≤ a} := by
  ext a; simp [Psi]

/-- **他の軸は空。**だから中間の元は腕が一本だけになる。 -/
theorem Psi_axis_other {i g : ι} (h : i ≠ g) (b : α) :
    Psi (E.axis i b : E ι α) g = ∅ := by
  ext a; simp [Psi, h]

/-- **星形。**𝓛 は全成分が全体、軸の元は一本だけ、𝓦 は全成分が空。 -/
theorem star_shape (i : ι) (b : α) (g : ι) :
    Psi (⊥ : E ι α) g = Set.univ ∧
    Psi (E.axis i b : E ι α) g = (if i = g then {a | b ≤ a} else ∅) ∧
    Psi (⊤ : E ι α) g = ∅ := by
  refine ⟨Psi_bot g, ?_, Psi_top g⟩
  by_cases h : i = g
  · subst h; simp [Psi_axis_self]
  · simp [Psi_axis_other h, h]

/-- **Ψ は反順序埋め込み。**成分ごとの包含が、束の順序をちょうど逆に写す。

    x ⪯ y  ⟺  ∀ g, Ψ(y)_g ⊆ Ψ(x)_g

軸が 2 本以上・軸の中が空でないことだけを使う。 -/
theorem Psi_le_iff [Nonempty α] {i j : ι} (hij : i ≠ j) {x y : E ι α} :
    (∀ g, Psi y g ⊆ Psi x g) ↔ x ≤ y := by
  constructor
  · intro h
    rcases x with _ | ⟨p, b⟩ | _
    · exact bot_le
    · rcases y with _ | ⟨q, c⟩ | _
      · obtain ⟨r, hr⟩ : ∃ r : ι, r ≠ p := by
          rcases eq_or_ne p i with rfl | hp
          · exact ⟨j, Ne.symm hij⟩
          · exact ⟨i, Ne.symm hp⟩
        have hmem : (Classical.arbitrary α) ∈ Psi (⊥ : E ι α) r := by
          rw [Psi_bot]; trivial
        have hbad := h r hmem
        rw [Psi_axis_other (Ne.symm hr)] at hbad
        exact absurd hbad (by simp)
      · have hmem : c ∈ Psi (E.axis q c : E ι α) q := by
          rw [Psi_axis_self]; exact le_rfl
        rcases eq_or_ne p q with rfl | hpq
        · have hbc := h p hmem
          rw [Psi_axis_self] at hbc
          exact ⟨rfl, hbc⟩
        · have hbad := h q hmem
          rw [Psi_axis_other hpq] at hbad
          exact absurd hbad (by simp)
      · exact le_top
    · rcases y with _ | ⟨q, c⟩ | _
      · have hmem : (Classical.arbitrary α) ∈ Psi (⊥ : E ι α) i := by
          rw [Psi_bot]; trivial
        have hbad : (Classical.arbitrary α) ∈ Psi (⊤ : E ι α) i := h i hmem
        rw [Psi_top] at hbad
        exact absurd hbad (by simp)
      · have hmem : c ∈ Psi (E.axis q c : E ι α) q := by
          rw [Psi_axis_self]; exact le_rfl
        have hbad : c ∈ Psi (⊤ : E ι α) q := h q hmem
        rw [Psi_top] at hbad
        exact absurd hbad (by simp)
      · exact le_rfl
  · intro h g; exact Psi_antitone h g

/-! ### 逆も言える — 「全 1 テンソルは 𝓛 だけ」

「𝓛 の座標は全 1」は `Phi_bot` で既に定理だが、**逆も定理になる**。
つまり 𝓛 と 𝓦 は「そういう座標をもつ」のではなく、
**そういう座標をもつ唯一の元として特徴づけられる**。 -/

/-- **全 1 テンソルであるのは 𝓛 だけ。** -/
theorem Phi_eq_univ_iff {x : E ι α} : Phi x = Set.univ ↔ x = ⊥ := by
  constructor
  · intro h
    have : (⊥ : E ι α) ∈ Phi x := h ▸ Set.mem_univ _
    exact le_bot_iff.mp this
  · rintro rfl; exact Phi_bot

/-- **過去が全体なのは 𝓦 だけ。** -/
theorem Down_eq_univ_iff {x : E ι α} : Down x = Set.univ ↔ x = ⊤ := by
  constructor
  · intro h
    have : (⊤ : E ι α) ∈ Down x := h ▸ Set.mem_univ _
    exact top_le_iff.mp this
  · rintro rfl; exact Down_top

/-- **one-hot であるのは 𝓦 だけ**（未来側）。 -/
theorem Phi_eq_singleton_iff {x : E ι α} : Phi x = {x} ↔ x = ⊤ := by
  constructor
  · intro h
    have : (⊤ : E ι α) ∈ Phi x := by simp [Phi]
    rw [h] at this
    exact this.symm
  · rintro rfl
    ext y
    simp only [Phi, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => top_le_iff.mp h |>.symm ▸ rfl, fun h => h ▸ le_rfl⟩

/-- **one-hot であるのは 𝓛 だけ**（過去側）。 -/
theorem Down_eq_singleton_iff {x : E ι α} : Down x = {x} ↔ x = ⊥ := by
  constructor
  · intro h
    have : (⊥ : E ι α) ∈ Down x := by simp [Down]
    rw [h] at this
    exact this.symm
  · rintro rfl
    ext y
    simp only [Down, Set.mem_Iic, Set.mem_singleton_iff]
    exact ⟨fun h => le_bot_iff.mp h, fun h => h ▸ le_rfl⟩

end HorizontalSum
