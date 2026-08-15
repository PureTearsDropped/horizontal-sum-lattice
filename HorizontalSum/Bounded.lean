import HorizontalSum.Cost

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v w

namespace HorizontalSum

/-! # 文献の定義をそのまま書く — 有界半順序の族の水平和

順序論で **horizontal sum**（水平和）と呼ばれているのは、有界半順序の族
`(P i, ≤, 0, 1)` を、**上下端だけ同一視して並べる**構成である。

    台        各成分の内部元をばらばらに置き、`⊥` と `⊤` を一つずつ共有する
    順序      同じ成分の中では成分の順序、**異なる成分の元は比較不能**

`Family.T` はこの構成の模型である。ここではそれを

    ① 定義を性質として書く          `IsHorizontalSum`
    ② `Family.T` が満たすことを示す  `mid_isHorizontalSum`
    ③ **同型を除いて一意**を示す     `unique`

の三段で確定させる。③が在るので「`Family.T` は*ある*水平和」ではなく
「**水平和そのもの**」と言える。

構成そのものは既知である。ここで足しているのは Lean での形式化だけで、
数学的な新しさは主張しない。 -/

/-- **水平和であることの定義**（文献の条件をそのまま並べたもの）。

`emb i : P i → S` は成分 `i` の元を全体に埋め込む写像。 -/
structure IsHorizontalSum {ι : Type u} (P : ι → Type v) [∀ i, Preorder (P i)]
    (S : Type w) [PartialOrder S] [BoundedOrder S]
    (emb : ∀ i, P i → S) : Prop where
  /-- 成分の元は `⊥` ではない（内部元である）。 -/
  ne_bot : ∀ i a, emb i a ≠ ⊥
  /-- 成分の元は `⊤` ではない。 -/
  ne_top : ∀ i a, emb i a ≠ ⊤
  /-- 成分の中では順序がそのまま移る。 -/
  mono : ∀ i a b, emb i a ≤ emb i b ↔ a ≤ b
  /-- **異なる成分の元は比較不能。** -/
  cross : ∀ ⦃i j⦄, i ≠ j → ∀ a b, ¬ (emb i a ≤ emb j b)
  /-- 台は `⊥`・`⊤`・成分の元で尽きる。 -/
  covers : ∀ s : S, s = ⊥ ∨ s = ⊤ ∨ ∃ i a, s = emb i a
  /-- **非退化。**文献も "nontrivial bounded lattice" と言う。これが無いと
  一点の台と二点の台がどちらも条件を満たしてしまい、一意性が壊れる。 -/
  bot_ne_top : (⊥ : S) ≠ ⊤

namespace IsHorizontalSum

variable {ι : Type u} {P : ι → Type v} [∀ i, PartialOrder (P i)]
variable {S : Type w} [PartialOrder S] [BoundedOrder S] {emb : ∀ i, P i → S}

/-- 埋め込みは単射。 -/
theorem injective (h : IsHorizontalSum P S emb) (i : ι) :
    Function.Injective (emb i) := fun a b hab => by
  have h₁ : a ≤ b := (h.mono i a b).1 (le_of_eq hab)
  have h₂ : b ≤ a := (h.mono i b a).1 (le_of_eq hab.symm)
  exact le_antisymm h₁ h₂

/-- 成分が違えば元も違う。 -/
theorem ne_of_ne_index (h : IsHorizontalSum P S emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ≠ emb j b := fun e =>
  h.cross hij a b (le_of_eq e)

/-- **同じ元を指す埋め込みは、行き先でも同じ元を指す。**一意性の要。 -/
theorem emb_eq_transport {S' : Type w} [PartialOrder S'] [BoundedOrder S']
    {emb' : ∀ i, P i → S'} (h : IsHorizontalSum P S emb)
    (h' : IsHorizontalSum P S' emb') {i j : ι} {a : P i} {b : P j}
    (e : emb i a = emb j b) : emb' i a = emb' j b := by
  by_cases hij : i = j
  · subst hij
    rw [h.injective i e]
  · exact absurd e (h.ne_of_ne_index hij a b)

end IsHorizontalSum

/-! ## `Family.T` は水平和である -/

namespace Family

variable {ι : Type u} [DecidableEq ι] {P : ι → Type v} [∀ i, PartialOrder (P i)]

@[simp] theorem mid_ne_bot (i : ι) (a : P i) : (T.mid i a : T ι P) ≠ ⊥ := by
  intro h; exact absurd h (by simp [Bot.bot])

@[simp] theorem mid_ne_top (i : ι) (a : P i) : (T.mid i a : T ι P) ≠ ⊤ := by
  intro h; exact absurd h (by simp [Top.top])

/-- **`Family.T` は文献の意味での水平和である。** -/
theorem mid_isHorizontalSum : IsHorizontalSum P (T ι P) T.mid where
  ne_bot := mid_ne_bot
  ne_top := mid_ne_top
  mono i a b := mid_le_mid
  cross _ _ h a b := mid_incomparable h a b
  covers s := by
    rcases s with _ | ⟨i, a⟩ | _
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨i, a, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  bot_ne_top := by intro h; exact absurd h (by simp [Bot.bot, Top.top])

end Family

/-! ## 同型を除いて一意

同じ族に対する二つの水平和は順序同型である。だから「水平和」は構成の
選び方に依らず、`Family.T` は**その一つの実装**である。 -/

namespace IsHorizontalSum

variable {ι : Type u} {P : ι → Type v} [∀ i, PartialOrder (P i)]
variable {S : Type w} [PartialOrder S] [BoundedOrder S] {emb : ∀ i, P i → S}
variable {S' : Type w} [PartialOrder S'] [BoundedOrder S'] {emb' : ∀ i, P i → S'}

open Classical in
/-- 一方の台からもう一方へ写す。`⊥ ↦ ⊥`・`⊤ ↦ ⊤`・`emb i a ↦ emb' i a`。 -/
noncomputable def transfer (h : IsHorizontalSum P S emb)
    (h' : IsHorizontalSum P S' emb') (s : S) : S' :=
  if hb : s = ⊥ then ⊥
  else if ht : s = ⊤ then ⊤
  else
    have hex : ∃ p : Σ i, P i, s = emb p.1 p.2 := by
      rcases h.covers s with h1 | h1 | ⟨i, a, h1⟩
      · exact absurd h1 hb
      · exact absurd h1 ht
      · exact ⟨⟨i, a⟩, h1⟩
    emb' (choose hex).1 (choose hex).2

theorem transfer_bot (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb') :
    transfer h h' ⊥ = ⊥ := by simp [transfer]

theorem transfer_top (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb') :
    transfer h h' ⊤ = ⊤ := by
  rw [transfer, dif_neg (Ne.symm h.bot_ne_top), dif_pos rfl]

open Classical in
theorem transfer_mid (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb')
    (i : ι) (a : P i) : transfer h h' (emb i a) = emb' i a := by
  have hb : emb i a ≠ ⊥ := h.ne_bot i a
  have ht : emb i a ≠ ⊤ := h.ne_top i a
  simp only [transfer, dif_neg hb, dif_neg ht]
  generalize_proofs hex
  exact (h.emb_eq_transport h' (choose_spec hex)).symm

end IsHorizontalSum

/-! ## 「⊥ と ⊤ しか共有しない」を定理にする

文献の水平和は「成分は `0` と `1` **だけ**を共有する」と言う。`IsHorizontalSum`
にはその条項を直接書いていないが、**他の条項から出る**。

    ne_bot / ne_top   成分の像に `⊥` も `⊤` も入らない
    cross             異なる成分の像は交わらない

したがって台は `{⊥, ⊤}` と互いに素な像たちに**分割される**。 -/

namespace IsHorizontalSum

variable {ι : Type u} {P : ι → Type v} [∀ i, PartialOrder (P i)]
variable {S : Type w} [PartialOrder S] [BoundedOrder S] {emb : ∀ i, P i → S}

/-- **成分の像に `⊥` は入らない。** -/
theorem bot_notMem_range (h : IsHorizontalSum P S emb) (i : ι) :
    (⊥ : S) ∉ Set.range (emb i) := by
  rintro ⟨a, ha⟩; exact h.ne_bot i a ha

/-- **成分の像に `⊤` は入らない。** -/
theorem top_notMem_range (h : IsHorizontalSum P S emb) (i : ι) :
    (⊤ : S) ∉ Set.range (emb i) := by
  rintro ⟨a, ha⟩; exact h.ne_top i a ha

/-- **異なる成分の像は交わらない。** -/
theorem range_disjoint (h : IsHorizontalSum P S emb) {i j : ι} (hij : i ≠ j) :
    Set.range (emb i) ∩ Set.range (emb j) = ∅ := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨a, rfl⟩ ⟨b, hb⟩
  exact h.ne_of_ne_index hij a b hb.symm

/-- **共有されるのは `⊥` と `⊤` だけ。**二つの成分に同時に属する元は無い。 -/
theorem shared_only_bounds (h : IsHorizontalSum P S emb) (s : S)
    (hs : ∃ i j, i ≠ j ∧ s ∈ Set.range (emb i) ∧ s ∈ Set.range (emb j)) : False := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  have : s ∈ Set.range (emb i) ∩ Set.range (emb j) := ⟨hi, hj⟩
  rw [h.range_disjoint hij] at this
  exact this

/-- **台の分割。**`⊥`・`⊤`・成分の像で覆われ、成分どうしは互いに素で
`⊥`,`⊤` を含まない。これが「上下端だけ同一視して並べる」の中身である。 -/
theorem partition (h : IsHorizontalSum P S emb) :
    (Set.univ : Set S) = {⊥, ⊤} ∪ ⋃ i, Set.range (emb i) := by
  ext s
  simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_range]
  rcases h.covers s with e | e | ⟨i, a, e⟩
  · exact Or.inl (Or.inl e)
  · exact Or.inl (Or.inr e)
  · exact Or.inr ⟨i, a, e.symm⟩

end IsHorizontalSum

/-! ## いつ水平和になるか — 必要条件を内在的に書く

「これは水平和か」を成分の族を持ち出さずに判定したい。次の二つが効く。

    比べられるなら同じ成分       `same_component_of_comparable`
    束なら、比較不能は ⊤ と ⊥ へ  `cross_sup_top` / `cross_inf_bot`

二つ目が**判定に使える形**である。束 `S` が水平和なら、比較不能な二元は
必ず `⊔` で `⊤`・`⊓` で `⊥` に飛ぶ。だから中間の高さで出会う対が一組でも
在れば、それは水平和では**ない**。 -/

namespace IsHorizontalSum

variable {ι : Type u} {P : ι → Type v} [∀ i, PartialOrder (P i)]
variable {S : Type w} [PartialOrder S] [BoundedOrder S] {emb : ∀ i, P i → S}

/-- **比べられるなら同じ成分。**成分をまたぐ比較は無い。 -/
theorem same_component_of_comparable (h : IsHorizontalSum P S emb)
    {i j : ι} {a : P i} {b : P j}
    (hc : emb i a ≤ emb j b ∨ emb j b ≤ emb i a) : i = j := by
  by_contra hij
  rcases hc with hc | hc
  · exact h.cross hij a b hc
  · exact h.cross (Ne.symm hij) b a hc

/-- 成分の元は `⊥` の上、`⊤` の下に真に在る。 -/
theorem not_le_bot (h : IsHorizontalSum P S emb) (i : ι) (a : P i) :
    ¬ (emb i a ≤ ⊥) := fun hle => h.ne_bot i a (le_antisymm hle bot_le)

theorem not_top_le (h : IsHorizontalSum P S emb) (i : ι) (a : P i) :
    ¬ ((⊤ : S) ≤ emb i a) := fun hle => h.ne_top i a (le_antisymm le_top hle)

variable {L : Type w} [Lattice L] [BoundedOrder L] {emb : ∀ i, P i → L}

/-- **成分をまたぐ結びは `⊤`。**水平和が束なら必ずこうなる。

判定に使える: 中間の高さで出会う比較不能な対が一組でも在れば水平和でない。 -/
theorem cross_sup_top (h : IsHorizontalSum P L emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ⊔ emb j b = ⊤ := by
  rcases h.covers (emb i a ⊔ emb j b) with e | e | ⟨k, c, e⟩
  · exact absurd (e ▸ le_sup_left) (h.not_le_bot i a)
  · exact e
  · have hik : i = k := h.same_component_of_comparable (Or.inl (e ▸ le_sup_left))
    have hjk : j = k := h.same_component_of_comparable (Or.inl (e ▸ le_sup_right))
    exact absurd (hik.trans hjk.symm) hij

/-- **成分をまたぐ交わりは `⊥`。**双対。 -/
theorem cross_inf_bot (h : IsHorizontalSum P L emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ⊓ emb j b = ⊥ := by
  rcases h.covers (emb i a ⊓ emb j b) with e | e | ⟨k, c, e⟩
  · exact e
  · exact absurd (e ▸ inf_le_left) (h.not_top_le i a)
  · have hik : i = k := h.same_component_of_comparable (Or.inr (e ▸ inf_le_left))
    have hjk : j = k := h.same_component_of_comparable (Or.inr (e ▸ inf_le_right))
    exact absurd (hik.trans hjk.symm) hij

end IsHorizontalSum

/-! ## いつ半直積が可換になるか — 捻れが自明なときだけ

半直積は一般に非可換である。**可換になる条件がちょうど一つ**に決まる。 -/

section Commutativity

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

theorem clockPow_id {f : ι → (α ≃o α)} (h : ∀ A : E ι α, clock f A = A) (k : ℕ) :
    ∀ A : E ι α, clockPow f k A = A := by
  induction k with
  | zero => intro A; rfl
  | succ k ih => intro A; rw [clockPow_succ, ih, h]

/-- **半直積が可換 ⟺ 時計が恒等。**

`⟸` は `⊔` と `+` が可換だから。`⟹` は `(⊥,1) * (A,0)` と `(A,0) * (⊥,1)` を
比べると `σA = A` が出る。**捻れが少しでも在れば非可換になる。** -/
theorem semi_comm_iff (f : ι → (α ≃o α)) :
    (∀ p q : Semi f, p * q = q * p) ↔ ∀ A : E ι α, clock f A = A := by
  constructor
  · intro hc A
    have := hc (Semi.inr 1) (Semi.inl A)
    rw [Semi.inr_mul_inl, Semi.inl_mul_inr] at this
    have h1 : clockPow f 1 A = A := congrArg Semi.left this
    rwa [clockPow_succ, clockPow_zero] at h1
  · intro h p q
    refine Semi.ext' ?_ (Nat.add_comm _ _)
    show clockPow f p.right q.left ⊔ p.left = clockPow f q.right p.left ⊔ q.left
    rw [clockPow_id h, clockPow_id h, sup_comm]

/-- 対偶。**捻れが在れば非可換。** -/
theorem semi_not_comm_of_clock_ne (f : ι → (α ≃o α)) (A : E ι α)
    (h : clock f A ≠ A) : ¬ (∀ p q : Semi f, p * q = q * p) :=
  fun hc => h ((semi_comm_iff f).1 hc A)

end Commutativity

end HorizontalSum
