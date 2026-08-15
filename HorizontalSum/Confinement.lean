import HorizontalSum.Action

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! # この束でしか言えないこと — 閉じ込め・二種類・履歴・始まり -/

/-! ## 閉じ込めと直既約性

この束は**直積に分解できない**（`bot_isCompl_unique`・`complement_not_unique`）。
だから作用の第二引数は「一部分」を指すことができず、束の元そのものである。

そのうえで、`⊥` でない元は**その軸から出られない**（`confinement`）。
軸を出た先は 𝓦 ただ一つで、そこでは区別が全部消える。
`⊥` だけが自由で、理由は **`⊥` がすべての軸の下に在る**こと。 -/

/-- **閉じ込め。**`A = ⟨i,a⟩` の作用の値は、軸 `i` の上か 𝓦 だけ。 -/
theorem confinement (f : ι → (α ≃o α)) (i : ι) (a : α) (b : E ι α) :
    act (clock f) (E.axis i a) b = ⊤ ∨
      ∃ x, act (clock f) (E.axis i a) b = E.axis i x := by
  rcases b with _ | ⟨j, c⟩ | _
  · exact Or.inr ⟨a, by simp [act]⟩
  · by_cases h : i = j
    · subst h
      exact Or.inr ⟨(f i) c ⊔ a, by simp [act]⟩
    · exact Or.inl (by simp [act, Ne.symm h])
  · exact Or.inl (by simp [act])

/-- **軸の元の像はちょうどこれだけ。**
`im λ_A = { ⟨i,x⟩ : a ⪯ x } ∪ { 𝓦 }`。 -/
theorem image_of_act (f : ι → (α ≃o α)) (i : ι) (a : α) :
    Set.range (act (clock f) (E.axis i a)) =
      (fun x => (E.axis i x : E ι α)) '' {x | a ≤ x} ∪ {⊤} := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl⟩
    rcases b with _ | ⟨j, c⟩ | _
    · exact Or.inl ⟨a, le_rfl, by simp [act]⟩
    · by_cases h : i = j
      · subst h
        exact Or.inl ⟨(f i) c ⊔ a, le_sup_right, by simp [act]⟩
      · exact Or.inr (by simp [act, Ne.symm h])
    · exact Or.inr (by simp [act])
  · rintro (⟨x, hx, rfl⟩ | rfl)
    · exact ⟨E.axis i ((f i).symm x), by simp [act, sup_eq_left.mpr hx]⟩
    · exact ⟨⊤, by simp [act]⟩

/-- 対して**`⊥` の像は全体**。`λ_𝓛 = σ_f` は全射（`sigma_surjective`）。 -/
theorem lmonad_reaches_everything (f : ι → (α ≃o α)) :
    Set.range (act (clock f) (⊥ : E ι α)) = Set.univ :=
  Set.range_eq_univ.mpr (sigma_surjective f)

/-! ### 直既約 — 座標が無い

束が直積に分解できるには、補元が一意な元（中心元）が要る。
この束にはそれが 𝓛 と 𝓦 しか無い。 -/

/-- 𝓛 の補元は 𝓦 ただ一つ。 -/
theorem bot_isCompl_unique {y : E ι α} (h : IsCompl (⊥ : E ι α) y) : y = ⊤ :=
  top_le_iff.mp (h.codisjoint bot_le le_rfl)

/-- 𝓦 の補元は 𝓛 ただ一つ。 -/
theorem top_isCompl_unique {y : E ι α} (h : IsCompl (⊤ : E ι α) y) : y = ⊥ :=
  le_bot_iff.mp (h.disjoint le_top le_rfl)

/-- **軸の元は補元をもつが一意でない。**だから座標にならず、
束は直積に分解できない（直既約）。 -/
theorem complement_not_unique {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : α) :
    IsCompl (E.axis i a : E ι α) (E.axis j b) ∧
      IsCompl (E.axis i a : E ι α) (E.axis k c) ∧
      (E.axis j b : E ι α) ≠ E.axis k c := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact disjoint_iff.mpr (axes_meet_at_lmonad hij a b)
  · exact codisjoint_iff.mpr (axes_join_to_world hij a b)
  · exact disjoint_iff.mpr (axes_meet_at_lmonad hik a c)
  · exact codisjoint_iff.mpr (axes_join_to_world hik a c)
  · intro h
    rw [E.axis.injEq] at h
    exact hjk h.1


/-- **軸の元が届く軸はちょうど 1 本。**
像に現れる名札の集合は `{i}` である。 -/
theorem reaches_exactly_one_axis (f : ι → (α ≃o α)) (i : ι) (a : α) :
    {j : ι | ∃ x, ∃ b, act (clock f) (E.axis i a) b = E.axis j x} = {i} := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, b, hb⟩
    rcases confinement f i a b with h | ⟨y, hy⟩
    · rw [h] at hb; simp at hb
    · rw [hy, E.axis.injEq] at hb
      exact hb.1.symm
  · rintro rfl
    exact ⟨a, ⊥, by simp [act]⟩


/-- **像はちょうど二つの部分に割れる。**
`A = ⟨i,a⟩` の届く先は「軸 `i` の `a` 以上」か「𝓦」のどちらかで、
この二つは**交わらず**、どちらも**空でない**。

    im λ_A = ( ↑A ∩ 軸 i )  ∪  { 𝓦 } -/
theorem two_kinds_of_non_lmonad (f : ι → (α ≃o α)) (i : ι) (a : α) :
    Set.range (act (clock f) (E.axis i a)) =
        (fun x => (E.axis i x : E ι α)) '' {x | a ≤ x} ∪ {⊤} ∧
      Disjoint ((fun x => (E.axis i x : E ι α)) '' {x | a ≤ x})
        ({⊤} : Set (E ι α)) ∧
      ((fun x => (E.axis i x : E ι α)) '' {x | a ≤ x}).Nonempty := by
  refine ⟨image_of_act f i a, ?_, ⟨E.axis i a, a, le_rfl, rfl⟩⟩
  rw [Set.disjoint_singleton_right]
  rintro ⟨x, _, hx⟩
  simp at hx

/-- 第二引数ごとに見ても二択になる。**軸の中を進むか、𝓦 に行くか。**
前者は軸の中で少しずつ進み、後者は一度で 𝓦 に着く。 -/
theorem harm_self_or_other (f : ι → (α ≃o α)) (i : ι) (a : α) (b : E ι α) :
    (∃ x, a ≤ x ∧ act (clock f) (E.axis i a) b = E.axis i x) ∨
      act (clock f) (E.axis i a) b = ⊤ := by
  rcases confinement f i a b with h | ⟨y, hy⟩
  · exact Or.inr h
  · refine Or.inl ⟨y, ?_, hy⟩
    have h6 := six f (E.axis i a) b
    rw [hy] at h6
    simpa using h6

/-- 第二引数が `⊥` なら値は動かない——`⑦` そのもの。三つ目の場合は無い。 -/
theorem harm_nothing (f : ι → (α ≃o α)) (a : E ι α) :
    act (clock f) a ⊥ = a := seven f a

end HorizontalSum
