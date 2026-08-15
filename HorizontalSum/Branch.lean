import HorizontalSum.Confinement

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ## 多価の時計 — 錐を埋める

軸ごとに一つの速さでは、錐は線の束にしかならなかった。時計そのものを
**多価**にする——一歩ごとに速さが枝分かれする——と、公理を一つも壊さずに
錐が埋まる。

要点は `clock f ⊥ = ⊥` が速さに依らないこと。だから枝が何本あっても
`A • 𝓛 = {A}` が成り立つ。**枝分かれを「働く者」ではなく「時計」に置く**
のが効いている（働く者に置くと ⑤ と ⑧ が壊れる）。 -/

/-- 速さの族 `F` を持つ多価の作用。 -/
def bact (F : Set (ι → (α ≃o α))) (a b : E ι α) : Set (E ι α) :=
  (fun f => act (clock f) a b) '' F

/-- ⑦ **枝が何本あっても `A • ⊥ = {A}`。**
`clock f ⊥ = ⊥` が速さに依らないから。 -/
theorem branch_seven (F : Set (ι → (α ≃o α))) (hF : F.Nonempty) (a : E ι α) :
    bact F a ⊥ = {a} := by
  ext x
  simp only [bact, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, _, rfl⟩; exact seven g a
  · intro hx
    obtain ⟨g, hg⟩ := hF
    exact ⟨g, hg, (seven g a).trans hx.symm⟩

/-- ⑥ どの枝でも積み上げは起きる。時間の矢印は枝分かれで壊れない。 -/
theorem branch_six (F : Set (ι → (α ≃o α))) (a b : E ι α) :
    ∀ c ∈ bact F a b, a ≤ c := by
  rintro c ⟨g, _, rfl⟩
  exact six g a b

/-- ⑧ 分解則も枝ごとに成り立つ。 -/
theorem branch_eight (F : Set (ι → (α ≃o α))) (a b : E ι α) :
    bact F a b = (fun c => c ⊔ a) '' bact F ⊥ b := by
  ext x
  simp only [bact, Set.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨act (clock g) ⊥ b, ⟨g, hg, rfl⟩, (form g a b).symm⟩
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, form g a b⟩

/-- ④ どの枝も対象について単調。 -/
theorem branch_four (F : Set (ι → (α ≃o α))) (a : E ι α) {b c : E ι α}
    (h : b ≤ c) : ∀ x ∈ bact F a b, ∃ y ∈ bact F a c, x ≤ y := by
  rintro x ⟨g, hg, rfl⟩
  exact ⟨act (clock g) a c, ⟨g, hg, rfl⟩, four g a h⟩

/-- ⑤ どの枝も働く者について単調。 -/
theorem branch_five (F : Set (ι → (α ≃o α))) {a a' : E ι α} (h : a ≤ a')
    (b : E ι α) : ∀ x ∈ bact F a b, ∃ y ∈ bact F a' b, x ≤ y := by
  rintro x ⟨g, hg, rfl⟩
  exact ⟨act (clock g) a' b, ⟨g, hg, rfl⟩, five g a a' b h⟩

/-- 第一引数は、枝が何本あっても一意に読める。 -/
theorem branch_actor (F : Set (ι → (α ≃o α))) (hF : F.Nonempty) {a a' : E ι α}
    (h : bact F a ⊥ = bact F a' ⊥) : a = a' := by
  rw [branch_seven F hF a, branch_seven F hF a'] at h
  exact Set.singleton_eq_singleton_iff.mp h

/-! ### 錐が埋まる

速さの集合を `{1, 2}` に取り、`T` 歩ぶん選ぶ。到達する高さの集合が
`T` から `2T` までの**すべて**の整数になる——隙間が無い。 -/

/-- **錐は隙間なく埋まる。** 速さ `{1,2}` を `T` 歩選んだときに届く高さの
集合は、区間 `[T, 2T]` にちょうど一致する。 -/
theorem cone_filled (T : ℕ) :
    {s | ∃ k ≤ T, s = 2 * k + (T - k)} = Set.Icc T (2 * T) := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨s - T, by omega, by omega⟩

/-- 対照。速さが一つだと届く先は一点だけで、錐は開かない。 -/
theorem cone_single (r T : ℕ) {s : ℕ} (h : ∃ k ≤ T, s = r * k + r * (T - k)) :
    s = r * T := by
  obtain ⟨k, hk, rfl⟩ := h
  rw [← Nat.mul_add, Nat.add_sub_cancel' hk]

end HorizontalSum
