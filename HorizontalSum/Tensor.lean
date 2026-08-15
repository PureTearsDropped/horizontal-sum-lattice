import HorizontalSum.Coordinates

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ## 座標は無限次元か — 「𝓛 と 𝓦 は ∞ 次元テンソル」を三つに割る

主張を三つに割ると、**二つは定理になり、一つは反証される**。

  (a) 次元が無限であること              ⟹ 定理（下の `axis_infinite_of_nontrivial_clock`）
  (b) 成分が全 1 / one-hot であること    ⟹ 定理（`lmonad_world_mirror`）
  (c) 「テンソル」＝多重添字であること    ⟹ **不可能**（`no_product_decomposition`） -/

/-- **整礎な線形順序の順序同型は恒等しかない。**
`StrictMono.le_apply` を `e` と `e.symm` の両側に当てる。 -/
theorem orderIso_eq_refl_of_wellFounded {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (e : β ≃o β) (x : β) : e x = x := by
  have h₁ : x ≤ e x := e.strictMono.le_apply
  have h₂ : x ≤ e.symm x := e.symm.strictMono.le_apply
  have h₃ : e x ≤ x := by simpa using e.monotone h₂
  exact le_antisymm h₃ h₁

/-- **時計が恒等でなければ、軸は整礎でありえない。**
これが「軸の長さは無限」の中身である（有限鎖も ℕ も整礎だから落ちる）。 -/
theorem not_wellFounded_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) : ¬ WellFoundedLT β := fun _ =>
  h (orderIso_eq_refl_of_wellFounded e x)

/-- **時計が恒等でなければ、軸は無限。**有限な線形順序は整礎だから。 -/
theorem axis_infinite_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) : Infinite β := by
  rw [← not_finite_iff_infinite]
  intro _
  exact not_wellFounded_of_nontrivial_clock e x h Finite.to_wellFoundedLT

/-- **そして束そのものが無限。**⟸ 上二つ + `infinite_of_infinite`。
だから `Φ` の行き先 `Set (E ι β)` は無限個の成分をもつ。 -/
theorem infinite_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) (i : ι) : Infinite (E ι β) :=
  letI := axis_infinite_of_nontrivial_clock e x h
  infinite_of_infinite i

/-- **直積の側には必ず「中間の中心元」が在る。**
`(⊥, ⊤)` の補元は `(⊤, ⊥)` ただ一つに決まる。 -/
theorem prod_mid_isCompl_unique {A B : Type*} [Lattice A] [Lattice B]
    [BoundedOrder A] [BoundedOrder B] {p : A × B}
    (h : IsCompl ((⊥, ⊤) : A × B) p) : p = (⊤, ⊥) := by
  have hs : ((⊥, ⊤) : A × B) ⊔ p = ⊤ := codisjoint_iff.mp h.codisjoint
  have hi : ((⊥, ⊤) : A × B) ⊓ p = ⊥ := disjoint_iff.mp h.disjoint
  have e1 : p.1 = ⊤ := by simpa using congrArg Prod.fst hs
  have e2 : p.2 = ⊥ := by simpa using congrArg Prod.snd hi
  obtain ⟨p1, p2⟩ := p
  simp_all

/-- **この束は直積に分解できない。**⟸ `complement_not_unique`（軸が 3 本以上）。
直積側の `(⊥,⊤)` は補元が一意だが、この束で 𝓛 でも 𝓦 でもない元は
補元が一意でない。**だから座標を多重添字に割ることができない——
「テンソル」にはならず、階数 1 のベクトルが上限である。** -/
theorem no_product_decomposition
    (h3 : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k)
    {A B : Type*} [Lattice A] [Lattice B] [BoundedOrder A] [BoundedOrder B]
    (e : E ι α ≃o A × B) (hA : (⊥ : A) ≠ ⊤) (hB : (⊥ : B) ≠ ⊤) : False := by
  set x : E ι α := e.symm (⊥, ⊤) with hx
  have hxb : x ≠ ⊥ := by
    intro hb
    have h0 : ((⊥ : A), (⊤ : B)) = (⊥ : A × B) := by
      rw [← e.map_bot, ← hb, hx, e.apply_symm_apply]
    exact hB (by simpa using (congrArg Prod.snd h0).symm)
  have hxt : x ≠ ⊤ := by
    intro ht
    have h0 : ((⊥ : A), (⊤ : B)) = (⊤ : A × B) := by
      rw [← e.map_top, ← ht, hx, e.apply_symm_apply]
    exact hA (by simpa using congrArg Prod.fst h0)
  -- 𝓛 でも 𝓦 でもないなら軸の元
  obtain ⟨i, a, hia⟩ : ∃ i a, x = E.axis i a := by
    rcases hxc : x with _ | ⟨i, a⟩ | _
    · exact absurd hxc hxb
    · exact ⟨i, a, rfl⟩
    · exact absurd hxc hxt
  obtain ⟨j, k, hij, hik, hjk⟩ := h3 i
  obtain ⟨hc1, hc2, hne⟩ := complement_not_unique (α := α) hij hik hjk a a a
  rw [← hia] at hc1 hc2
  have t1 : IsCompl ((⊥, ⊤) : A × B) (e (E.axis j a)) := by
    have := e.isCompl hc1
    rwa [hx, e.apply_symm_apply] at this
  have t2 : IsCompl ((⊥, ⊤) : A × B) (e (E.axis k a)) := by
    have := e.isCompl hc2
    rwa [hx, e.apply_symm_apply] at this
  exact hne (e.injective ((prod_mid_isCompl_unique t1).trans
    (prod_mid_isCompl_unique t2).symm))

/-! ### 𝓦 = ∞ 次元の one-hot、𝓛 = ∞ 次元の全 1

座標を指示関数として literal に書き下す。`1 = まだ可能`、`0 = もう不可能`。
添字集合は `E` 自身で、時計が動くならこれは無限（`infinite_of_nontrivial_clock`）。 -/

section Chi

attribute [local instance] Classical.propDecidable

/-- 座標の指示関数。`χ_x(y) = 1` ⟺ `x` から `y` がまだ可能。 -/
noncomputable def chi (x y : E ι α) : ℕ := if x ≤ y then 1 else 0

/-- **𝓛 の座標は全 1。**成分がひとつも 0 にならない。 -/
theorem chi_lmonad (y : E ι α) : chi (⊥ : E ι α) y = 1 := if_pos bot_le

/-- **𝓦 の座標は one-hot。**立っている成分は `𝓦` ただ一つ。 -/
theorem chi_world (y : E ι α) : chi (⊤ : E ι α) y = if y = ⊤ then 1 else 0 := by
  by_cases h : y = ⊤
  · rw [if_pos h, chi, if_pos (h ▸ le_rfl)]
  · rw [if_neg h, chi, if_neg (fun hle => h (top_le_iff.mp hle))]

/-- 台は `Φ` そのもの。指示関数と集合の言い換えが一致する。 -/
theorem chi_support (x : E ι α) : {y | chi x y = 1} = Phi x := by
  ext y
  simp only [Set.mem_setOf_eq, Phi]
  constructor
  · intro h
    by_contra hle
    rw [chi, if_neg hle] at h
    exact absurd h (by decide)
  · intro h
    rw [chi, if_pos h]

/-- 台で書くと: 𝓛 は全体。 -/
theorem chi_lmonad_support : {y : E ι α | chi (⊥ : E ι α) y = 1} = Set.univ := by
  rw [chi_support]; exact Phi_bot

/-- 台で書くと: **𝓦 は一点。**これが「one-hot」の literal な意味。 -/
theorem chi_world_support : {y : E ι α | chi (⊤ : E ι α) y = 1} = {(⊤ : E ι α)} := by
  rw [chi_support]; exact Phi_eq_singleton_iff.mpr rfl

/-- **one-hot になるのは 𝓦 だけ。**⟸ `Phi_eq_singleton_iff`。
「𝓦 = one-hot」は定義ではなく、**one-hot な元が 𝓦 しか無いという定理**である。 -/
theorem chi_onehot_iff {x : E ι α} : {y | chi x y = 1} = {x} ↔ x = ⊤ := by
  rw [chi_support]; exact Phi_eq_singleton_iff

/-- **全 1 になるのは 𝓛 だけ。** -/
theorem chi_allones_iff {x : E ι α} : {y | chi x y = 1} = Set.univ ↔ x = ⊥ := by
  rw [chi_support]; exact Phi_eq_univ_iff

/-- **上に進むと 1 が 0 に変わっていく。**戻ることはない。 -/
theorem chi_antitone {x y : E ι α} (h : x ≤ y) (z : E ι α) : chi y z ≤ chi x z := by
  rw [chi, chi]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h.trans h1) h2
  · exact Nat.zero_le _
  · exact le_rfl

/-- **順序は座標で完全に読める**（反順序埋め込み）。 -/
theorem chi_le_iff {x y : E ι α} : (∀ z, chi y z ≤ chi x z) ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h z => chi_antitone h z⟩
  have hy := h y
  rw [chi, if_pos (le_refl y)] at hy
  by_contra hxy
  rw [chi, if_neg hxy] at hy
  exact absurd hy (by decide)

/-- **𝓦 の one-hot は無限次元。**⟸ `infinite_of_nontrivial_clock`。
時計が動くなら添字集合 `E` が無限なので、これは有限ベクトルではない。 -/
theorem chi_world_infinite_support {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) (i : ι) :
    Infinite (E ι β) ∧ {y : E ι β | chi (⊤ : E ι β) y = 1} = {(⊤ : E ι β)} :=
  ⟨infinite_of_nontrivial_clock e x h i, chi_world_support⟩

end Chi

/-! ### 「∞ ならテンソルが書ける」— 添字の読み替え

無限集合は自分自身との直積と同型になる。だから `E` 上の 0/1 ベクトルは
**そのまま任意の階数のテンソルとして読める**。有限ではこれが起きない。 -/

/-- **無限なら 2 階に読み替えられる。**⟸ `Cardinal.mul_eq_self`。 -/
theorem reshape_two (β : Type*) [Infinite β] : Nonempty (β ≃ β × β) := by
  rw [← Cardinal.eq]
  simp [Cardinal.mk_prod,
    Cardinal.mul_eq_self (Cardinal.aleph0_le_mk β)]

/-- **無限なら任意の階数に読み替えられる。**⟸ `Cardinal.power_nat_eq`。
`𝓛` の座標は「∞ 次元の全 1 ベクトル」であり、同時に
**任意の階数 `n` の ∞ 次元全 1 テンソル**でもある。 -/
theorem reshape_rank (β : Type*) [Infinite β] {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (β ≃ (Fin n → β)) := by
  rw [← Cardinal.eq]
  have h1 : Cardinal.aleph0 ≤ Cardinal.mk β := Cardinal.aleph0_le_mk β
  simp [Cardinal.mk_arrow, Cardinal.power_nat_eq h1 hn]

/-- **有限ではこの読み替えが不可能。**`n = n²` は `n = 0, 1` でしか成り立たない。
だから**「テンソルであること」を買っているのは無限次元そのもの**である。 -/
theorem no_reshape_of_finite (β : Type*) [Finite β] (e : β ≃ β × β) :
    Subsingleton β := by
  have h : Nat.card β = Nat.card β * Nat.card β := by
    rw [← Nat.card_prod]; exact Nat.card_congr e
  rcases Nat.eq_zero_or_pos (Nat.card β) with h0 | hpos
  · have : IsEmpty β := by
      rcases Nat.card_eq_zero.mp h0 with h' | h'
      · exact h'
      · exact absurd h' (not_infinite_iff_finite.mpr inferInstance)
    infer_instance
  · have h1 : Nat.card β * 1 = Nat.card β * Nat.card β := by simpa using h
    have := Nat.eq_of_mul_eq_mul_left hpos h1
    exact (Nat.card_eq_one_iff_unique.mp this.symm).1

/-! ### 「読み替えても積のまま」で 𝓛 と 𝓦 を特徴づける

添字を `A × B` に読み替えたとき、部分集合が**長方形**（= 階数 1 のテンソル）
であるとは、二点の座標を混ぜても中に留まること。 -/

/-- 長方形＝階数 1。二点の第 1 成分と第 2 成分を混ぜても集合に留まる。 -/
def IsRect {A B : Type*} (S : Set (A × B)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S

/-- **全 1 はどんな読み替えでも積に割れる。** -/
theorem univ_isRect {A B : Type*} : IsRect (Set.univ : Set (A × B)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- **one-hot もどんな読み替えでも積に割れる。** -/
theorem singleton_isRect {A B : Type*} (p : A × B) : IsRect ({p} : Set (A × B)) := by
  rintro q hq r hr
  rw [Set.mem_singleton_iff] at hq hr ⊢
  subst hq; subst hr
  rfl

/-- **𝓛 の座標は、どんな読み替えでも階数 1。**⟸ `Phi_bot` + `univ_isRect`。 -/
theorem Phi_bot_isRect {A B : Type*} (e : E ι α ≃ A × B) :
    IsRect (e '' Phi (⊥ : E ι α)) := by
  rw [Phi_bot]
  rw [Set.image_univ_of_surjective e.surjective]
  exact univ_isRect

/-- **𝓦 の座標も、どんな読み替えでも階数 1。**⟸ `Phi_top` は one-hot。 -/
theorem Phi_top_isRect {A B : Type*} (e : E ι α ≃ A × B) :
    IsRect (e '' Phi (⊤ : E ι α)) := by
  have h : Phi (⊤ : E ι α) = {⊤} := Phi_eq_singleton_iff.mpr rfl
  rw [h, Set.image_singleton]
  exact singleton_isRect _

/-- **そして中間の元は割れない読み替えが在る。**
`Bool × Bool` に読み替えた具体例。対角 `{(f,f), (t,t)}` は長方形でない
——`(f,t)` が抜けるから。**大きさが 2 以上かつ全体でない座標は、
必ずこの形に潰せる**（有限模型の数え上げでも ∅・一点・全体だけが残った）。 -/
theorem diagonal_not_isRect :
    ¬ IsRect ({(false, false), (true, true)} : Set (Bool × Bool)) := by
  intro h
  have := h (false, false) (by simp) (true, true) (by simp)
  simp at this

/-! ### 有限テンソルによる近似 — 軸 ℤ を高さ N で切る

「𝓛 と 𝓦 は ∞ 次元テンソル」は書けるが、**有限テンソルでどこまで代用できるか**。
答え: **有限時間ぶんは厳密に代用できる。ただし時計は外から与えるしかない。**

    E(m, N) = {𝓛, 𝓦} ∪ { ⟨i, a⟩ : i < m, |a| ≤ N }        m(2N+1) + 2 成分 -/

/-- 軸を `ℤ`、本数を `m` に取り、高さ `N` で切った有限部分。 -/
def trunc (m N : ℕ) : Set (E (Fin m) ℤ) :=
  {⊥, ⊤} ∪ {x | ∃ i a, x = E.axis i a ∧ |a| ≤ (N : ℤ)}

theorem bot_mem_trunc (m N : ℕ) : (⊥ : E (Fin m) ℤ) ∈ trunc m N := Or.inl (by simp)

theorem top_mem_trunc (m N : ℕ) : (⊤ : E (Fin m) ℤ) ∈ trunc m N := Or.inl (by simp)

/-- **切っても有限。**成分数は `m(2N+1) + 2`。 -/
theorem trunc_finite (m N : ℕ) : (trunc m N).Finite := by
  refine Set.Finite.union (Set.toFinite _) (Set.Finite.subset
    (Set.Finite.image (fun p : Fin m × ℤ => E.axis p.1 p.2)
      (Set.Finite.prod Set.finite_univ (Set.finite_Icc (-(N : ℤ)) (N : ℤ)))) ?_)
  rintro x ⟨i, a, rfl, ha⟩
  exact ⟨(i, a), ⟨trivial, abs_le.mp ha⟩, rfl⟩

/-- 軸の元が切り口に入る条件は、高さの絶対値だけ。 -/
theorem mem_trunc_axis {m N : ℕ} {i : Fin m} {a : ℤ} :
    (E.axis i a : E (Fin m) ℤ) ∈ trunc m N ↔ |a| ≤ (N : ℤ) := by
  constructor
  · rintro (h | ⟨j, b, hEq, hb⟩)
    · rcases h with h | h <;> exact absurd h (by simp)
    · rw [E.axis.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      exact hb
  · intro h
    exact Or.inr ⟨i, a, rfl, h⟩

/-- **切っても束のまま。**`⊔` で外に出ない。 -/
theorem trunc_sup_mem {m N : ℕ} {x y : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) (hy : y ∈ trunc m N) : x ⊔ y ∈ trunc m N := by
  rcases x with _ | ⟨i, a⟩ | _
  · simpa using hy
  · rcases y with _ | ⟨j, b⟩ | _
    · simpa using hx
    · by_cases hij : i = j
      · subst hij
        rw [mem_trunc_axis] at hx hy
        rw [same_axis_sup, mem_trunc_axis]
        rcases le_total a b with h | h
        · rwa [sup_eq_right.mpr h]
        · rwa [sup_eq_left.mpr h]
      · rw [axes_join_to_world hij]
        exact top_mem_trunc m N
    · exact top_mem_trunc m N
  · exact top_mem_trunc m N

/-- **`⊓` でも外に出ない。** -/
theorem trunc_inf_mem {m N : ℕ} {x y : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) (hy : y ∈ trunc m N) : x ⊓ y ∈ trunc m N := by
  rcases x with _ | ⟨i, a⟩ | _
  · exact bot_mem_trunc m N
  · rcases y with _ | ⟨j, b⟩ | _
    · exact bot_mem_trunc m N
    · by_cases hij : i = j
      · subst hij
        rw [mem_trunc_axis] at hx hy
        rw [same_axis_inf, mem_trunc_axis]
        rcases le_total a b with h | h
        · rwa [inf_eq_left.mpr h]
        · rwa [inf_eq_right.mpr h]
      · rw [axes_meet_at_lmonad hij]
        exact bot_mem_trunc m N
    · simpa using hx
  · simpa using hy

/-- 速さ 1 の時計（軸 `ℤ` の平行移動）。 -/
def shift1 : ℤ ≃o ℤ := OrderIso.addRight 1

/-- **切った先には時計が住めない。**⟸ `orderIso_eq_refl_of_wellFounded`。
有限な線形順序の順序同型は恒等しかないので、**有限テンソルの中では時間が止まる**。 -/
theorem no_clock_inside_trunc (N : ℕ)
    (e : Set.Icc (-(N : ℤ)) (N : ℤ) ≃o Set.Icc (-(N : ℤ)) (N : ℤ)) (x) : e x = x :=
  letI : Finite (Set.Icc (-(N : ℤ)) (N : ℤ)) := Set.finite_Icc _ _
  letI := Finite.to_wellFoundedLT (α := Set.Icc (-(N : ℤ)) (N : ℤ))
  orderIso_eq_refl_of_wellFounded e x

/-- **一歩進むと切り口が一つ伸びる。** -/
theorem trunc_clock_step {m N : ℕ} {x : E (Fin m) ℤ} (hx : x ∈ trunc m N) :
    clock (fun _ : Fin m => shift1) x ∈ trunc m (N + 1) := by
  rcases x with _ | ⟨i, a⟩ | _
  · exact bot_mem_trunc m (N + 1)
  · rw [mem_trunc_axis] at hx
    show clock (fun _ : Fin m => shift1) (E.axis i a) ∈ trunc m (N + 1)
    have hc : clock (fun _ : Fin m => shift1) (E.axis i a) = E.axis i (a + 1) := by
      simp [clock, shift1]
    rw [hc, mem_trunc_axis]
    rw [abs_le] at hx ⊢
    push_cast
    omega
  · exact top_mem_trunc m (N + 1)

/-- **有限時間ぶんは有限テンソルで厳密。**
`T` 歩なら `N + T` まで取れば足りる——**これが近似である**。
`N` を固定したままにはできないが（上の `no_clock_inside_trunc`）、
**どんな有限の `T` にも、それを丸ごと収める有限テンソルが在る**。 -/
theorem trunc_approximates (m N : ℕ) : ∀ (T : ℕ) {x : E (Fin m) ℤ},
    x ∈ trunc m N → (clock (fun _ : Fin m => shift1))^[T] x ∈ trunc m (N + T) := by
  intro T
  induction T with
  | zero => intro x hx; simpa using hx
  | succ T ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      have h1 := trunc_clock_step (ih hx)
      have hN : N + T + 1 = N + (T + 1) := by omega
      rwa [hN] at h1

/-- **そして有限テンソルを重ねると元に戻る。**⟸ 上。
無限次元は「有限次元の極限」であって、別のものではない。 -/
theorem trunc_union (m : ℕ) : ⋃ N, trunc m N = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases x with _ | ⟨i, a⟩ | _
  · exact ⟨0, bot_mem_trunc m 0⟩
  · exact ⟨a.natAbs, Or.inr ⟨i, a, rfl, by rw [abs_le]; omega⟩⟩
  · exact ⟨0, top_mem_trunc m 0⟩

end HorizontalSum
