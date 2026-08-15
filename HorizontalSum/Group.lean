import HorizontalSum.Rotation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 名札を群に取る — 非可換なら作用が二種類になる

名札の型 `ι` は任意なので、**群 `G` を名札にできる**。すると左移動と右移動の
二つが順序同型になる。左と右はいつでも互いに可換だが（結合律）、
`G` が非可換なら**左移動どうしが可換でなくなる**——順序が結果に残る。

`G = ℤ/4` は可換で、これまで扱ってきた四方向。
`G = Q8 = {±1, ±i, ±j, ±k}` は非可換で、**八方向**になる。 -/

section GroupLabels

variable {G : Type*} [Group G] [DecidableEq G]

/-- 名札を左から掛ける。 -/
def lrot (g : G) : E G α ≃o E G α := ofAxisEquiv (Equiv.mulLeft g)

/-- 名札を右から掛ける。 -/
def rrot (g : G) : E G α ≃o E G α := ofAxisEquiv (Equiv.mulRight g)

@[simp] theorem lrot_lmonad (g : G) : lrot g (E.lmonad : E G α) = E.lmonad := rfl
@[simp] theorem lrot_world (g : G) : lrot g (E.world : E G α) = E.world := rfl
@[simp] theorem lrot_axis (g k : G) (a : α) :
    lrot g (E.axis k a : E G α) = E.axis (g * k) a := rfl
@[simp] theorem rrot_lmonad (g : G) : rrot g (E.lmonad : E G α) = E.lmonad := rfl
@[simp] theorem rrot_world (g : G) : rrot g (E.world : E G α) = E.world := rfl
@[simp] theorem rrot_axis (g k : G) (a : α) :
    rrot g (E.axis k a : E G α) = E.axis (k * g) a := rfl

/-- **左と右はいつでも可換。**結合律そのもの。 -/
theorem lrot_rrot_comm (g h : G) (x : E G α) :
    lrot g (rrot h x) = rrot h (lrot g x) := by
  rcases x with _ | ⟨k, a⟩ | _ <;> simp [mul_assoc]


/-! ### 相対位相だけが不変量 — 軸の名札は捩れ子（torsor）

`W^θ = W^φ` なので頂は一つ。では `{W^{θ_n}}` は何かというと、
**同じ 𝓦 に至る相異なる「向き」の集まり**である。名札に原点は無い。 -/

/-- **どの軸もどの軸に移せる。**左移動が軸の上で推移的に働く。
`h * g⁻¹` を選べば `θ_g` の軸が `θ_h` の軸に重なる。 -/
theorem axes_homogeneous (g h : G) (a : α) :
    lrot (h * g⁻¹) (E.axis g a : E G α) = E.axis h a := by
  simp [inv_mul_cancel_right]

/-- **だから絶対的な名札は不変量になれない。**
名札が二つ以上あれば、原点を動かす順序同型が必ず在る。 -/
theorem no_distinguished_axis {g h : G} (hgh : g ≠ h) (a : α) :
    ∃ e : E G α ≃o E G α, e (E.axis g a) ≠ E.axis g a :=
  ⟨lrot (h * g⁻¹), by simp [inv_mul_cancel_right]; exact fun hc => hgh hc.symm⟩

/-- **相対位相 `g⁻¹ * h` は左移動で動かない。**
名札そのものは左移動の不変量になれず、差だけが残る。 -/
theorem relative_label_invariant (k g h : G) : (k * g)⁻¹ * (k * h) = g⁻¹ * h := by
  group

/-- **右移動でも同じことが右側で起きる。**`g * h⁻¹` が右移動の不変量。 -/
theorem relative_label_invariant' (k g h : G) : (g * k) * (h * k)⁻¹ = g * h⁻¹ := by
  group

/-- **まとめ。**軸は捩れ子: 名札の集合は推移的に動かせるが、
**差 `g⁻¹ * h` だけが残る**。頂 `𝓦` はどの向きから見ても同じ（`W^θ = W^φ`）。 -/
theorem axes_form_a_torsor (g h : G) (a : α) :
    (∀ k : G, (k * g)⁻¹ * (k * h) = g⁻¹ * h) ∧
      lrot (h * g⁻¹) (E.axis g a : E G α) = E.axis h a ∧
      (E.axis g a : E G α) ⊔ E.axis h a = (if g = h then E.axis g a else ⊤) := by
  refine ⟨fun k => relative_label_invariant k g h, axes_homogeneous g h a, ?_⟩
  by_cases hgh : g = h
  · subst hgh; simp [same_axis_sup]
  · simp [hgh, axes_join_to_world hgh]


/-- **中心の元は順序を忘れる。**
全員と可換な名札では、左移動どうしが可換になる。`Q8` では `±1` がこれ。 -/
theorem lrot_comm_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) (h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x) := by
  rcases x with _ | ⟨k, a⟩ | _
  · rfl
  · simp only [lrot_axis, ← mul_assoc,
      (Subgroup.mem_center_iff.mp hg h)]
  · rfl

/-- **群で添字を付けると和が不変。**左移動は名札の置換なので、
全体の和は動かない。 -/
theorem sum_translate_invariant {M : Type*} [AddCommMonoid M] [Fintype G]
    (f : G → M) (g : G) : ∑ k, f (g * k) = ∑ k, f k :=
  Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

end GroupLabels

/-- 可換群を名札にすると、左移動どうしも可換になる（＝ℤ/4 の場合）。 -/
theorem lrot_comm_of_comm {G : Type*} [CommGroup G] [DecidableEq G] (g h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x) := by
  rcases x with _ | ⟨k, a⟩ | _
  · rfl
  · simp only [lrot_axis, ← mul_assoc, mul_comm g h]
  · rfl

/-! ### 八方向 — 名札を四元数群 Q8 に取る -/

/-- 八方向。`Q8 = {±1, ±i, ±j, ±k}`。 -/
abbrev Eight (α : Type v) := E (QuaternionGroup 2) α

/-- Q8 は位数 8。四方向が八方向になる。 -/
theorem q8_card : Fintype.card (QuaternionGroup 2) = 8 := by decide

/-- **Q8 は非可換。** -/
theorem q8_not_comm : ∃ g h : QuaternionGroup 2, g * h ≠ h * g := by decide


/-- **Q8 には非自明な中心元が在る**——`±1` の `−1` にあたる。
そこだけ順序が潰れる（`lrot_comm_of_mem_center`）。 -/
theorem q8_center_nontrivial : ∃ z : QuaternionGroup 2, z ≠ 1 ∧ ∀ g, z * g = g * z := by
  decide

/-- だが全員が中心にいるわけではない。**六つは順序を覚える。** -/
theorem q8_center_proper : ∃ z : QuaternionGroup 2, ∃ g, z * g ≠ g * z := q8_not_comm

/-- **非可換な名札だと、左移動どうしが可換でない。**
順序が結果に残る——干渉に要ると測った性質が、構造から出る。 -/
theorem lrot_not_comm (a : α) :
    ∃ g h : QuaternionGroup 2,
      lrot g (lrot h (E.axis 1 a : Eight α)) ≠
        lrot h (lrot g (E.axis 1 a : Eight α)) := by
  obtain ⟨g, h, hgh⟩ := q8_not_comm
  refine ⟨g, h, ?_⟩
  simp only [lrot_axis, mul_one]
  intro hc
  rw [E.axis.injEq] at hc
  exact hgh hc.1

/-- 対して `ℤ/4`（可換）では左移動どうしが可換。**四方向では順序が消える。** -/
theorem four_lrot_comm {G : Type*} [CommGroup G] [DecidableEq G] (g h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x) :=
  lrot_comm_of_comm g h x

/-- 八方向でも束は同じ。`§1`〜`§3` の定理がそのまま効く。 -/
theorem eight_axes_join_to_world {g h : QuaternionGroup 2} (hgh : g ≠ h) (a b : α) :
    (E.axis g a : Eight α) ⊔ E.axis h b = ⊤ := axes_join_to_world hgh a b

theorem eight_axes_meet_at_lmonad {g h : QuaternionGroup 2} (hgh : g ≠ h) (a b : α) :
    (E.axis g a : Eight α) ⊓ E.axis h b = ⊥ := axes_meet_at_lmonad hgh a b


/-! ### 順序が潰れるとはどういうことか

経路の振幅は「訪れた名札の列」に表現 `f` を掛けて**並べた積**である。

    振幅(l) = f(k₁) · f(k₂) · … · f(k_T)        l = [k₁, …, k_T]

「順序が潰れる」とは、`l` を並べ替えても積が変わらないこと。これは束の話では
なく**リストの積**の話で、可換なら定理、非可換なら反例が在る。 -/

section PathAmplitude

variable {G : Type*} {M : Type*}

/-- 訪れた名札の列に `f` を掛けて並べた積。経路の振幅にあたる。 -/
def pathAmp [Monoid M] (f : G → M) (l : List G) : M := (l.map f).prod

@[simp] theorem pathAmp_nil [Monoid M] (f : G → M) : pathAmp f [] = 1 := rfl

@[simp] theorem pathAmp_cons [Monoid M] (f : G → M) (g : G) (l : List G) :
    pathAmp f (g :: l) = f g * pathAmp f l := rfl

/-- **可換なら順序が潰れる。**
訪問列を並べ替えても振幅は変わらない——経路は順序を覚えていない。 -/
theorem amp_perm_invariant [CommMonoid M] (f : G → M) {l₁ l₂ : List G}
    (h : l₁.Perm l₂) : pathAmp f l₁ = pathAmp f l₂ :=
  (h.map f).prod_eq

/-- 生成元の列に沿って軸を移りながら、訪れた名札を並べる。 -/
def visited [Mul G] (start : G) : List G → List G
  | [] => []
  | g :: gs => start :: visited (g * start) gs

@[simp] theorem visited_nil [Mul G] (start : G) : visited start [] = [] := rfl

@[simp] theorem visited_cons [Mul G] (start g : G) (gs : List G) :
    visited start (g :: gs) = start :: visited (g * start) gs := rfl

theorem visited_length [Mul G] (start : G) (gs : List G) :
    (visited start gs).length = gs.length := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih => simp [ih]

end PathAmplitude

/-- **非可換なら順序が残る。**
並べ替えると振幅が変わる列が実在する——`Q8` の `[i, j]` と `[j, i]`。 -/
theorem amp_perm_not_invariant :
    ∃ l₁ l₂ : List (QuaternionGroup 2),
      l₁.Perm l₂ ∧ pathAmp id l₁ ≠ pathAmp id l₂ := by
  obtain ⟨g, h, hgh⟩ := q8_not_comm
  refine ⟨[g, h], [h, g], List.Perm.swap _ _ _, ?_⟩
  simpa [pathAmp] using hgh

end HorizontalSum
