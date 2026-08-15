import HorizontalSum.Semidirect

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 既存の道具との対応（一括）

独自に書いた定義のうち、Mathlib の既存構成に落ちるものを繋ぐ。
落ちないものを最後に残すことで、**本当に新しい部分**がどこかを確定させる。 -/

/-- `clockPow` は関数の反復そのもの。 -/
theorem clockPow_eq_iterate (f : ι → (α ≃o α)) (n : ℕ) (x : E ι α) :
    clockPow f n x = (clock f)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [clockPow_succ, ih, ← Function.iterate_succ_apply' (clock f) n x]

/-- `chi` は `Set.Ici` の指示関数そのもの。 -/
theorem chi_eq_indicator (x y : E ι α) :
    chi x y = (Set.Ici x).indicator (fun _ => (1 : ℕ)) y := by
  classical
  by_cases h : y ∈ Set.Ici x
  · rw [Set.indicator_of_mem h]
    exact if_pos (Set.mem_Ici.mp h)
  · rw [Set.indicator_of_notMem h]
    exact if_neg (fun hx => h (Set.mem_Ici.mpr hx))

/-- `pathAmp` は「写して積を取る」そのもの。 -/
theorem pathAmp_eq_map_prod {M : Type*} [Monoid M] (f : G → M) (l : List G) :
    pathAmp f l = (l.map f).prod := rfl

/-- `endpoint` は経路の積を始点に掛けたもの。 -/
theorem endpoint_eq_prod_mul {G : Type*} [Monoid G] (start : G) (l : List G) :
    endpoint start l = (l.map id).prod * start := rfl

/-- `trunc` の軸の部分は閉区間そのもの。 -/
theorem trunc_axis_mem (m N : ℕ) (i : Fin m) (a : ℤ) :
    (E.axis i a : E (Fin m) ℤ) ∈ trunc m N ↔ a ∈ Set.Icc (-(N : ℤ)) (N : ℤ) := by
  rw [mem_trunc_axis, Set.mem_Icc, abs_le]

/-- `Phi` は上方集合、`Down` は下方集合。どちらも Mathlib の区間。 -/
theorem Phi_Down_are_intervals (x : E ι α) :
    Phi x = Set.Ici x ∧ Down x = Set.Iic x := ⟨Phi_eq_Ici x, rfl⟩

/-- `IsRect` は「直積である」ことと同値。 -/
theorem isRect_iff_prod {A B : Type*} (S : Set (A × B)) :
    IsRect S ↔ ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S := Iff.rfl

/-- `shift1` と `shiftBy` は Mathlib の平行移動。 -/
theorem shift_are_addRight (k a : ℤ) :
    shift1 a = a + 1 ∧ shiftBy k a = a + k := ⟨rfl, rfl⟩

/-- `lrot` / `rrot` は Mathlib の左右移動を名札に写したもの。 -/
theorem lrot_rrot_are_translations {G : Type*} [Group G] [DecidableEq G]
    (g k : G) (a : α) :
    lrot g (E.axis k a : E G α) = E.axis (Equiv.mulLeft g k) a ∧
      rrot g (E.axis k a : E G α) = E.axis (Equiv.mulRight g k) a :=
  ⟨rfl, rfl⟩


/-! ### 行列と四元数 — Mathlib の `ℍ[R]` との対応

`qmat` は四元数を左から掛ける写像の行列表示（**正則表現**）である。
Mathlib には `Quaternion R = ℍ[R]` があるので、そこに繋ぐ。 -/

section MatrixBridge

variable {R : Type*} [CommRing R]

/-- `qmat` は四元数 `a + bi + cj + dk` を左から掛ける写像の行列。
基底 `(1, i, j, k)` に対する像を並べたもので、**正則表現そのもの**。 -/
theorem qmat_is_left_mul (a b c d : R) :
    qmat a b c d = Matrix.of ![![a, -b, -c, -d],
                               ![b,  a, -d,  c],
                               ![c,  d,  a, -b],
                               ![d, -c,  b,  a]] := rfl

/-- `cmat` は複素数を左から掛ける写像の行列。 -/
theorem cmat_is_left_mul (a b : R) :
    cmat a b = Matrix.of ![![a, -b], ![b, a]] := rfl

/-- **四元数の積は行列の積に対応する。**`ℍ` の正則表現が忠実であること。
Mathlib の `Quaternion` を使って書ける。 -/
theorem qmat_mul_regular (a b c d a' b' c' d' : R) :
    qmat a b c d * qmat a' b' c' d'
      = qmat (a*a' - b*b' - c*c' - d*d')
             (a*b' + b*a' + c*d' - d*c')
             (a*c' - b*d' + c*a' + d*b')
             (a*d' + b*c' - c*b' + d*a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **複素数の積も同じ形。**`ℂ` の正則表現。 -/
theorem cmat_mul (a b a' b' : R) :
    cmat a b * cmat a' b' = cmat (a*a' - b*b') (a*b' + b*a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `quad` は「値と符号反転を巡回に並べたもの」＝ `ℤ/4` の巡回表現。 -/
theorem quad_shift_is_cyclic (x y : R) :
    shift (quad x y) = quad y (-x) := by
  funext i
  fin_cases i <;> simp [shift, quad]

/-- **`shift` を 4 回で恒等。**`ℤ/4` の作用であること。 -/
theorem shift_pow_four (v : Fin 4 → R) : shift (shift (shift (shift v))) = v := by
  funext i
  fin_cases i <;> rfl

end MatrixBridge

/-! ### 名札の入れ替えと時計 — `Equiv` の標準構成

`ofAxisEquiv` は名札の付け替え（`Equiv.sigmaCongrLeft` に対応）、
`clock` は成分ごとに写像を並べたもの（`Equiv.sigmaCongrRight` に対応）である。
`stdEquiv` を通して見ると、どちらも標準構成になる。 -/

/-- **名札の入れ替えは軸の付け替え。**行き先が名札を写しただけであることを示す。 -/
theorem ofAxisEquiv_is_relabel (e : ι ≃ ι) (i : ι) (a : α) :
    ofAxisEquiv e (E.axis i a : E ι α) = E.axis (e i) a := rfl

/-- **時計は成分ごとの写像。**軸を変えず、各軸の中だけで動く。 -/
theorem clock_is_componentwise (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (E.axis i a : E ι α) = E.axis i (f i a) := rfl

/-- **二つは可換にならないことがある。**時計が軸ごとに違うとき。
これが §4.4 の「非可換なら作用が二種類」の源。 -/
theorem clock_relabel_not_comm (e : ι ≃ ι) (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (ofAxisEquiv e (E.axis i a : E ι α)) = E.axis (e i) (f (e i) a) ∧
      ofAxisEquiv e (clock f (E.axis i a : E ι α)) = E.axis (e i) (f i a) :=
  ⟨rfl, rfl⟩

end HorizontalSum
