import HorizontalSum.Quad

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

/-! ### 十六成分の座標 — 四元数版

四つ組は「`z` を掛ける写像」と同じ成分数をもっていた。四元数にすると
`4×4 = 16` 成分になる。

    ℂ:  z を掛ける = 2×2 実行列 = **4 成分**（独立なのは 2 個）
    ℍ:  q を掛ける = 4×4 実行列 = **16 成分**（独立なのは 4 個）

二次不変量も同じ形で生きる——`L_z L_z̄ = |z|²·1`、`L_q L_q̄ = |q|²·1`。 -/

section Matrices

variable {R : Type*} [CommRing R]

/-- `z = a + bi` を左から掛ける 2×2 行列。**4 成分**。 -/
def cmat (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, -b; b, a]

/-- `q = a + bi + cj + dk` を左から掛ける 4×4 行列。**16 成分**。 -/
def qmat (a b c d : R) : Matrix (Fin 4) (Fin 4) R :=
  !![a, -b, -c, -d;
     b,  a, -d,  c;
     c,  d,  a, -b;
     d, -c,  b,  a]

/-- 四元数の積（実部）。 -/
def qRe (a b c d e f g h : R) : R := a * e - b * f - c * g - d * h
/-- 四元数の積（i 成分）。 -/
def qI (a b c d e f g h : R) : R := a * f + b * e + c * h - d * g
/-- 四元数の積（j 成分）。 -/
def qJ (a b c d e f g h : R) : R := a * g - b * h + c * e + d * f
/-- 四元数の積（k 成分）。 -/
def qK (a b c d e f g h : R) : R := a * h + b * g - c * f + d * e

/-- `1` の行列は単位行列。 -/
theorem qmat_one : qmat (1 : R) 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmat, Matrix.one_apply]

/-- 実数倍はスカラー行列。 -/
theorem qmat_scalar (n : R) : qmat n 0 0 0 = n • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qmat, Matrix.one_apply]

/-- **行列の積が四元数の積になる。**左掛けは環準同型。 -/
theorem qmat_mul (a b c d e f g h : R) :
    qmat a b c d * qmat e f g h =
      qmat (qRe a b c d e f g h) (qI a b c d e f g h)
        (qJ a b c d e f g h) (qK a b c d e f g h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, qRe, qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **二次不変量。**`L_q L_q̄ = |q|²·1`。 -/
theorem qmat_conj (a b c d : R) :
    qmat a b c d * qmat a (-b) (-c) (-d)
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  rw [qmat_mul]
  have : qRe a b c d a (-b) (-c) (-d) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    simp [qRe]; ring
  rw [show qI a b c d a (-b) (-c) (-d) = 0 by simp [qI]; ring,
      show qJ a b c d a (-b) (-c) (-d) = 0 by simp [qJ]; ring,
      show qK a b c d a (-b) (-c) (-d) = 0 by simp [qK]; ring, this,
      qmat_scalar]

/-- ℂ 側も同じ形。`L_z L_z̄ = |z|²·1`。 -/
theorem cmat_conj (a b : R) :
    cmat a b * cmat a (-b) = (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- ℂ 側の行列式は `|z|²`。 -/
theorem cmat_det (a b : R) : (cmat a b).det = a ^ 2 + b ^ 2 := by
  simp [cmat, Matrix.det_fin_two]
  ring

/-- 跡は `4·(実部)`。 -/
theorem qmat_trace (a b c d : R) : (qmat a b c d).trace = 4 * a := by
  simp [qmat, Matrix.trace, Matrix.diag, Fin.sum_univ_four]
  ring

/-- **16 成分だが、独立なのは 4 個。** -/
theorem qmat_injective {a b c d a' b' c' d' : R}
    (h : qmat a b c d = qmat a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [qmat] using congrFun (congrFun h 0) 0
  · simpa [qmat] using congrFun (congrFun h 1) 0
  · simpa [qmat] using congrFun (congrFun h 2) 0
  · simpa [qmat] using congrFun (congrFun h 3) 0

end Matrices

/-- **四元数は非可換。**`L_i L_j ≠ L_j L_i`。 -/
theorem qmat_not_comm :
    qmat (0 : ℚ) 1 0 0 * qmat 0 0 1 0 ≠ qmat 0 0 1 0 * qmat (0 : ℚ) 1 0 0 := by
  rw [qmat_mul, qmat_mul]
  intro hc
  have := (qmat_injective hc).2.2.2
  simp [qK] at this
  exact absurd this (by norm_num)

/-- 対して ℂ は可換。`L_z L_w = L_w L_z`。 -/
theorem cmat_comm (a b e f : R) [CommRing R] :
    cmat a b * cmat e f = cmat e f * cmat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring


/-- **𝓛 は基底の和。**`e₀ + e₁ + e₂ + e₃ = (1,1,1,1)`。 -/
theorem one4_eq_sum_basis {R : Type*} [CommRing R] :
    (∑ i : Fin 4, Pi.single i (1 : R)) = (one4 : Fin 4 → R) := by
  funext j
  fin_cases j <;> simp [one4, Fin.sum_univ_four, Pi.single_apply]

/-- **基底で添字を付けると壊れる。**
`×i` は基底 `{1,i,j,k}` を**符号つきに**動かすので、全 1 ベクトルが不動でない。 -/
theorem basis_not_invariant :
    (qmat (0 : ℚ) 1 0 0).mulVec ![1, 1, 1, 1] ≠ ![1, 1, 1, 1] := by
  intro h
  have := congrFun h 0
  simp [qmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this
  exact absurd this (by norm_num)

/-- しかも和も保たれない（`4` が `0` になる）。 -/
theorem basis_sum_not_invariant :
    ∑ i, (qmat (0 : ℚ) 1 0 0).mulVec ![1, 1, 1, 1] i = 0 := by
  simp [qmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

end HorizontalSum
