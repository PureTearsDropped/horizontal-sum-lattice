import HorizontalSum.Group

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

/-! ### 四つ組による具体模型

四方向を抽象的な名札 `ZMod 4` で扱ってきたが、具体的に書くこともできる。

    A^θ = (sin θ, cos θ, −sin θ, −cos θ)

**四つの座標が、四つの方向 `W, W^i, W^(−1), W^(−i)` に一対一で対応する。**
このとき `×i`（回転）は **座標を一つずらすだけ**になる（`shift_quad`）。
半径 `r` を掛けたものが軸の中の高さで、`r = 0` が 𝓛、`r → ∞` が `W^θ`。 -/

section Quad

variable {R : Type*} [AddCommGroup R]

/-- 四つ組 `(x, y, −x, −y)`。`x = sin θ`, `y = cos θ` と読む。 -/
def quad (x y : R) : Fin 4 → R := ![x, y, -x, -y]

/-- 座標を一つずらす。 -/
def shift (v : Fin 4 → R) : Fin 4 → R := fun i => v (i + 1)

/-- **成分の和は常にゼロ。**四つ組は 4 次元の中の 2 次元部分空間に住む。 -/
theorem quad_sum (x y : R) : ∑ i, quad x y i = 0 := by
  simp [quad, Fin.sum_univ_four]

/-- **一つずらすのが ×i。**
`(sin θ, cos θ) ↦ (cos θ, −sin θ) = (sin(θ+π/2), cos(θ+π/2))`。 -/
theorem shift_quad (x y : R) : shift (quad x y) = quad y (-x) := by
  funext i
  fin_cases i <;> simp [shift, quad]

/-- 二つずらすと符号反転。`W^(θ+π) = −W^θ`——`𝓛` 中心の鏡映にあたる。 -/
theorem shift_shift_quad (x y : R) :
    shift (shift (quad x y)) = quad (-x) (-y) := by
  rw [shift_quad, shift_quad]

/-- 四つずらすと元に戻る。`rot_pow_four` の具体版。 -/
theorem shift_four (v : Fin 4 → R) : shift (shift (shift (shift v))) = v := by
  funext i
  simp only [shift]
  congr 1
  revert i
  decide

/-- `A^0 = 𝓛`。半径ゼロが原点。 -/
theorem quad_zero : quad (0 : R) 0 = 0 := by
  funext i
  fin_cases i <;> simp [quad]

/-- 半径 `r` を掛けても四つ組の形は保たれる（軸の中を進んでも方向は変わらない）。 -/
theorem smul_quad {S : Type*} [Monoid S] [DistribMulAction S R] (r : S) (x y : R) :
    (r • quad x y) = quad (r • x) (r • y) := by
  funext i
  fin_cases i <;> simp [quad]

end Quad



/-! ### アフィン版 — 𝓛 = (1,1,1,1) に置くと確率が出る

四つ組の原点を 𝓛 = (1,1,1,1) に移す。

    A(x, y) = 𝓛 + (x, y, −x, −y) = (1+x, 1+y, 1−x, 1−y)

`(1,1,1,1)` は**巡回シフトで不動**なので、`×i` の性質はそのまま保たれる。
そのうえで成分の和が `0` から `4` に変わり、**規格化できる**ようになる。
`x² + y² < 1` なら全成分が正なので、`A/4` は確率分布になり、
`𝓛` はその中の**一様分布**にあたる。 -/

section Affine

variable {R : Type*} [CommRing R]

/-- 𝓛 = (1,1,1,1)。 -/
def one4 : Fin 4 → R := ![1, 1, 1, 1]

/-- アフィン四つ組 `A(x,y) = 𝓛 + (x, y, −x, −y)`。 -/
def aquad (x y : R) : Fin 4 → R := ![1 + x, 1 + y, 1 - x, 1 - y]

/-- **𝓛 は巡回シフトで不動。** だから `×i` は 𝓛 を動かさない。 -/
theorem shift_one4 : shift (one4 : Fin 4 → R) = one4 := by
  funext i
  fin_cases i <;> simp [shift, one4]

/-- アフィン版は「𝓛 ＋ 四つ組」に他ならない。 -/
theorem aquad_eq (x y : R) : aquad x y = fun i => one4 i + quad x y i := by
  funext i
  fin_cases i <;> simp [aquad, one4, quad] <;> ring

/-- `A(0,0) = 𝓛`。 -/
theorem aquad_zero : aquad (0 : R) 0 = one4 := by
  funext i
  fin_cases i <;> simp [aquad, one4]

/-- **成分の和は常に 4。** 前は 0 だったので割れなかった。 -/
theorem aquad_sum (x y : R) : ∑ i, aquad x y i = 4 := by
  first
    | (simp [aquad, Fin.sum_univ_four]; ring)
    | simp [aquad, Fin.sum_univ_four]

/-- **一つずらすのが ×i。** アフィンにしても保たれる。 -/
theorem shift_aquad (x y : R) : shift (aquad x y) = aquad y (-x) := by
  funext i
  fin_cases i <;> simp [shift, aquad] <;> ring

/-- 二つずらすと 𝓛 を中心に反転する。 -/
theorem shift_shift_aquad (x y : R) :
    shift (shift (aquad x y)) = aquad (-x) (-y) := by
  rw [shift_aquad, shift_aquad]

/-- **二次不変量。**対蹠の対を掛けて足すと `2 − (x²+y²)`——
`θ` に依らず**半径だけ**で決まる。 -/
theorem aquad_quadratic (x y : R) :
    aquad x y 0 * aquad x y 2 + aquad x y 1 * aquad x y 3
      = 2 - (x ^ 2 + y ^ 2) := by
  simp [aquad]
  ring

end Affine

section AffineOrdered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **半径が 1 より小さければ全成分が正。**確率になれる領域。 -/
theorem aquad_pos {x y : K} (h : x ^ 2 + y ^ 2 < 1) (i : Fin 4) :
    0 < aquad x y i := by
  fin_cases i <;> simp [aquad] <;>
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + 1), sq_nonneg (x - 1),
      sq_nonneg (y + 1), sq_nonneg (y - 1)]

/-- **`A/4` は確率分布。**和が 1 になる。 -/
theorem aquad_prob (x y : K) : ∑ i, aquad x y i / 4 = 1 := by
  rw [← Finset.sum_div, aquad_sum]
  norm_num

/-- **𝓛 は一様分布。**`(1/4, 1/4, 1/4, 1/4)`。 -/
theorem one4_uniform (i : Fin 4) : (one4 : Fin 4 → K) i / 4 = 1 / 4 := by
  fin_cases i <;> simp [one4]

end AffineOrdered

end HorizontalSum
