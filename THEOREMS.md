# `HorizontalSum.lean` の宣言一覧

`HorizontalSum/*.lean` から機械的に抜き出したもの。**この文書に意味づけは入らない。**
在るのは宣言名と型（定理なら主張そのもの）だけで、読み・動機・解釈は
`DESIGN.md` / `READING.md` の側に置く。生成は `tools/gen_theorems.py`。

    定理・補題   361
    定義・実装   73
    合計         434

すべて Lean 4 + Mathlib で受理済み（`sorryAx` なし）。検証は
`python tools/verify.py` が `#print axioms` の出力から確かめる。

順序はソースに現れる順。見出しはモジュール名と各ファイルの `/-! … -/` の区切り
そのものである。

---

## Basic

**`HorizontalSum.E`**

```lean
inductive E (ι : Type u) (α : Type v) where
  | lmonad : E ι α
  | axis : ι → α → E ι α
  | world : E ι α
```

**`HorizontalSum.E.le`**

```lean
def E.le : E ι α → E ι α → Prop
  | .lmonad, _ => True
  | .axis _ _, .lmonad => False
  | .axis i a, .axis j b => i = j ∧ a ≤ b
  | .axis _ _, .world => True
  | .world, .lmonad => False
  | .world, .axis _ _ => False
  | .world, .world => True
```

**`HorizontalSum.E.sup`**

```lean
def E.sup : E ι α → E ι α → E ι α
  | .lmonad, y => y
  | .axis i a, .lmonad => .axis i a
  | .axis i a, .axis j b => if i = j then .axis i (a ⊔ b) else .world
  | .axis _ _, .world => .world
  | .world, _ => .world
```

**`HorizontalSum.E.inf`**

```lean
def E.inf : E ι α → E ι α → E ι α
  | .lmonad, _ => .lmonad
  | .axis _ _, .lmonad => .lmonad
  | .axis i a, .axis j b => if i = j then .axis i (a ⊓ b) else .lmonad
  | .axis i a, .world => .axis i a
  | .world, y => y
```

**`HorizontalSum.lmonad_le`**

```lean
@[simp] theorem lmonad_le (y : E ι α) : E.le E.lmonad y
```

**`HorizontalSum.le_world`**

```lean
@[simp] theorem le_world (x : E ι α) : E.le x E.world
```

**`HorizontalSum.axis_le_axis`**

```lean
@[simp] theorem axis_le_axis {i j : ι} {a b : α} :
    E.le (E.axis i a) (E.axis j b) ↔ i = j ∧ a ≤ b
```

**`HorizontalSum.not_axis_le_lmonad`**

```lean
@[simp] theorem not_axis_le_lmonad {i : ι} {a : α} :
    ¬ E.le (E.axis i a : E ι α) E.lmonad
```

**`HorizontalSum.not_world_le_lmonad`**

```lean
@[simp] theorem not_world_le_lmonad : ¬ E.le (E.world : E ι α) E.lmonad
```

**`HorizontalSum.not_world_le_axis`**

```lean
@[simp] theorem not_world_le_axis {i : ι} {a : α} :
    ¬ E.le (E.world : E ι α) (E.axis i a)
```

**`HorizontalSum.lmonad_sup`**

```lean
@[simp] theorem lmonad_sup (y : E ι α) : E.sup E.lmonad y = y
```

**`HorizontalSum.sup_lmonad`**

```lean
@[simp] theorem sup_lmonad (x : E ι α) : E.sup x E.lmonad = x
```

**`HorizontalSum.world_sup`**

```lean
@[simp] theorem world_sup (y : E ι α) : E.sup E.world y = E.world
```

**`HorizontalSum.sup_world`**

```lean
@[simp] theorem sup_world (x : E ι α) : E.sup x E.world = E.world
```

**`HorizontalSum.axis_sup_axis`**

```lean
@[simp] theorem axis_sup_axis {i j : ι} {a b : α} :
    E.sup (E.axis i a) (E.axis j b)
      = if i = j then E.axis i (a ⊔ b) else E.world
```

**`HorizontalSum.lmonad_inf`**

```lean
@[simp] theorem lmonad_inf (y : E ι α) : E.inf E.lmonad y = E.lmonad
```

**`HorizontalSum.inf_lmonad`**

```lean
@[simp] theorem inf_lmonad (x : E ι α) : E.inf x E.lmonad = E.lmonad
```

**`HorizontalSum.world_inf`**

```lean
@[simp] theorem world_inf (y : E ι α) : E.inf E.world y = y
```

**`HorizontalSum.inf_world`**

```lean
@[simp] theorem inf_world (x : E ι α) : E.inf x E.world = x
```

**`HorizontalSum.axis_inf_axis`**

```lean
@[simp] theorem axis_inf_axis {i j : ι} {a b : α} :
    E.inf (E.axis i a) (E.axis j b)
      = if i = j then E.axis i (a ⊓ b) else E.lmonad
```

**`HorizontalSum.instLattice`**

```lean
instance instLattice : Lattice (E ι α) where
  le
```

**`HorizontalSum.instBoundedOrder`**

```lean
instance instBoundedOrder : BoundedOrder (E ι α) where
  bot
```

**`HorizontalSum.bot_def`**

```lean
@[simp] theorem bot_def : (⊥ : E ι α) = E.lmonad
```

**`HorizontalSum.top_def`**

```lean
@[simp] theorem top_def : (⊤ : E ι α) = E.world
```

**`HorizontalSum.le_iff`**

```lean
@[simp] theorem le_iff {x y : E ι α} : x ≤ y ↔ E.le x y
```

**`HorizontalSum.sup_def`**

```lean
@[simp] theorem sup_def (x y : E ι α) : x ⊔ y = E.sup x y
```

**`HorizontalSum.inf_def`**

```lean
@[simp] theorem inf_def (x y : E ι α) : x ⊓ y = E.inf x y
```

## 土台と骨格 — 束を作り、W^θ = W^φ を出す

### W = W⁻¹ = W^i = W^(−i)

**`HorizontalSum.axes_join_to_world`**

```lean
theorem axes_join_to_world {i j : ι} (h : i ≠ j) (a b : α) :
    (E.axis i a : E ι α) ⊔ E.axis j b = ⊤
```

**`HorizontalSum.axes_meet_at_lmonad`**

```lean
theorem axes_meet_at_lmonad {i j : ι} (h : i ≠ j) (a b : α) :
    (E.axis i a : E ι α) ⊓ E.axis j b = ⊥
```

**`HorizontalSum.same_axis_sup`**

```lean
theorem same_axis_sup (i : ι) (a b : α) :
    (E.axis i a : E ι α) ⊔ E.axis i b = E.axis i (a ⊔ b)
```

**`HorizontalSum.same_axis_inf`**

```lean
theorem same_axis_inf (i : ι) (a b : α) :
    (E.axis i a : E ι α) ⊓ E.axis i b = E.axis i (a ⊓ b)
```

#### 台を既存の構成で書く — `WithBot (WithTop (Σ i, α))`

**`HorizontalSum.toStd`**

```lean
def toStd : E ι α → WithBot (WithTop (Σ _ : ι, α))
  | .lmonad => ⊥
  | .axis i a => (((⟨i, a⟩ : Σ _ : ι, α) : WithTop (Σ _ : ι, α)) : WithBot _)
  | .world => ((⊤ : WithTop (Σ _ : ι, α)) : WithBot _)
```

**`HorizontalSum.ofStd`**

```lean
def ofStd : WithBot (WithTop (Σ _ : ι, α)) → E ι α
  | none => .lmonad
  | some none => .world
  | some (some p) => .axis p.1 p.2
```

**`HorizontalSum.ofStd_toStd`**

```lean
@[simp] theorem ofStd_toStd (x : E ι α) : ofStd (toStd x) = x
```

**`HorizontalSum.toStd_ofStd`**

```lean
@[simp] theorem toStd_ofStd (x : WithBot (WithTop (Σ _ : ι, α))) :
    toStd (ofStd x) = x
```

**`HorizontalSum.toStd_le_iff`**

```lean
theorem toStd_le_iff (x y : E ι α) : toStd x ≤ toStd y ↔ x ≤ y
```

**`HorizontalSum.stdEquiv`**

```lean
def stdEquiv : E ι α ≃o WithBot (WithTop (Σ _ : ι, α)) where
  toFun
```

**`HorizontalSum.stdEquiv_lmonad`**

```lean
theorem stdEquiv_lmonad : stdEquiv (E.lmonad : E ι α) = ⊥
```

**`HorizontalSum.stdEquiv_world`**

```lean
theorem stdEquiv_world :
    stdEquiv (E.world : E ι α) = ((⊤ : WithTop (Σ _ : ι, α)) : WithBot _)
```

**`HorizontalSum.stdEquiv_axis`**

```lean
theorem stdEquiv_axis (i : ι) (a : α) :
    stdEquiv (E.axis i a : E ι α)
      = (((⟨i, a⟩ : Σ _ : ι, α) : WithTop (Σ _ : ι, α)) : WithBot _)
```

## Rotation

## 名札の対称性 — 回転・群・相対位相・四つ組・十六成分

### 名札の対称性 — 回転 ×i と共役

**`HorizontalSum.ofAxisEquiv`**

```lean
def ofAxisEquiv (e : ι ≃ ι) : E ι α ≃o E ι α where
  toFun x
```

**`HorizontalSum.ofAxisEquiv_lmonad`**

```lean
@[simp] theorem ofAxisEquiv_lmonad (e : ι ≃ ι) :
    ofAxisEquiv (α := α) e E.lmonad = E.lmonad
```

**`HorizontalSum.ofAxisEquiv_axis`**

```lean
@[simp] theorem ofAxisEquiv_axis (e : ι ≃ ι) (i : ι) (a : α) :
    ofAxisEquiv (α := α) e (E.axis i a) = E.axis (e i) a
```

**`HorizontalSum.ofAxisEquiv_world`**

```lean
@[simp] theorem ofAxisEquiv_world (e : ι ≃ ι) :
    ofAxisEquiv (α := α) e E.world = E.world
```

**`HorizontalSum.Four`**

```lean
abbrev Four (α : Type v)
```

**`HorizontalSum.rot`**

```lean
def rot : Four α ≃o Four α
```

**`HorizontalSum.conj`**

```lean
def conj : Four α ≃o Four α
```

**`HorizontalSum.conj_involutive`**

```lean
theorem conj_involutive : Function.Involutive (conj : Four α → Four α)
```

**`HorizontalSum.rot_pow_four`**

```lean
theorem rot_pow_four (x : Four α) : rot (rot (rot (rot x))) = x
```

## Group

#### 名札を群に取る — 非可換なら作用が二種類になる

**`HorizontalSum.lrot`**

```lean
def lrot (g : G) : E G α ≃o E G α
```

**`HorizontalSum.rrot`**

```lean
def rrot (g : G) : E G α ≃o E G α
```

**`HorizontalSum.lrot_lmonad`**

```lean
@[simp] theorem lrot_lmonad (g : G) : lrot g (E.lmonad : E G α) = E.lmonad
```

**`HorizontalSum.lrot_world`**

```lean
@[simp] theorem lrot_world (g : G) : lrot g (E.world : E G α) = E.world
```

**`HorizontalSum.lrot_axis`**

```lean
@[simp] theorem lrot_axis (g k : G) (a : α) :
    lrot g (E.axis k a : E G α) = E.axis (g * k) a
```

**`HorizontalSum.rrot_lmonad`**

```lean
@[simp] theorem rrot_lmonad (g : G) : rrot g (E.lmonad : E G α) = E.lmonad
```

**`HorizontalSum.rrot_world`**

```lean
@[simp] theorem rrot_world (g : G) : rrot g (E.world : E G α) = E.world
```

**`HorizontalSum.rrot_axis`**

```lean
@[simp] theorem rrot_axis (g k : G) (a : α) :
    rrot g (E.axis k a : E G α) = E.axis (k * g) a
```

**`HorizontalSum.lrot_rrot_comm`**

```lean
theorem lrot_rrot_comm (g h : G) (x : E G α) :
    lrot g (rrot h x) = rrot h (lrot g x)
```

#### 相対位相だけが不変量 — 軸の名札は捩れ子（torsor）

**`HorizontalSum.axes_homogeneous`**

```lean
theorem axes_homogeneous (g h : G) (a : α) :
    lrot (h * g⁻¹) (E.axis g a : E G α) = E.axis h a
```

**`HorizontalSum.no_distinguished_axis`**

```lean
theorem no_distinguished_axis {g h : G} (hgh : g ≠ h) (a : α) :
    ∃ e : E G α ≃o E G α, e (E.axis g a) ≠ E.axis g a
```

**`HorizontalSum.relative_label_invariant`**

```lean
theorem relative_label_invariant (k g h : G) : (k * g)⁻¹ * (k * h) = g⁻¹ * h
```

**`HorizontalSum.relative_label_invariant'`**

```lean
theorem relative_label_invariant' (k g h : G) : (g * k) * (h * k)⁻¹ = g * h⁻¹
```

**`HorizontalSum.axes_form_a_torsor`**

```lean
theorem axes_form_a_torsor (g h : G) (a : α) :
    (∀ k : G, (k * g)⁻¹ * (k * h) = g⁻¹ * h) ∧
      lrot (h * g⁻¹) (E.axis g a : E G α) = E.axis h a ∧
      (E.axis g a : E G α) ⊔ E.axis h a = (if g = h then E.axis g a else ⊤)
```

**`HorizontalSum.lrot_comm_of_mem_center`**

```lean
theorem lrot_comm_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) (h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x)
```

**`HorizontalSum.sum_translate_invariant`**

```lean
theorem sum_translate_invariant {M : Type*} [AddCommMonoid M] [Fintype G]
    (f : G → M) (g : G) : ∑ k, f (g * k) = ∑ k, f k
```

**`HorizontalSum.lrot_comm_of_comm`**

```lean
theorem lrot_comm_of_comm {G : Type*} [CommGroup G] [DecidableEq G] (g h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x)
```

#### 八方向 — 名札を四元数群 Q8 に取る

**`HorizontalSum.Eight`**

```lean
abbrev Eight (α : Type v)
```

**`HorizontalSum.q8_card`**

```lean
theorem q8_card : Fintype.card (QuaternionGroup 2) = 8
```

**`HorizontalSum.q8_not_comm`**

```lean
theorem q8_not_comm : ∃ g h : QuaternionGroup 2, g * h ≠ h * g
```

**`HorizontalSum.q8_center_nontrivial`**

```lean
theorem q8_center_nontrivial : ∃ z : QuaternionGroup 2, z ≠ 1 ∧ ∀ g, z * g = g * z
```

**`HorizontalSum.q8_center_proper`**

```lean
theorem q8_center_proper : ∃ z : QuaternionGroup 2, ∃ g, z * g ≠ g * z
```

**`HorizontalSum.lrot_not_comm`**

```lean
theorem lrot_not_comm (a : α) :
    ∃ g h : QuaternionGroup 2,
      lrot g (lrot h (E.axis 1 a : Eight α)) ≠
        lrot h (lrot g (E.axis 1 a : Eight α))
```

**`HorizontalSum.four_lrot_comm`**

```lean
theorem four_lrot_comm {G : Type*} [CommGroup G] [DecidableEq G] (g h : G)
    (x : E G α) : lrot g (lrot h x) = lrot h (lrot g x)
```

**`HorizontalSum.eight_axes_join_to_world`**

```lean
theorem eight_axes_join_to_world {g h : QuaternionGroup 2} (hgh : g ≠ h) (a b : α) :
    (E.axis g a : Eight α) ⊔ E.axis h b = ⊤
```

**`HorizontalSum.eight_axes_meet_at_lmonad`**

```lean
theorem eight_axes_meet_at_lmonad {g h : QuaternionGroup 2} (hgh : g ≠ h) (a b : α) :
    (E.axis g a : Eight α) ⊓ E.axis h b = ⊥
```

#### 順序が潰れるとはどういうことか

**`HorizontalSum.pathAmp`**

```lean
def pathAmp [Monoid M] (f : G → M) (l : List G) : M
```

**`HorizontalSum.pathAmp_nil`**

```lean
@[simp] theorem pathAmp_nil [Monoid M] (f : G → M) : pathAmp f [] = 1
```

**`HorizontalSum.pathAmp_cons`**

```lean
@[simp] theorem pathAmp_cons [Monoid M] (f : G → M) (g : G) (l : List G) :
    pathAmp f (g :: l) = f g * pathAmp f l
```

**`HorizontalSum.amp_perm_invariant`**

```lean
theorem amp_perm_invariant [CommMonoid M] (f : G → M) {l₁ l₂ : List G}
    (h : l₁.Perm l₂) : pathAmp f l₁ = pathAmp f l₂
```

**`HorizontalSum.visited`**

```lean
def visited [Mul G] (start : G) : List G → List G
  | [] => []
  | g :: gs => start :: visited (g * start) gs
```

**`HorizontalSum.visited_nil`**

```lean
@[simp] theorem visited_nil [Mul G] (start : G) : visited start [] = []
```

**`HorizontalSum.visited_cons`**

```lean
@[simp] theorem visited_cons [Mul G] (start g : G) (gs : List G) :
    visited start (g :: gs) = start :: visited (g * start) gs
```

**`HorizontalSum.visited_length`**

```lean
theorem visited_length [Mul G] (start : G) (gs : List G) :
    (visited start gs).length = gs.length
```

**`HorizontalSum.amp_perm_not_invariant`**

```lean
theorem amp_perm_not_invariant :
    ∃ l₁ l₂ : List (QuaternionGroup 2),
      l₁.Perm l₂ ∧ pathAmp id l₁ ≠ pathAmp id l₂
```

## Quad

#### 四つ組による具体模型

**`HorizontalSum.quad`**

```lean
def quad (x y : R) : Fin 4 → R
```

**`HorizontalSum.shift`**

```lean
def shift (v : Fin 4 → R) : Fin 4 → R
```

**`HorizontalSum.quad_sum`**

```lean
theorem quad_sum (x y : R) : ∑ i, quad x y i = 0
```

**`HorizontalSum.shift_quad`**

```lean
theorem shift_quad (x y : R) : shift (quad x y) = quad y (-x)
```

**`HorizontalSum.shift_shift_quad`**

```lean
theorem shift_shift_quad (x y : R) :
    shift (shift (quad x y)) = quad (-x) (-y)
```

**`HorizontalSum.shift_four`**

```lean
theorem shift_four (v : Fin 4 → R) : shift (shift (shift (shift v))) = v
```

**`HorizontalSum.quad_zero`**

```lean
theorem quad_zero : quad (0 : R) 0 = 0
```

**`HorizontalSum.smul_quad`**

```lean
theorem smul_quad {S : Type*} [Monoid S] [DistribMulAction S R] (r : S) (x y : R) :
    (r • quad x y) = quad (r • x) (r • y)
```

#### アフィン版 — 𝓛 = (1,1,1,1) に置くと確率が出る

**`HorizontalSum.one4`**

```lean
def one4 : Fin 4 → R
```

**`HorizontalSum.aquad`**

```lean
def aquad (x y : R) : Fin 4 → R
```

**`HorizontalSum.shift_one4`**

```lean
theorem shift_one4 : shift (one4 : Fin 4 → R) = one4
```

**`HorizontalSum.aquad_eq`**

```lean
theorem aquad_eq (x y : R) : aquad x y = fun i => one4 i + quad x y i
```

**`HorizontalSum.aquad_zero`**

```lean
theorem aquad_zero : aquad (0 : R) 0 = one4
```

**`HorizontalSum.aquad_sum`**

```lean
theorem aquad_sum (x y : R) : ∑ i, aquad x y i = 4
```

**`HorizontalSum.shift_aquad`**

```lean
theorem shift_aquad (x y : R) : shift (aquad x y) = aquad y (-x)
```

**`HorizontalSum.shift_shift_aquad`**

```lean
theorem shift_shift_aquad (x y : R) :
    shift (shift (aquad x y)) = aquad (-x) (-y)
```

**`HorizontalSum.aquad_quadratic`**

```lean
theorem aquad_quadratic (x y : R) :
    aquad x y 0 * aquad x y 2 + aquad x y 1 * aquad x y 3
      = 2 - (x ^ 2 + y ^ 2)
```

**`HorizontalSum.aquad_pos`**

```lean
theorem aquad_pos {x y : K} (h : x ^ 2 + y ^ 2 < 1) (i : Fin 4) :
    0 < aquad x y i
```

**`HorizontalSum.aquad_prob`**

```lean
theorem aquad_prob (x y : K) : ∑ i, aquad x y i / 4 = 1
```

**`HorizontalSum.one4_uniform`**

```lean
theorem one4_uniform (i : Fin 4) : (one4 : Fin 4 → K) i / 4 = 1 / 4
```

## Matrix

#### 十六成分の座標 — 四元数版

**`HorizontalSum.cmat`**

```lean
def cmat (a b : R) : Matrix (Fin 2) (Fin 2) R
```

**`HorizontalSum.qmat`**

```lean
def qmat (a b c d : R) : Matrix (Fin 4) (Fin 4) R
```

**`HorizontalSum.qRe`**

```lean
def qRe (a b c d e f g h : R) : R
```

**`HorizontalSum.qI`**

```lean
def qI (a b c d e f g h : R) : R
```

**`HorizontalSum.qJ`**

```lean
def qJ (a b c d e f g h : R) : R
```

**`HorizontalSum.qK`**

```lean
def qK (a b c d e f g h : R) : R
```

**`HorizontalSum.qmat_one`**

```lean
theorem qmat_one : qmat (1 : R) 0 0 0 = 1
```

**`HorizontalSum.qmat_scalar`**

```lean
theorem qmat_scalar (n : R) : qmat n 0 0 0 = n • (1 : Matrix (Fin 4) (Fin 4) R)
```

**`HorizontalSum.qmat_mul`**

```lean
theorem qmat_mul (a b c d e f g h : R) :
    qmat a b c d * qmat e f g h =
      qmat (qRe a b c d e f g h) (qI a b c d e f g h)
        (qJ a b c d e f g h) (qK a b c d e f g h)
```

**`HorizontalSum.qmat_conj`**

```lean
theorem qmat_conj (a b c d : R) :
    qmat a b c d * qmat a (-b) (-c) (-d)
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : Matrix (Fin 4) (Fin 4) R)
```

**`HorizontalSum.cmat_conj`**

```lean
theorem cmat_conj (a b : R) :
    cmat a b * cmat a (-b) = (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R)
```

**`HorizontalSum.cmat_det`**

```lean
theorem cmat_det (a b : R) : (cmat a b).det = a ^ 2 + b ^ 2
```

**`HorizontalSum.qmat_trace`**

```lean
theorem qmat_trace (a b c d : R) : (qmat a b c d).trace = 4 * a
```

**`HorizontalSum.qmat_injective`**

```lean
theorem qmat_injective {a b c d a' b' c' d' : R}
    (h : qmat a b c d = qmat a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d'
```

**`HorizontalSum.qmat_not_comm`**

```lean
theorem qmat_not_comm :
    qmat (0 : ℚ) 1 0 0 * qmat 0 0 1 0 ≠ qmat 0 0 1 0 * qmat (0 : ℚ) 1 0 0
```

**`HorizontalSum.cmat_comm`**

```lean
theorem cmat_comm (a b e f : R) [CommRing R] :
    cmat a b * cmat e f = cmat e f * cmat a b
```

**`HorizontalSum.one4_eq_sum_basis`**

```lean
theorem one4_eq_sum_basis {R : Type*} [CommRing R] :
    (∑ i : Fin 4, Pi.single i (1 : R)) = (one4 : Fin 4 → R)
```

**`HorizontalSum.basis_not_invariant`**

```lean
theorem basis_not_invariant :
    (qmat (0 : ℚ) 1 0 0).mulVec ![1, 1, 1, 1] ≠ ![1, 1, 1, 1]
```

**`HorizontalSum.basis_sum_not_invariant`**

```lean
theorem basis_sum_not_invariant :
    ∑ i, (qmat (0 : ℚ) 1 0 0).mulVec ![1, 1, 1, 1] i = 0
```

## Phase

#### 四つ組の結びと交わり — 一致するのは両端だけ

**`HorizontalSum.zmod_four_ne`**

```lean
theorem zmod_four_ne (k : ZMod 4) : k ≠ k + 1 ∧ k ≠ k + 2 ∧ k ≠ k + 3
```

**`HorizontalSum.rot_axis`**

```lean
theorem rot_axis (k : ZMod 4) (a : α) :
    rot (E.axis k a : Four α) = E.axis (k + 1) a
```

**`HorizontalSum.rot_bot`**

```lean
theorem rot_bot : rot (⊥ : Four α) = ⊥
```

**`HorizontalSum.rot_top`**

```lean
theorem rot_top : rot (⊤ : Four α) = ⊤
```

**`HorizontalSum.rot_ne_self`**

```lean
theorem rot_ne_self (k : ZMod 4) (a : α) :
    rot (E.axis k a : Four α) ≠ E.axis k a
```

**`HorizontalSum.quad_join_to_world`**

```lean
theorem quad_join_to_world (k : ZMod 4) (a b : α) :
    ((E.axis k a : Four α) ⊔ E.axis (k + 1) b = ⊤) ∧
    ((E.axis k a : Four α) ⊔ E.axis (k + 2) b = ⊤) ∧
    ((E.axis k a : Four α) ⊔ E.axis (k + 3) b = ⊤)
```

**`HorizontalSum.quad_meet_at_lmonad`**

```lean
theorem quad_meet_at_lmonad (k : ZMod 4) (a b : α) :
    ((E.axis k a : Four α) ⊓ E.axis (k + 1) b = ⊥) ∧
    ((E.axis k a : Four α) ⊓ E.axis (k + 2) b = ⊥) ∧
    ((E.axis k a : Four α) ⊓ E.axis (k + 3) b = ⊥)
```

**`HorizontalSum.rot_join_meet`**

```lean
theorem rot_join_meet (k : ZMod 4) (a : α) :
    ((E.axis k a : Four α) ⊔ rot (E.axis k a) = ⊤) ∧
    ((E.axis k a : Four α) ⊓ rot (E.axis k a) = ⊥)
```

## Action

## 位相・時計・作用 — 公理が一つも壊れないこと

### 位相で名付けた軸 — W^θ = W^(−θ) = W^(iθ) = W^(−iθ)

**`HorizontalSum.instDecidableEqComplex`**

```lean
noncomputable instance instDecidableEqComplex : DecidableEq ℂ
```

**`HorizontalSum.quarter`**

```lean
noncomputable def quarter : E ℂ α ≃o E ℂ α
```

**`HorizontalSum.one_sub_I_ne_zero`**

```lean
theorem one_sub_I_ne_zero : (1 : ℂ) - Complex.I ≠ 0
```

**`HorizontalSum.one_add_I_ne_zero`**

```lean
theorem one_add_I_ne_zero : (1 : ℂ) + Complex.I ≠ 0
```

**`HorizontalSum.phase_ne_neg`**

```lean
theorem phase_ne_neg {θ : ℂ} (h : θ ≠ 0) : θ ≠ -θ
```

**`HorizontalSum.phase_ne_mul_I`**

```lean
theorem phase_ne_mul_I {θ : ℂ} (h : θ ≠ 0) : θ ≠ Complex.I * θ
```

**`HorizontalSum.phase_ne_neg_mul_I`**

```lean
theorem phase_ne_neg_mul_I {θ : ℂ} (h : θ ≠ 0) : θ ≠ -(Complex.I * θ)
```

**`HorizontalSum.all_phases_one_world`**

```lean
theorem all_phases_one_world {θ φ : ℂ} (h : θ ≠ φ) (a b : α) :
    (E.axis θ a : E ℂ α) ⊔ E.axis φ b = ⊤
```

**`HorizontalSum.all_phases_meet_at_lmonad`**

```lean
theorem all_phases_meet_at_lmonad {θ φ : ℂ} (h : θ ≠ φ) (a b : α) :
    (E.axis θ a : E ℂ α) ⊓ E.axis φ b = ⊥
```

**`HorizontalSum.four_phases_one_world`**

```lean
theorem four_phases_one_world {θ : ℂ} (h : θ ≠ 0) (a b : α) :
    ((E.axis θ a : E ℂ α) ⊔ E.axis (-θ) b = ⊤) ∧
    ((E.axis θ a : E ℂ α) ⊔ E.axis (Complex.I * θ) b = ⊤) ∧
    ((E.axis θ a : E ℂ α) ⊔ E.axis (-(Complex.I * θ)) b = ⊤)
```

**`HorizontalSum.four_phases_meet_at_lmonad`**

```lean
theorem four_phases_meet_at_lmonad {θ : ℂ} (h : θ ≠ 0) (a b : α) :
    ((E.axis θ a : E ℂ α) ⊓ E.axis (-θ) b = ⊥) ∧
    ((E.axis θ a : E ℂ α) ⊓ E.axis (Complex.I * θ) b = ⊥) ∧
    ((E.axis θ a : E ℂ α) ⊓ E.axis (-(Complex.I * θ)) b = ⊥)
```

### 作用 — 時計は一つ、速さは軸ごと

**`HorizontalSum.clock`**

```lean
def clock (f : ι → (α ≃o α)) : E ι α → E ι α
  | .lmonad => .lmonad
  | .axis i a => .axis i (f i a)
  | .world => .world
```

**`HorizontalSum.clock_lmonad`**

```lean
@[simp] theorem clock_lmonad (f : ι → (α ≃o α)) :
    clock f (E.lmonad : E ι α) = E.lmonad
```

**`HorizontalSum.clock_axis`**

```lean
@[simp] theorem clock_axis (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (E.axis i a) = E.axis i (f i a)
```

**`HorizontalSum.clock_world`**

```lean
@[simp] theorem clock_world (f : ι → (α ≃o α)) :
    clock f (E.world : E ι α) = E.world
```

**`HorizontalSum.clock_bot`**

```lean
theorem clock_bot (f : ι → (α ≃o α)) : clock f (⊥ : E ι α) = ⊥
```

**`HorizontalSum.clock_mono`**

```lean
theorem clock_mono (f : ι → (α ≃o α)) : Monotone (clock f : E ι α → E ι α)
```

**`HorizontalSum.clock_injective`**

```lean
theorem clock_injective (f : ι → (α ≃o α)) :
    Function.Injective (clock f : E ι α → E ι α)
```

**`HorizontalSum.act`**

```lean
def act (σ : E ι α → E ι α) (a b : E ι α) : E ι α
```

**`HorizontalSum.seven`**

```lean
theorem seven (a : E ι α) : act (clock f) a ⊥ = a
```

**`HorizontalSum.eight`**

```lean
theorem eight (a b : E ι α) :
    act (clock f) a b = act (clock f) ⊥ b ⊔ act (clock f) a ⊥
```

**`HorizontalSum.six`**

```lean
theorem six (a b : E ι α) : a ≤ act (clock f) a b
```

**`HorizontalSum.five`**

```lean
theorem five (a b c : E ι α) (h : a ≤ b) :
    act (clock f) a c ≤ act (clock f) b c
```

**`HorizontalSum.four`**

```lean
theorem four (a : E ι α) : Monotone (act (clock f) a)
```

**`HorizontalSum.nine`**

```lean
theorem nine : Function.Injective (act (clock f) (⊥ : E ι α))
```

**`HorizontalSum.clock_axioms`**

```lean
theorem clock_axioms :
    (∀ a : E ι α, act (clock f) a ⊥ = a) ∧
    (∀ a b : E ι α, act (clock f) a b = act (clock f) ⊥ b ⊔ act (clock f) a ⊥) ∧
    (∀ a b : E ι α, a ≤ act (clock f) a b) ∧
    (∀ a b c : E ι α, a ≤ b → act (clock f) a c ≤ act (clock f) b c) ∧
    (∀ a : E ι α, Monotone (act (clock f) a)) ∧
    Function.Injective (act (clock f) (⊥ : E ι α))
```

## 公理から出る定理 — 先行体系をこの束の上で

### 先行体系をこの束の上で書き直す

**`HorizontalSum.clockIso`**

```lean
def clockIso (f : ι → (α ≃o α)) : E ι α ≃o E ι α where
  toFun
```

**`HorizontalSum.instNontrivial`**

```lean
instance instNontrivial : Nontrivial (E ι α)
```

**`HorizontalSum.infinite_of_infinite`**

```lean
theorem infinite_of_infinite [Infinite α] (i : ι) : Infinite (E ι α)
```

**`HorizontalSum.form`**

```lean
theorem form (a b : E ι α) : act (clock f) a b = act (clock f) ⊥ b ⊔ a
```

**`HorizontalSum.sigma_fixes_lmonad`**

```lean
theorem sigma_fixes_lmonad : act (clock f) (⊥ : E ι α) ⊥ = ⊥
```

**`HorizontalSum.factors_through_lmonad`**

```lean
theorem factors_through_lmonad (a b : E ι α) :
    act (clock f) a b = (fun x => x ⊔ a) (act (clock f) ⊥ b)
```

**`HorizontalSum.second_stage_ignores_target`**

```lean
theorem second_stage_ignores_target (a : E ι α) :
    ∀ b, act (clock f) a b = (fun x => x ⊔ a) (act (clock f) ⊥ b)
```

**`HorizontalSum.second_stage_forgets`**

```lean
theorem second_stage_forgets (a : E ι α) (ha : a ≠ ⊥) :
    ¬ Function.Injective (fun x : E ι α => x ⊔ a)
```

**`HorizontalSum.actor_from_lmonad`**

```lean
theorem actor_from_lmonad {a a' : E ι α}
    (e : act (clock f) a ⊥ = act (clock f) a' ⊥) : a = a'
```

**`HorizontalSum.target_from_lmonad`**

```lean
theorem target_from_lmonad {b b' : E ι α}
    (e : act (clock f) ⊥ b = act (clock f) ⊥ b') : b = b'
```

**`HorizontalSum.order_is_lmonad`**

```lean
theorem order_is_lmonad (a b : E ι α) :
    a ≤ b ↔ act (clock f) a ⊥ ≤ act (clock f) b ⊥
```

**`HorizontalSum.lmonad_takes_form`**

```lean
theorem lmonad_takes_form : ¬ ∀ a : E ι α, act (clock f) a ⊥ = ⊥
```

**`HorizontalSum.clock_symm_clock`**

```lean
theorem clock_symm_clock (y : E ι α) :
    clock f (clock (fun i => (f i).symm) y) = y
```

**`HorizontalSum.sigma_surjective`**

```lean
theorem sigma_surjective : Function.Surjective (act (clock f) (⊥ : E ι α))
```

**`HorizontalSum.only_lmonad_is_traceable`**

```lean
theorem only_lmonad_is_traceable (a : E ι α) (ha : a ≠ ⊥) :
    ¬ Function.Injective (act (clock f) a)
```

#### この束でしか言えないこと

**`HorizontalSum.lmonad_acts_by_the_clock`**

```lean
theorem lmonad_acts_by_the_clock (b : E ι α) :
    act (clock f) ⊥ b = clock f b
```

**`HorizontalSum.same_axis_act`**

```lean
theorem same_axis_act (i : ι) (a b : α) :
    act (clock f) (E.axis i a) (E.axis i b) = E.axis i ((f i) b ⊔ a)
```

**`HorizontalSum.cross_axis_act`**

```lean
theorem cross_axis_act {i j : ι} (h : i ≠ j) (a b : α) :
    act (clock f) (E.axis i a) (E.axis j b) = ⊤
```

## Confinement

## この束でしか言えないこと — 閉じ込め・二種類・履歴・始まり

### 閉じ込めと直既約性

**`HorizontalSum.confinement`**

```lean
theorem confinement (f : ι → (α ≃o α)) (i : ι) (a : α) (b : E ι α) :
    act (clock f) (E.axis i a) b = ⊤ ∨
      ∃ x, act (clock f) (E.axis i a) b = E.axis i x
```

**`HorizontalSum.image_of_act`**

```lean
theorem image_of_act (f : ι → (α ≃o α)) (i : ι) (a : α) :
    Set.range (act (clock f) (E.axis i a)) =
      (fun x => (E.axis i x : E ι α)) '' {x | a ≤ x} ∪ {⊤}
```

**`HorizontalSum.lmonad_reaches_everything`**

```lean
theorem lmonad_reaches_everything (f : ι → (α ≃o α)) :
    Set.range (act (clock f) (⊥ : E ι α)) = Set.univ
```

#### 直既約 — 座標が無い

**`HorizontalSum.bot_isCompl_unique`**

```lean
theorem bot_isCompl_unique {y : E ι α} (h : IsCompl (⊥ : E ι α) y) : y = ⊤
```

**`HorizontalSum.top_isCompl_unique`**

```lean
theorem top_isCompl_unique {y : E ι α} (h : IsCompl (⊤ : E ι α) y) : y = ⊥
```

**`HorizontalSum.complement_not_unique`**

```lean
theorem complement_not_unique {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : α) :
    IsCompl (E.axis i a : E ι α) (E.axis j b) ∧
      IsCompl (E.axis i a : E ι α) (E.axis k c) ∧
      (E.axis j b : E ι α) ≠ E.axis k c
```

**`HorizontalSum.reaches_exactly_one_axis`**

```lean
theorem reaches_exactly_one_axis (f : ι → (α ≃o α)) (i : ι) (a : α) :
    {j : ι | ∃ x, ∃ b, act (clock f) (E.axis i a) b = E.axis j x} = {i}
```

**`HorizontalSum.two_kinds_of_non_lmonad`**

```lean
theorem two_kinds_of_non_lmonad (f : ι → (α ≃o α)) (i : ι) (a : α) :
    Set.range (act (clock f) (E.axis i a)) =
        (fun x => (E.axis i x : E ι α)) '' {x | a ≤ x} ∪ {⊤} ∧
      Disjoint ((fun x => (E.axis i x : E ι α)) '' {x | a ≤ x})
        ({⊤} : Set (E ι α)) ∧
      ((fun x => (E.axis i x : E ι α)) '' {x | a ≤ x}).Nonempty
```

**`HorizontalSum.harm_self_or_other`**

```lean
theorem harm_self_or_other (f : ι → (α ≃o α)) (i : ι) (a : α) (b : E ι α) :
    (∃ x, a ≤ x ∧ act (clock f) (E.axis i a) b = E.axis i x) ∨
      act (clock f) (E.axis i a) b = ⊤
```

**`HorizontalSum.harm_nothing`**

```lean
theorem harm_nothing (f : ι → (α ≃o α)) (a : E ι α) :
    act (clock f) a ⊥ = a
```

## Branch

### 多価の時計 — 錐を埋める

**`HorizontalSum.bact`**

```lean
def bact (F : Set (ι → (α ≃o α))) (a b : E ι α) : Set (E ι α)
```

**`HorizontalSum.branch_seven`**

```lean
theorem branch_seven (F : Set (ι → (α ≃o α))) (hF : F.Nonempty) (a : E ι α) :
    bact F a ⊥ = {a}
```

**`HorizontalSum.branch_six`**

```lean
theorem branch_six (F : Set (ι → (α ≃o α))) (a b : E ι α) :
    ∀ c ∈ bact F a b, a ≤ c
```

**`HorizontalSum.branch_eight`**

```lean
theorem branch_eight (F : Set (ι → (α ≃o α))) (a b : E ι α) :
    bact F a b = (fun c => c ⊔ a) '' bact F ⊥ b
```

**`HorizontalSum.branch_four`**

```lean
theorem branch_four (F : Set (ι → (α ≃o α))) (a : E ι α) {b c : E ι α}
    (h : b ≤ c) : ∀ x ∈ bact F a b, ∃ y ∈ bact F a c, x ≤ y
```

**`HorizontalSum.branch_five`**

```lean
theorem branch_five (F : Set (ι → (α ≃o α))) {a a' : E ι α} (h : a ≤ a')
    (b : E ι α) : ∀ x ∈ bact F a b, ∃ y ∈ bact F a' b, x ≤ y
```

**`HorizontalSum.branch_actor`**

```lean
theorem branch_actor (F : Set (ι → (α ≃o α))) (hF : F.Nonempty) {a a' : E ι α}
    (h : bact F a ⊥ = bact F a' ⊥) : a = a'
```

#### 錐が埋まる

**`HorizontalSum.cone_filled`**

```lean
theorem cone_filled (T : ℕ) :
    {s | ∃ k ≤ T, s = 2 * k + (T - k)} = Set.Icc T (2 * T)
```

**`HorizontalSum.cone_single`**

```lean
theorem cone_single (r T : ℕ) {s : ℕ} (h : ∃ k ≤ T, s = r * k + r * (T - k)) :
    s = r * T
```

## Trace

#### 履歴 — 戻れないこと、𝓦 が吸収すること

**`HorizontalSum.trace`**

```lean
def trace (f : ι → (α ≃o α)) (x : E ι α) (as : List (E ι α)) : E ι α
```

**`HorizontalSum.trace_nil`**

```lean
@[simp] theorem trace_nil (f : ι → (α ≃o α)) (x : E ι α) : trace f x [] = x
```

**`HorizontalSum.trace_cons`**

```lean
@[simp] theorem trace_cons (f : ι → (α ≃o α)) (x a : E ι α) (as : List (E ι α)) :
    trace f x (a :: as) = trace f (act (clock f) a x) as
```

**`HorizontalSum.world_absorbing_target`**

```lean
theorem world_absorbing_target (f : ι → (α ≃o α)) (a : E ι α) :
    act (clock f) a ⊤ = ⊤
```

**`HorizontalSum.world_absorbing_actor`**

```lean
theorem world_absorbing_actor (f : ι → (α ≃o α)) (b : E ι α) :
    act (clock f) ⊤ b = ⊤
```

**`HorizontalSum.trace_mono`**

```lean
theorem trace_mono (f : ι → (α ≃o α)) (hf : ∀ x : E ι α, x ≤ clock f x)
    (x : E ι α) (as : List (E ι α)) : x ≤ trace f x as
```

**`HorizontalSum.all_lmonad_stays`**

```lean
theorem all_lmonad_stays (f : ι → (α ≃o α)) (as : List (E ι α))
    (h : ∀ a ∈ as, a = ⊥) : trace f (⊥ : E ι α) as = ⊥
```

**`HorizontalSum.same_axis_never_world`**

```lean
theorem same_axis_never_world (f : ι → (α ≃o α)) (i : ι) (a b : α) :
    act (clock f) (E.axis i a) (E.axis i b) ≠ ⊤
```

**`HorizontalSum.trace_stays_on_axis`**

```lean
theorem trace_stays_on_axis (f : ι → (α ≃o α)) (i : ι) (a : α)
    (as : List (E ι α)) (h : ∀ b ∈ as, ∃ y, b = E.axis i y) :
    ∃ z, trace f (E.axis i a) as = E.axis i z
```

#### 始点はどこか — 「すべてに届く」から 𝓛 が出る

**`HorizontalSum.lmonad_can_become_anything`**

```lean
theorem lmonad_can_become_anything (f : ι → (α ≃o α)) (y : E ι α) :
    trace f ⊥ [y] = y
```

**`HorizontalSum.only_lmonad_can_become_anything`**

```lean
theorem only_lmonad_can_become_anything (f : ι → (α ≃o α))
    (hf : ∀ x : E ι α, x ≤ clock f x) (x : E ι α)
    (h : ∀ y : E ι α, ∃ as, trace f x as = y) : x = ⊥
```

## Coordinates

## 座標 — 束を数で書く

#### 橋 — 「まだ可能なもの」への写像

**`HorizontalSum.Phi`**

```lean
def Phi (x : E ι α) : Set (E ι α)
```

**`HorizontalSum.Phi_bot`**

```lean
theorem Phi_bot : Phi (⊥ : E ι α) = Set.univ
```

**`HorizontalSum.Phi_sup`**

```lean
theorem Phi_sup (x y : E ι α) : Phi (x ⊔ y) = Phi x ∩ Phi y
```

**`HorizontalSum.Phi_antitone`**

```lean
theorem Phi_antitone {x y : E ι α} : x ≤ y ↔ Phi y ⊆ Phi x
```

**`HorizontalSum.Phi_injective`**

```lean
theorem Phi_injective : Function.Injective (Phi : E ι α → Set (E ι α))
```

**`HorizontalSum.Phi_cross_axis`**

```lean
theorem Phi_cross_axis {i j : ι} (h : i ≠ j) (a b : α) :
    Phi (E.axis i a : E ι α) ∩ Phi (E.axis j b) = Phi (⊤ : E ι α)
```

**`HorizontalSum.Phi_inf_superset`**

```lean
theorem Phi_inf_superset (x y : E ι α) : Phi x ∪ Phi y ⊆ Phi (x ⊓ y)
```

**`HorizontalSum.Phi_inf_ne`**

```lean
theorem Phi_inf_ne {i j : ι} (h : i ≠ j) (a b : α) :
    Phi ((E.axis i a : E ι α) ⊓ E.axis j b) ≠
      Phi (E.axis i a : E ι α) ∪ Phi (E.axis j b)
```

**`HorizontalSum.Phi_clock`**

```lean
theorem Phi_clock (f : ι → (α ≃o α)) (x y : E ι α) :
    y ∈ Phi (clock f x) ↔ (clockIso f).symm y ∈ Phi x
```

#### 二つの記号を分けて繋ぐ — Mathlib の `Ici` / `Iic`

**`HorizontalSum.Phi_eq_Ici`**

```lean
theorem Phi_eq_Ici (x : E ι α) : Phi x = Set.Ici x
```

**`HorizontalSum.Down`**

```lean
def Down (x : E ι α) : Set (E ι α)
```

**`HorizontalSum.Down_top`**

```lean
theorem Down_top : Down (⊤ : E ι α) = Set.univ
```

**`HorizontalSum.Down_bot`**

```lean
theorem Down_bot : Down (⊥ : E ι α) = {⊥}
```

**`HorizontalSum.Down_inf`**

```lean
theorem Down_inf (x y : E ι α) : Down (x ⊓ y) = Down x ∩ Down y
```

**`HorizontalSum.Down_monotone`**

```lean
theorem Down_monotone {x y : E ι α} : x ≤ y ↔ Down x ⊆ Down y
```

**`HorizontalSum.Down_injective`**

```lean
theorem Down_injective : Function.Injective (Down : E ι α → Set (E ι α))
```

**`HorizontalSum.two_directions`**

```lean
theorem two_directions (x y : E ι α) :
    Phi (x ⊔ y) = Phi x ∩ Phi y ∧ Down (x ⊓ y) = Down x ∩ Down y
```

**`HorizontalSum.lmonad_world_mirror`**

```lean
theorem lmonad_world_mirror :
    Phi (⊥ : E ι α) = Set.univ ∧ Down (⊤ : E ι α) = Set.univ ∧
      Phi (⊤ : E ι α) = {⊤} ∧ Down (⊥ : E ι α) = {⊥}
```

#### 星形 — 軸ごとにまとめた座標 Ψ

**`HorizontalSum.Psi`**

```lean
def Psi (x : E ι α) (g : ι) : Set α
```

**`HorizontalSum.Psi_bot`**

```lean
theorem Psi_bot (g : ι) : Psi (⊥ : E ι α) g = Set.univ
```

**`HorizontalSum.Psi_top`**

```lean
theorem Psi_top (g : ι) : Psi (⊤ : E ι α) g = ∅
```

**`HorizontalSum.Psi_sup`**

```lean
theorem Psi_sup (x y : E ι α) (g : ι) :
    Psi (x ⊔ y) g = Psi x g ∩ Psi y g
```

**`HorizontalSum.Psi_antitone`**

```lean
theorem Psi_antitone {x y : E ι α} (h : x ≤ y) (g : ι) : Psi y g ⊆ Psi x g
```

**`HorizontalSum.Psi_axis_self`**

```lean
theorem Psi_axis_self (i : ι) (b : α) : Psi (E.axis i b : E ι α) i = {a | b ≤ a}
```

**`HorizontalSum.Psi_axis_other`**

```lean
theorem Psi_axis_other {i g : ι} (h : i ≠ g) (b : α) :
    Psi (E.axis i b : E ι α) g = ∅
```

**`HorizontalSum.star_shape`**

```lean
theorem star_shape (i : ι) (b : α) (g : ι) :
    Psi (⊥ : E ι α) g = Set.univ ∧
    Psi (E.axis i b : E ι α) g = (if i = g then {a | b ≤ a} else ∅) ∧
    Psi (⊤ : E ι α) g = ∅
```

**`HorizontalSum.Psi_le_iff`**

```lean
theorem Psi_le_iff [Nonempty α] {i j : ι} (hij : i ≠ j) {x y : E ι α} :
    (∀ g, Psi y g ⊆ Psi x g) ↔ x ≤ y
```

#### 逆も言える — 「全 1 テンソルは 𝓛 だけ」

**`HorizontalSum.Phi_eq_univ_iff`**

```lean
theorem Phi_eq_univ_iff {x : E ι α} : Phi x = Set.univ ↔ x = ⊥
```

**`HorizontalSum.Down_eq_univ_iff`**

```lean
theorem Down_eq_univ_iff {x : E ι α} : Down x = Set.univ ↔ x = ⊤
```

**`HorizontalSum.Phi_eq_singleton_iff`**

```lean
theorem Phi_eq_singleton_iff {x : E ι α} : Phi x = {x} ↔ x = ⊤
```

**`HorizontalSum.Down_eq_singleton_iff`**

```lean
theorem Down_eq_singleton_iff {x : E ι α} : Down x = {x} ↔ x = ⊥
```

## Tensor

### 座標は無限次元か — 「𝓛 と 𝓦 は ∞ 次元テンソル」を三つに割る

**`HorizontalSum.orderIso_eq_refl_of_wellFounded`**

```lean
theorem orderIso_eq_refl_of_wellFounded {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (e : β ≃o β) (x : β) : e x = x
```

**`HorizontalSum.not_wellFounded_of_nontrivial_clock`**

```lean
theorem not_wellFounded_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) : ¬ WellFoundedLT β
```

**`HorizontalSum.axis_infinite_of_nontrivial_clock`**

```lean
theorem axis_infinite_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) : Infinite β
```

**`HorizontalSum.infinite_of_nontrivial_clock`**

```lean
theorem infinite_of_nontrivial_clock {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) (i : ι) : Infinite (E ι β)
```

**`HorizontalSum.prod_mid_isCompl_unique`**

```lean
theorem prod_mid_isCompl_unique {A B : Type*} [Lattice A] [Lattice B]
    [BoundedOrder A] [BoundedOrder B] {p : A × B}
    (h : IsCompl ((⊥, ⊤) : A × B) p) : p = (⊤, ⊥)
```

**`HorizontalSum.no_product_decomposition`**

```lean
theorem no_product_decomposition
    (h3 : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k)
    {A B : Type*} [Lattice A] [Lattice B] [BoundedOrder A] [BoundedOrder B]
    (e : E ι α ≃o A × B) (hA : (⊥ : A) ≠ ⊤) (hB : (⊥ : B) ≠ ⊤) : False
```

#### 𝓦 = ∞ 次元の one-hot、𝓛 = ∞ 次元の全 1

**`HorizontalSum.chi`**

```lean
noncomputable def chi (x y : E ι α) : ℕ
```

**`HorizontalSum.chi_lmonad`**

```lean
theorem chi_lmonad (y : E ι α) : chi (⊥ : E ι α) y = 1
```

**`HorizontalSum.chi_world`**

```lean
theorem chi_world (y : E ι α) : chi (⊤ : E ι α) y = if y = ⊤ then 1 else 0
```

**`HorizontalSum.chi_support`**

```lean
theorem chi_support (x : E ι α) : {y | chi x y = 1} = Phi x
```

**`HorizontalSum.chi_lmonad_support`**

```lean
theorem chi_lmonad_support : {y : E ι α | chi (⊥ : E ι α) y = 1} = Set.univ
```

**`HorizontalSum.chi_world_support`**

```lean
theorem chi_world_support : {y : E ι α | chi (⊤ : E ι α) y = 1} = {(⊤ : E ι α)}
```

**`HorizontalSum.chi_onehot_iff`**

```lean
theorem chi_onehot_iff {x : E ι α} : {y | chi x y = 1} = {x} ↔ x = ⊤
```

**`HorizontalSum.chi_allones_iff`**

```lean
theorem chi_allones_iff {x : E ι α} : {y | chi x y = 1} = Set.univ ↔ x = ⊥
```

**`HorizontalSum.chi_antitone`**

```lean
theorem chi_antitone {x y : E ι α} (h : x ≤ y) (z : E ι α) : chi y z ≤ chi x z
```

**`HorizontalSum.chi_le_iff`**

```lean
theorem chi_le_iff {x y : E ι α} : (∀ z, chi y z ≤ chi x z) ↔ x ≤ y
```

**`HorizontalSum.chi_world_infinite_support`**

```lean
theorem chi_world_infinite_support {β : Type*} [LinearOrder β]
    (e : β ≃o β) (x : β) (h : e x ≠ x) (i : ι) :
    Infinite (E ι β) ∧ {y : E ι β | chi (⊤ : E ι β) y = 1} = {(⊤ : E ι β)}
```

#### 「∞ ならテンソルが書ける」— 添字の読み替え

**`HorizontalSum.reshape_two`**

```lean
theorem reshape_two (β : Type*) [Infinite β] : Nonempty (β ≃ β × β)
```

**`HorizontalSum.reshape_rank`**

```lean
theorem reshape_rank (β : Type*) [Infinite β] {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (β ≃ (Fin n → β))
```

**`HorizontalSum.no_reshape_of_finite`**

```lean
theorem no_reshape_of_finite (β : Type*) [Finite β] (e : β ≃ β × β) :
    Subsingleton β
```

#### 「読み替えても積のまま」で 𝓛 と 𝓦 を特徴づける

**`HorizontalSum.IsRect`**

```lean
def IsRect {A B : Type*} (S : Set (A × B)) : Prop
```

**`HorizontalSum.univ_isRect`**

```lean
theorem univ_isRect {A B : Type*} : IsRect (Set.univ : Set (A × B))
```

**`HorizontalSum.singleton_isRect`**

```lean
theorem singleton_isRect {A B : Type*} (p : A × B) : IsRect ({p} : Set (A × B))
```

**`HorizontalSum.Phi_bot_isRect`**

```lean
theorem Phi_bot_isRect {A B : Type*} (e : E ι α ≃ A × B) :
    IsRect (e '' Phi (⊥ : E ι α))
```

**`HorizontalSum.Phi_top_isRect`**

```lean
theorem Phi_top_isRect {A B : Type*} (e : E ι α ≃ A × B) :
    IsRect (e '' Phi (⊤ : E ι α))
```

**`HorizontalSum.diagonal_not_isRect`**

```lean
theorem diagonal_not_isRect :
    ¬ IsRect ({(false, false), (true, true)} : Set (Bool × Bool))
```

#### 有限テンソルによる近似 — 軸 ℤ を高さ N で切る

**`HorizontalSum.trunc`**

```lean
def trunc (m N : ℕ) : Set (E (Fin m) ℤ)
```

**`HorizontalSum.bot_mem_trunc`**

```lean
theorem bot_mem_trunc (m N : ℕ) : (⊥ : E (Fin m) ℤ) ∈ trunc m N
```

**`HorizontalSum.top_mem_trunc`**

```lean
theorem top_mem_trunc (m N : ℕ) : (⊤ : E (Fin m) ℤ) ∈ trunc m N
```

**`HorizontalSum.trunc_finite`**

```lean
theorem trunc_finite (m N : ℕ) : (trunc m N).Finite
```

**`HorizontalSum.mem_trunc_axis`**

```lean
theorem mem_trunc_axis {m N : ℕ} {i : Fin m} {a : ℤ} :
    (E.axis i a : E (Fin m) ℤ) ∈ trunc m N ↔ |a| ≤ (N : ℤ)
```

**`HorizontalSum.trunc_sup_mem`**

```lean
theorem trunc_sup_mem {m N : ℕ} {x y : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) (hy : y ∈ trunc m N) : x ⊔ y ∈ trunc m N
```

**`HorizontalSum.trunc_inf_mem`**

```lean
theorem trunc_inf_mem {m N : ℕ} {x y : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) (hy : y ∈ trunc m N) : x ⊓ y ∈ trunc m N
```

**`HorizontalSum.shift1`**

```lean
def shift1 : ℤ ≃o ℤ
```

**`HorizontalSum.no_clock_inside_trunc`**

```lean
theorem no_clock_inside_trunc (N : ℕ)
    (e : Set.Icc (-(N : ℤ)) (N : ℤ) ≃o Set.Icc (-(N : ℤ)) (N : ℤ)) (x) : e x = x
```

**`HorizontalSum.trunc_clock_step`**

```lean
theorem trunc_clock_step {m N : ℕ} {x : E (Fin m) ℤ} (hx : x ∈ trunc m N) :
    clock (fun _ : Fin m => shift1) x ∈ trunc m (N + 1)
```

**`HorizontalSum.trunc_approximates`**

```lean
theorem trunc_approximates (m N : ℕ) : ∀ (T : ℕ) {x : E (Fin m) ℤ},
    x ∈ trunc m N → (clock (fun _ : Fin m => shift1))^[T] x ∈ trunc m (N + T)
```

**`HorizontalSum.trunc_union`**

```lean
theorem trunc_union (m : ℕ) : ⋃ N, trunc m N = Set.univ
```

## Folding

#### 畳み直せる条件 — 値づけが加法的であること

**`HorizontalSum.Foldable`**

```lean
def Foldable {M : Type*} [AddCommGroup M] (val : ℤ → M) : Prop
```

**`HorizontalSum.foldable_of_smul`**

```lean
theorem foldable_of_smul {M : Type*} [AddCommGroup M] (v : M) :
    Foldable (fun k : ℤ => k • v)
```

**`HorizontalSum.smul_of_foldable`**

```lean
theorem smul_of_foldable {M : Type*} [AddCommGroup M] {val : ℤ → M}
    (h : Foldable val) (k : ℤ) : val k = k • val 1
```

**`HorizontalSum.foldable_iff_smul`**

```lean
theorem foldable_iff_smul {M : Type*} [AddCommGroup M] (val : ℤ → M) :
    Foldable val ↔ ∀ k : ℤ, val k = k • val 1
```

**`HorizontalSum.FoldableMul`**

```lean
def FoldableMul {G : Type*} [CommGroup G] (val : ℤ → G) : Prop
```

**`HorizontalSum.foldableMul_of_zpow`**

```lean
theorem foldableMul_of_zpow {G : Type*} [CommGroup G] (v : G) :
    FoldableMul (fun k : ℤ => v ^ k)
```

**`HorizontalSum.zpow_of_foldableMul`**

```lean
theorem zpow_of_foldableMul {G : Type*} [CommGroup G] {val : ℤ → G}
    (h : FoldableMul val) (k : ℤ) : val k = val 1 ^ k
```

**`HorizontalSum.additive_and_multiplicative_are_dual`**

```lean
theorem additive_and_multiplicative_are_dual {M G : Type*}
    [AddCommGroup M] [CommGroup G] (v : M) (w : G) :
    Foldable (fun k : ℤ => k • v) ∧ FoldableMul (fun k : ℤ => w ^ k)
```

**`HorizontalSum.cos_not_foldable`**

```lean
theorem cos_not_foldable : ¬ Foldable (fun k : ℤ => Real.cos k)
```

**`HorizontalSum.mixing_needs_arithmetic_steps`**

```lean
theorem mixing_needs_arithmetic_steps {M : Type*} [AddCommGroup M] (v : M) :
    Foldable (fun k : ℤ => k • v) ∧ ¬ Foldable (fun k : ℤ => Real.cos k)
```

#### 経路の重ね合わせ — 成り立つのは名札が可換なときだけ

**`HorizontalSum.endpoint`**

```lean
def endpoint [Monoid G] (start : G) (l : List G) : G
```

**`HorizontalSum.endpoint_nil`**

```lean
@[simp] theorem endpoint_nil [Monoid G] (start : G) : endpoint start [] = start
```

**`HorizontalSum.endpoint_perm`**

```lean
theorem endpoint_perm [CommMonoid G] (start : G) {l₁ l₂ : List G}
    (h : l₁.Perm l₂) : endpoint start l₁ = endpoint start l₂
```

**`HorizontalSum.endpoint_zip`**

```lean
theorem endpoint_zip [CommMonoid G] (s₁ s₂ : G) : ∀ (l₁ l₂ : List G),
    l₁.length = l₂.length →
    endpoint s₁ l₁ * endpoint s₂ l₂ = endpoint (s₁ * s₂) (List.zipWith (· * ·) l₁ l₂)
  | [], [], _ => by simp
  | a :: as, b :: bs, h => by
      have hl : as.length = bs.length
```

**`HorizontalSum.endpoint_not_perm_of_noncomm`**

```lean
theorem endpoint_not_perm_of_noncomm :
    ∃ (g h : QuaternionGroup 2), endpoint 1 [g, h] ≠ endpoint 1 [h, g]
```

**`HorizontalSum.superposition_iff_commutative`**

```lean
theorem superposition_iff_commutative :
    (∀ (s : Multiplicative ℤ) (l₁ l₂ : List (Multiplicative ℤ)),
        l₁.Perm l₂ → endpoint s l₁ = endpoint s l₂) ∧
      (∃ (g h : QuaternionGroup 2), endpoint 1 [g, h] ≠ endpoint 1 [h, g])
```

#### 軸の内側には足し算がある — 時計の合成

**`HorizontalSum.shiftBy`**

```lean
def shiftBy (k : ℤ) : ℤ ≃o ℤ
```

**`HorizontalSum.shiftBy_apply`**

```lean
@[simp] theorem shiftBy_apply (k a : ℤ) : shiftBy k a = a + k
```

**`HorizontalSum.shiftBy_comp`**

```lean
theorem shiftBy_comp (j k a : ℤ) : shiftBy j (shiftBy k a) = shiftBy (j + k) a
```

**`HorizontalSum.shift1_is_shiftBy_one`**

```lean
theorem shift1_is_shiftBy_one (a : ℤ) : shift1 a = shiftBy 1 a
```

**`HorizontalSum.clock_shiftBy_comp`**

```lean
theorem clock_shiftBy_comp (j k : ι → ℤ) (x : E ι ℤ) :
    clock (fun i => shiftBy (j i)) (clock (fun i => shiftBy (k i)) x)
      = clock (fun i => shiftBy (j i + k i)) x
```

**`HorizontalSum.clock_iterate_shiftBy`**

```lean
theorem clock_iterate_shiftBy (k : ℤ) (T : ℕ) (x : E ι ℤ) :
    (clock (fun _ : ι => shiftBy k))^[T] x = clock (fun _ : ι => shiftBy (T * k)) x
```

**`HorizontalSum.mixing_identity`**

```lean
theorem mixing_identity (j k : ℤ) (i : ι) (a : ℤ) :
    clock (fun _ : ι => shiftBy j) (clock (fun _ : ι => shiftBy k) (E.axis i a))
      = E.axis i (a + (j + k))
```

**`HorizontalSum.addition_is_inside_the_axis`**

```lean
theorem addition_is_inside_the_axis {i j : ι} (hij : i ≠ j) (a b : ℤ) :
    (E.axis i a : E ι ℤ) ⊔ E.axis j b = ⊤ ∧
      clock (fun _ : ι => shiftBy b) (E.axis i a : E ι ℤ) = E.axis i (a + b)
```

## Semidirect

#### 作用を無限次元の行列として書く — 置換 × 対角

**`HorizontalSum.clock_sup`**

```lean
theorem clock_sup (f : ι → (α ≃o α)) (x y : E ι α) :
    clock f (x ⊔ y) = clock f x ⊔ clock f y
```

**`HorizontalSum.Phi_act`**

```lean
theorem Phi_act (f : ι → (α ≃o α)) (A B : E ι α) :
    Phi (act (clock f) A B) = (clockIso f) '' Phi B ∩ Phi A
```

**`HorizontalSum.Phi_act_twice`**

```lean
theorem Phi_act_twice (f : ι → (α ≃o α)) (A C B : E ι α) :
    Phi (act (clock f) A (act (clock f) C B))
      = (clockIso f) '' ((clockIso f) '' Phi B ∩ Phi C) ∩ Phi A
```

**`HorizontalSum.act_comp_is_affine`**

```lean
theorem act_comp_is_affine (f : ι → (α ≃o α)) (A C B : E ι α) :
    act (clock f) A (act (clock f) C B)
      = clock f (clock f B) ⊔ (clock f C ⊔ A)
```

#### 作用の正体は半直積モノイド — `E ⋊[σ] ℕ`

**`HorizontalSum.clockPow`**

```lean
def clockPow (f : ι → (α ≃o α)) : ℕ → E ι α → E ι α
  | 0, x => x
  | (n + 1), x => clock f (clockPow f n x)
```

**`HorizontalSum.clockPow_zero`**

```lean
@[simp] theorem clockPow_zero (f : ι → (α ≃o α)) (x : E ι α) :
    clockPow f 0 x = x
```

**`HorizontalSum.clockPow_succ`**

```lean
theorem clockPow_succ (f : ι → (α ≃o α)) (n : ℕ) (x : E ι α) :
    clockPow f (n + 1) x = clock f (clockPow f n x)
```

**`HorizontalSum.clockPow_bot`**

```lean
theorem clockPow_bot (f : ι → (α ≃o α)) (n : ℕ) :
    clockPow f n (⊥ : E ι α) = ⊥
```

**`HorizontalSum.clockPow_sup`**

```lean
theorem clockPow_sup (f : ι → (α ≃o α)) (n : ℕ) (x y : E ι α) :
    clockPow f n (x ⊔ y) = clockPow f n x ⊔ clockPow f n y
```

**`HorizontalSum.clockPow_add`**

```lean
theorem clockPow_add (f : ι → (α ≃o α)) (m n : ℕ) (x : E ι α) :
    clockPow f (m + n) x = clockPow f m (clockPow f n x)
```

**`HorizontalSum.Semi`**

```lean
structure Semi (f : ι → (α ≃o α)) where
  left : E ι α
  right : ℕ
```

**`HorizontalSum.Semi.:`**

```lean
instance : Mul (Semi f) where
  mul a b
```

**`HorizontalSum.Semi.:`**

```lean
instance : One (Semi f) where
  one
```

**`HorizontalSum.Semi.mul_left`**

```lean
@[simp] theorem mul_left (a b : Semi f) :
    (a * b).left = clockPow f a.right b.left ⊔ a.left
```

**`HorizontalSum.Semi.mul_right`**

```lean
@[simp] theorem mul_right (a b : Semi f) :
    (a * b).right = a.right + b.right
```

**`HorizontalSum.Semi.one_left`**

```lean
@[simp] theorem one_left : (1 : Semi f).left = ⊥
```

**`HorizontalSum.Semi.one_right`**

```lean
@[simp] theorem one_right : (1 : Semi f).right = 0
```

**`HorizontalSum.Semi.ext'`**

```lean
theorem ext' {a b : Semi f} (hl : a.left = b.left) (hr : a.right = b.right) :
    a = b
```

**`HorizontalSum.Semi.:`**

```lean
instance : Monoid (Semi f) where
  mul_assoc a b c
```

**`HorizontalSum.Semi.:`**

```lean
instance : MulAction (Semi f) (E ι α) where
  smul p x
```

**`HorizontalSum.Semi.smul_def`**

```lean
@[simp] theorem smul_def (p : Semi f) (x : E ι α) :
    p • x = clockPow f p.right x ⊔ p.left
```

**`HorizontalSum.Semi.:`**

```lean
instance : Coe (E ι α) (Semi f) where
  coe A
```

**`HorizontalSum.Semi.coe_left`**

```lean
@[simp] theorem coe_left (A : E ι α) : ((A : Semi f)).left = A
```

**`HorizontalSum.Semi.coe_right`**

```lean
@[simp] theorem coe_right (A : E ι α) : ((A : Semi f)).right = 1
```

**`HorizontalSum.Semi.mul_left_of_trivial`**

```lean
theorem mul_left_of_trivial (a b : Semi (fun _ : ι => OrderIso.refl α)) :
    (a * b).left = b.left ⊔ a.left
```

**`HorizontalSum.Semi.is_direct_product_when_trivial`**

```lean
theorem is_direct_product_when_trivial
    (a b : Semi (fun _ : ι => OrderIso.refl α)) :
    (a * b).left = b.left ⊔ a.left ∧ (a * b).right = a.right + b.right
```

**`HorizontalSum.act_eq_smul`**

```lean
theorem act_eq_smul (f : ι → (α ≃o α)) (A B : E ι α) :
    act (clock f) A B = (A : Semi f) • B
```

**`HorizontalSum.act_eq_mul_left`**

```lean
theorem act_eq_mul_left (f : ι → (α ≃o α)) (A B : E ι α) :
    act (clock f) A B = ((A : Semi f) * (B : Semi f)).left
```

**`HorizontalSum.mul_right_counts`**

```lean
theorem mul_right_counts (f : ι → (α ≃o α)) (A B : E ι α) :
    ((A : Semi f) * (B : Semi f)).right = 2
```

**`HorizontalSum.mul_three`**

```lean
theorem mul_three (f : ι → (α ≃o α)) (A B C : E ι α) :
    ((A : Semi f) * (B : Semi f) * (C : Semi f)).left
      = clockPow f 2 C ⊔ (clock f B ⊔ A) ∧
    ((A : Semi f) * (B : Semi f) * (C : Semi f)).right = 3
```

#### 二つの入れ方 — `inl`（刻む）と `inr`（進める）

**`HorizontalSum.Semi.inl`**

```lean
def inl (A : E ι α) : Semi f
```

**`HorizontalSum.Semi.inr`**

```lean
def inr (k : ℕ) : Semi f
```

**`HorizontalSum.Semi.inl_left`**

```lean
@[simp] theorem inl_left (A : E ι α) : (inl A : Semi f).left = A
```

**`HorizontalSum.Semi.inl_right`**

```lean
@[simp] theorem inl_right (A : E ι α) : (inl A : Semi f).right = 0
```

**`HorizontalSum.Semi.inr_left`**

```lean
@[simp] theorem inr_left (k : ℕ) : (inr k : Semi f).left = ⊥
```

**`HorizontalSum.Semi.inr_right`**

```lean
@[simp] theorem inr_right (k : ℕ) : (inr k : Semi f).right = k
```

**`HorizontalSum.Semi.inl_mul`**

```lean
theorem inl_mul (A B : E ι α) :
    (inl A : Semi f) * inl B = inl (B ⊔ A)
```

**`HorizontalSum.Semi.inr_mul`**

```lean
theorem inr_mul (j k : ℕ) : (inr j : Semi f) * inr k = inr (j + k)
```

**`HorizontalSum.Semi.inl_bot`**

```lean
@[simp] theorem inl_bot : (inl ⊥ : Semi f) = 1
```

**`HorizontalSum.Semi.inr_zero`**

```lean
@[simp] theorem inr_zero : (inr 0 : Semi f) = 1
```

**`HorizontalSum.Semi.inl_mul_inr`**

```lean
theorem inl_mul_inr (A : E ι α) (k : ℕ) :
    (inl A : Semi f) * inr k = ⟨A, k⟩
```

**`HorizontalSum.Semi.coe_eq_inl_mul_inr`**

```lean
theorem coe_eq_inl_mul_inr (A : E ι α) :
    (A : Semi f) = inl A * inr 1
```

**`HorizontalSum.Semi.inr_mul_inl`**

```lean
theorem inr_mul_inl (A : E ι α) (k : ℕ) :
    (inr k : Semi f) * inl A = ⟨clockPow f k A, k⟩
```

**`HorizontalSum.Semi.inr_inl_comm`**

```lean
theorem inr_inl_comm (A : E ι α) (k : ℕ) :
    (inr k : Semi f) * inl A = inl (clockPow f k A) * inr k
```

#### 有限テンソルによる近似 — 作用の版

**`HorizontalSum.trunc_mono`**

```lean
theorem trunc_mono {m N N' : ℕ} (h : N ≤ N') {x : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) : x ∈ trunc m N'
```

**`HorizontalSum.trunc_act_step`**

```lean
theorem trunc_act_step {m N : ℕ} {a b : E (Fin m) ℤ}
    (ha : a ∈ trunc m N) (hb : b ∈ trunc m N) :
    act (clock (fun _ : Fin m => shift1)) a b ∈ trunc m (N + 1)
```

**`HorizontalSum.trunc_act_approximates`**

```lean
theorem trunc_act_approximates :
    ∀ (T m N : ℕ) (as : List (E (Fin m) ℤ)), as.length = T →
      (∀ a ∈ as, a ∈ trunc m N) →
      ∀ {b : E (Fin m) ℤ}, b ∈ trunc m N →
        as.foldl (act (clock (fun _ : Fin m => shift1))) b ∈ trunc m (N + T)
```

## Bridge

#### 既存の道具との対応（一括）

**`HorizontalSum.clockPow_eq_iterate`**

```lean
theorem clockPow_eq_iterate (f : ι → (α ≃o α)) (n : ℕ) (x : E ι α) :
    clockPow f n x = (clock f)^[n] x
```

**`HorizontalSum.chi_eq_indicator`**

```lean
theorem chi_eq_indicator (x y : E ι α) :
    chi x y = (Set.Ici x).indicator (fun _ => (1 : ℕ)) y
```

**`HorizontalSum.pathAmp_eq_map_prod`**

```lean
theorem pathAmp_eq_map_prod {M : Type*} [Monoid M] (f : G → M) (l : List G) :
    pathAmp f l = (l.map f).prod
```

**`HorizontalSum.endpoint_eq_prod_mul`**

```lean
theorem endpoint_eq_prod_mul {G : Type*} [Monoid G] (start : G) (l : List G) :
    endpoint start l = (l.map id).prod * start
```

**`HorizontalSum.trunc_axis_mem`**

```lean
theorem trunc_axis_mem (m N : ℕ) (i : Fin m) (a : ℤ) :
    (E.axis i a : E (Fin m) ℤ) ∈ trunc m N ↔ a ∈ Set.Icc (-(N : ℤ)) (N : ℤ)
```

**`HorizontalSum.Phi_Down_are_intervals`**

```lean
theorem Phi_Down_are_intervals (x : E ι α) :
    Phi x = Set.Ici x ∧ Down x = Set.Iic x
```

**`HorizontalSum.isRect_iff_prod`**

```lean
theorem isRect_iff_prod {A B : Type*} (S : Set (A × B)) :
    IsRect S ↔ ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S
```

**`HorizontalSum.shift_are_addRight`**

```lean
theorem shift_are_addRight (k a : ℤ) :
    shift1 a = a + 1 ∧ shiftBy k a = a + k
```

**`HorizontalSum.lrot_rrot_are_translations`**

```lean
theorem lrot_rrot_are_translations {G : Type*} [Group G] [DecidableEq G]
    (g k : G) (a : α) :
    lrot g (E.axis k a : E G α) = E.axis (Equiv.mulLeft g k) a ∧
      rrot g (E.axis k a : E G α) = E.axis (Equiv.mulRight g k) a
```

#### 行列と四元数 — Mathlib の `ℍ[R]` との対応

**`HorizontalSum.qmat_is_left_mul`**

```lean
theorem qmat_is_left_mul (a b c d : R) :
    qmat a b c d = Matrix.of ![![a, -b, -c, -d],
                               ![b,  a, -d,  c],
                               ![c,  d,  a, -b],
                               ![d, -c,  b,  a]]
```

**`HorizontalSum.cmat_is_left_mul`**

```lean
theorem cmat_is_left_mul (a b : R) :
    cmat a b = Matrix.of ![![a, -b], ![b, a]]
```

**`HorizontalSum.qmat_mul_regular`**

```lean
theorem qmat_mul_regular (a b c d a' b' c' d' : R) :
    qmat a b c d * qmat a' b' c' d'
      = qmat (a*a' - b*b' - c*c' - d*d')
             (a*b' + b*a' + c*d' - d*c')
             (a*c' - b*d' + c*a' + d*b')
             (a*d' + b*c' - c*b' + d*a')
```

**`HorizontalSum.cmat_mul`**

```lean
theorem cmat_mul (a b a' b' : R) :
    cmat a b * cmat a' b' = cmat (a*a' - b*b') (a*b' + b*a')
```

**`HorizontalSum.quad_shift_is_cyclic`**

```lean
theorem quad_shift_is_cyclic (x y : R) :
    shift (quad x y) = quad y (-x)
```

**`HorizontalSum.shift_pow_four`**

```lean
theorem shift_pow_four (v : Fin 4 → R) : shift (shift (shift (shift v))) = v
```

#### 名札の入れ替えと時計 — `Equiv` の標準構成

**`HorizontalSum.ofAxisEquiv_is_relabel`**

```lean
theorem ofAxisEquiv_is_relabel (e : ι ≃ ι) (i : ι) (a : α) :
    ofAxisEquiv e (E.axis i a : E ι α) = E.axis (e i) a
```

**`HorizontalSum.clock_is_componentwise`**

```lean
theorem clock_is_componentwise (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (E.axis i a : E ι α) = E.axis i (f i a)
```

**`HorizontalSum.clock_relabel_not_comm`**

```lean
theorem clock_relabel_not_comm (e : ι ≃ ι) (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (ofAxisEquiv e (E.axis i a : E ι α)) = E.axis (e i) (f (e i) a) ∧
      ofAxisEquiv e (clock f (E.axis i a : E ι α)) = E.axis (e i) (f i a)
```

## Family

## 水平和 — Mathlib に無い構成を一般形で

**`HorizontalSum.Family.T`**

```lean
inductive T (ι : Type u) (P : ι → Type v) where
  | bot : T ι P
  | mid : ∀ i, P i → T ι P
  | top : T ι P
```

**`HorizontalSum.Family.le`**

```lean
def le : T ι P → T ι P → Prop
  | .bot, _ => True
  | .mid _ _, .bot => False
  | .mid i a, .mid j b => ∃ h : i = j, (h ▸ a) ≤ b
  | .mid _ _, .top => True
  | .top, .bot => False
  | .top, .mid _ _ => False
  | .top, .top => True
```

**`HorizontalSum.Semi.:`**

```lean
instance : LE (T ι P)
```

**`HorizontalSum.Family.le_refl'`**

```lean
theorem le_refl' (x : T ι P) : le x x
```

**`HorizontalSum.Family.le_trans'`**

```lean
theorem le_trans' {x y z : T ι P} (h₁ : le x y) (h₂ : le y z) : le x z
```

**`HorizontalSum.Family.le_antisymm'`**

```lean
theorem le_antisymm' {x y : T ι P} (h₁ : le x y) (h₂ : le y x) : x = y
```

**`HorizontalSum.Semi.:`**

```lean
instance : PartialOrder (T ι P) where
  le
```

**`HorizontalSum.Semi.:`**

```lean
instance : OrderBot (T ι P) where
  bot
```

**`HorizontalSum.Semi.:`**

```lean
instance : OrderTop (T ι P) where
  top
```

**`HorizontalSum.Semi.:`**

```lean
instance : BoundedOrder (T ι P)
```

**`HorizontalSum.Family.mid_le_mid_iff`**

```lean
theorem mid_le_mid_iff {i j : ι} (a : P i) (b : P j) :
    (T.mid i a : T ι P) ≤ T.mid j b ↔ ∃ h : i = j, (h ▸ a) ≤ b
```

**`HorizontalSum.Family.mid_incomparable`**

```lean
theorem mid_incomparable {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    ¬ ((T.mid i a : T ι P) ≤ T.mid j b)
```

**`HorizontalSum.Family.mid_le_mid`**

```lean
theorem mid_le_mid {i : ι} {a b : P i} :
    (T.mid i a : T ι P) ≤ T.mid i b ↔ a ≤ b
```

**`HorizontalSum.Family.mid_le_iff`**

```lean
theorem mid_le_iff {i : ι} {a : P i} {y : T ι P} :
    (T.mid i a : T ι P) ≤ y ↔ y = ⊤ ∨ ∃ c : P i, y = T.mid i c ∧ a ≤ c
```

**`HorizontalSum.Family.le_mid_iff`**

```lean
theorem le_mid_iff {i : ι} {c : P i} {x : T ι P} :
    x ≤ (T.mid i c : T ι P) ↔ x = ⊥ ∨ ∃ a : P i, x = T.mid i a ∧ a ≤ c
```

### 束になる条件 — 十分だが必要でない

**`HorizontalSum.Family.mid_isLUB_iff`**

```lean
theorem mid_isLUB_iff (i : ι) (a b c : P i) :
    IsLUB {(T.mid i a : T ι P), T.mid i b} (T.mid i c) ↔ IsLUB {a, b} c
```

**`HorizontalSum.Family.cross_isLUB`**

```lean
theorem cross_isLUB {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    IsLUB {(T.mid i a : T ι P), T.mid j b} ⊤
```

**`HorizontalSum.Family.cross_isGLB`**

```lean
theorem cross_isGLB {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    IsGLB {(T.mid i a : T ι P), T.mid j b} ⊥
```

### 反例 — 「各成分が束」は必要でない

**`HorizontalSum.Family.Two`**

```lean
inductive Two where
  | a : Two
  | b : Two
  deriving DecidableEq
```

**`HorizontalSum.Semi.:`**

```lean
instance : PartialOrder Two where
  le x y
```

**`HorizontalSum.Family.two_not_lattice`**

```lean
theorem two_not_lattice : ¬ ∃ c : Two, IsLUB {Two.a, Two.b} c
```

**`HorizontalSum.Family.two_hsum_has_lub`**

```lean
theorem two_hsum_has_lub :
    IsLUB {(T.mid () Two.a : T Unit fun _ => Two), T.mid () Two.b} ⊤
```

**`HorizontalSum.Family.sup`**

```lean
def sup : T ι P → T ι P → T ι P
  | .bot, y => y
  | .mid i a, .bot => .mid i a
  | .mid i a, .mid j b => if h : i = j then .mid j ((h ▸ a) ⊔ b) else .top
  | .mid _ _, .top => .top
  | .top, _ => .top
```

**`HorizontalSum.Family.inf`**

```lean
def inf : T ι P → T ι P → T ι P
  | .bot, _ => .bot
  | .mid _ _, .bot => .bot
  | .mid i a, .mid j b => if h : i = j then .mid j ((h ▸ a) ⊓ b) else .bot
  | .mid i a, .top => .mid i a
  | .top, y => y
```

**`HorizontalSum.Family.sup_same`**

```lean
theorem sup_same (i : ι) (a b : P i) :
    sup (T.mid i a) (T.mid i b) = T.mid i (a ⊔ b)
```

**`HorizontalSum.Family.sup_diff`**

```lean
theorem sup_diff {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    sup (T.mid i a) (T.mid j b) = T.top
```

**`HorizontalSum.Family.inf_same`**

```lean
theorem inf_same (i : ι) (a b : P i) :
    inf (T.mid i a) (T.mid i b) = T.mid i (a ⊓ b)
```

**`HorizontalSum.Family.inf_diff`**

```lean
theorem inf_diff {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    inf (T.mid i a) (T.mid j b) = T.bot
```

**`HorizontalSum.Family.le_sup_left'`**

```lean
theorem le_sup_left' (x y : T ι P) : le x (sup x y)
```

**`HorizontalSum.Family.le_sup_right'`**

```lean
theorem le_sup_right' (x y : T ι P) : le y (sup x y)
```

**`HorizontalSum.Family.sup_le'`**

```lean
theorem sup_le' {x y z : T ι P} (h₁ : le x z) (h₂ : le y z) : le (sup x y) z
```

**`HorizontalSum.Family.inf_le_left'`**

```lean
theorem inf_le_left' (x y : T ι P) : le (inf x y) x
```

**`HorizontalSum.Family.inf_le_right'`**

```lean
theorem inf_le_right' (x y : T ι P) : le (inf x y) y
```

**`HorizontalSum.Family.le_inf'`**

```lean
theorem le_inf' {x y z : T ι P} (h₁ : le x y) (h₂ : le x z) : le x (inf y z)
```

**`HorizontalSum.instLattice`**

```lean
instance instLattice : Lattice (T ι P) where
  sup
```

**`HorizontalSum.Family.sup_cross`**

```lean
theorem sup_cross {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    (T.mid i a : T ι P) ⊔ T.mid j b = ⊤
```

**`HorizontalSum.Family.inf_cross`**

```lean
theorem inf_cross {i j : ι} (h : i ≠ j) (a : P i) (b : P j) :
    (T.mid i a : T ι P) ⊓ T.mid j b = ⊥
```

**`HorizontalSum.Family.sup_inside`**

```lean
theorem sup_inside (i : ι) (a b : P i) :
    (T.mid i a : T ι P) ⊔ T.mid i b = T.mid i (a ⊔ b)
```

**`HorizontalSum.Family.inf_inside`**

```lean
theorem inf_inside (i : ι) (a b : P i) :
    (T.mid i a : T ι P) ⊓ T.mid i b = T.mid i (a ⊓ b)
```

### `E ι α` は水平和の特殊形

**`HorizontalSum.Family.ofE`**

```lean
def ofE : E ι α → T ι (fun _ => α)
  | .lmonad => .bot
  | .axis i a => .mid i a
  | .world => .top
```

**`HorizontalSum.Family.toE`**

```lean
def toE : T ι (fun _ => α) → E ι α
  | .bot => .lmonad
  | .mid i a => .axis i a
  | .top => .world
```

**`HorizontalSum.Family.toE_ofE`**

```lean
theorem toE_ofE (x : E ι α) : toE (ofE x) = x
```

**`HorizontalSum.Family.ofE_toE`**

```lean
theorem ofE_toE (x : T ι (fun _ => α)) : ofE (toE x) = x
```

**`HorizontalSum.Family.ofE_le_iff`**

```lean
theorem ofE_le_iff (x y : E ι α) : ofE x ≤ ofE y ↔ x ≤ y
```

**`HorizontalSum.Family.eEquiv`**

```lean
def eEquiv : E ι α ≃o T ι (fun _ => α) where
  toFun
```

**`HorizontalSum.Family.eEquiv_lmonad`**

```lean
@[simp] theorem eEquiv_lmonad : eEquiv (E.lmonad : E ι α) = ⊥
```

**`HorizontalSum.Family.eEquiv_axis`**

```lean
@[simp] theorem eEquiv_axis (i : ι) (a : α) :
    eEquiv (E.axis i a : E ι α) = T.mid i a
```

**`HorizontalSum.Family.eEquiv_world`**

```lean
@[simp] theorem eEquiv_world : eEquiv (E.world : E ι α) = ⊤
```

**`HorizontalSum.Family.eEquiv_sup`**

```lean
theorem eEquiv_sup (x y : E ι α) : eEquiv (x ⊔ y) = eEquiv x ⊔ eEquiv y
```

**`HorizontalSum.Family.eEquiv_inf`**

```lean
theorem eEquiv_inf (x y : E ι α) : eEquiv (x ⊓ y) = eEquiv x ⊓ eEquiv y
```

## Cost

## 代償 — この束が支払うもの

### 代償 — 分配でもモジュラでもない

**`HorizontalSum.not_distributive`**

```lean
theorem not_distributive {i j : ι} (hij : i ≠ j) {a c : α} (hac : ¬ a ≤ c) (b : α) :
    (E.axis i a : E ι α) ⊓ (E.axis j b ⊔ E.axis i c) ≠
      ((E.axis i a : E ι α) ⊓ E.axis j b) ⊔ ((E.axis i a : E ι α) ⊓ E.axis i c)
```

**`HorizontalSum.not_modular`**

```lean
theorem not_modular {i j : ι} (hij : i ≠ j) {a c : α} (hac : a ≤ c) (hne : a ≠ c)
    (b : α) :
    (E.axis i a : E ι α) ⊔ ((E.axis j b : E ι α) ⊓ E.axis i c) ≠
      ((E.axis i a : E ι α) ⊔ E.axis j b) ⊓ E.axis i c
```

## Bounded

## 文献の定義をそのまま書く — 有界半順序の族の水平和

**`HorizontalSum.IsHorizontalSum`**

```lean
structure IsHorizontalSum {ι : Type u} (P : ι → Type v) [∀ i, Preorder (P i)]
    (S : Type w) [PartialOrder S] [BoundedOrder S]
    (emb : ∀ i, P i → S) : Prop where
  ne_bot : ∀ i a, emb i a ≠ ⊥
  ne_top : ∀ i a, emb i a ≠ ⊤
  mono : ∀ i a b, emb i a ≤ emb i b ↔ a ≤ b
  cross : ∀ ⦃i j⦄, i ≠ j → ∀ a b, ¬ (emb i a ≤ emb j b)
  covers : ∀ s : S, s = ⊥ ∨ s = ⊤ ∨ ∃ i a, s = emb i a
  bot_ne_top : (⊥ : S) ≠ ⊤
```

**`HorizontalSum.IsHorizontalSum.injective`**

```lean
theorem injective (h : IsHorizontalSum P S emb) (i : ι) :
    Function.Injective (emb i)
```

**`HorizontalSum.IsHorizontalSum.ne_of_ne_index`**

```lean
theorem ne_of_ne_index (h : IsHorizontalSum P S emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ≠ emb j b
```

**`HorizontalSum.IsHorizontalSum.emb_eq_transport`**

```lean
theorem emb_eq_transport {S' : Type w} [PartialOrder S'] [BoundedOrder S']
    {emb' : ∀ i, P i → S'} (h : IsHorizontalSum P S emb)
    (h' : IsHorizontalSum P S' emb') {i j : ι} {a : P i} {b : P j}
    (e : emb i a = emb j b) : emb' i a = emb' j b
```

### `Family.T` は水平和である

**`HorizontalSum.Family.mid_ne_bot`**

```lean
@[simp] theorem mid_ne_bot (i : ι) (a : P i) : (T.mid i a : T ι P) ≠ ⊥
```

**`HorizontalSum.Family.mid_ne_top`**

```lean
@[simp] theorem mid_ne_top (i : ι) (a : P i) : (T.mid i a : T ι P) ≠ ⊤
```

**`HorizontalSum.Family.mid_isHorizontalSum`**

```lean
theorem mid_isHorizontalSum : IsHorizontalSum P (T ι P) T.mid where
  ne_bot
```

### 同型を除いて一意

**`HorizontalSum.IsHorizontalSum.transfer`**

```lean
noncomputable def transfer (h : IsHorizontalSum P S emb)
    (h' : IsHorizontalSum P S' emb') (s : S) : S'
```

**`HorizontalSum.IsHorizontalSum.transfer_bot`**

```lean
theorem transfer_bot (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb') :
    transfer h h' ⊥ = ⊥
```

**`HorizontalSum.IsHorizontalSum.transfer_top`**

```lean
theorem transfer_top (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb') :
    transfer h h' ⊤ = ⊤
```

**`HorizontalSum.IsHorizontalSum.transfer_mid`**

```lean
theorem transfer_mid (h : IsHorizontalSum P S emb) (h' : IsHorizontalSum P S' emb')
    (i : ι) (a : P i) : transfer h h' (emb i a) = emb' i a
```

### いつ水平和になるか — 必要条件を内在的に書く

**`HorizontalSum.IsHorizontalSum.same_component_of_comparable`**

```lean
theorem same_component_of_comparable (h : IsHorizontalSum P S emb)
    {i j : ι} {a : P i} {b : P j}
    (hc : emb i a ≤ emb j b ∨ emb j b ≤ emb i a) : i = j
```

**`HorizontalSum.IsHorizontalSum.not_le_bot`**

```lean
theorem not_le_bot (h : IsHorizontalSum P S emb) (i : ι) (a : P i) :
    ¬ (emb i a ≤ ⊥)
```

**`HorizontalSum.IsHorizontalSum.not_top_le`**

```lean
theorem not_top_le (h : IsHorizontalSum P S emb) (i : ι) (a : P i) :
    ¬ ((⊤ : S) ≤ emb i a)
```

**`HorizontalSum.IsHorizontalSum.cross_sup_top`**

```lean
theorem cross_sup_top (h : IsHorizontalSum P L emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ⊔ emb j b = ⊤
```

**`HorizontalSum.IsHorizontalSum.cross_inf_bot`**

```lean
theorem cross_inf_bot (h : IsHorizontalSum P L emb) {i j : ι} (hij : i ≠ j)
    (a : P i) (b : P j) : emb i a ⊓ emb j b = ⊥
```

### いつ半直積が可換になるか — 捻れが自明なときだけ

**`HorizontalSum.clockPow_id`**

```lean
theorem clockPow_id {f : ι → (α ≃o α)} (h : ∀ A : E ι α, clock f A = A) (k : ℕ) :
    ∀ A : E ι α, clockPow f k A = A
```

**`HorizontalSum.semi_comm_iff`**

```lean
theorem semi_comm_iff (f : ι → (α ≃o α)) :
    (∀ p q : Semi f, p * q = q * p) ↔ ∀ A : E ι α, clock f A = A
```

**`HorizontalSum.semi_not_comm_of_clock_ne`**

```lean
theorem semi_not_comm_of_clock_ne (f : ι → (α ≃o α)) (A : E ι α)
    (h : clock f A ≠ A) : ¬ (∀ p q : Semi f, p * q = q * p)
```

