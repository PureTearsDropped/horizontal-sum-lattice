import HorizontalSum.Bounded

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v w

namespace HorizontalSum

/-! # モノイドの半直積 — 一般形を書いて `Semi` をその実例にする

Mathlib の `SemidirectProduct` は `[Group N] [Group G]` と
`φ : G →* MulAut N` を要求する。**モノイド版は無い。**

代数では既知の構成である（Zappa–Szép 積などの名で標準的）。ここで足して
いるのは Lean での形式化だけで、数学的な新しさは主張しない。

    N        モノイド
    G        モノイド
    φ        `G →* Monoid.End N`（自己**同型**でなく自己準同型でよい）
    N ⋊[φ] G (n₁,g₁)(n₂,g₂) = (n₁ · φ g₁ n₂, g₁ g₂)

そして `Semi f` がちょうどこの形であることを示す（`semiMulEquiv`）。

    N = (E ι α, ⊔, ⊥)          可換冪等モノイド（結び半束）
    G = Multiplicative ℕ        時計を進めた回数
    φ k = clockPow f k          `⊔` と `⊥` を保つ（`clockPow_sup`/`clockPow_bot`） -/

/-- 半束を `⊔` でモノイドとして見るための型シノニム。 -/
def SupM (α : Type v) : Type v := α

namespace SupM

variable {α : Type v}

/-- 元をこちら側へ。 -/
def of (a : α) : SupM α := a

/-- 元を戻す。 -/
def out (a : SupM α) : α := a

@[simp] theorem out_of (a : α) : out (of a) = a := rfl
@[simp] theorem of_out (a : SupM α) : of (out a) = a := rfl

instance [SemilatticeSup α] [OrderBot α] : CommMonoid (SupM α) where
  mul a b := of (out a ⊔ out b)
  one := of ⊥
  mul_assoc a b c := congrArg of (sup_assoc (out a) (out b) (out c))
  one_mul a := congrArg of (bot_sup_eq (out a))
  mul_one a := congrArg of (sup_bot_eq (out a))
  mul_comm a b := congrArg of (sup_comm (out a) (out b))

@[simp] theorem mul_def [SemilatticeSup α] [OrderBot α] (a b : SupM α) :
    a * b = of (out a ⊔ out b) := rfl

@[simp] theorem one_def [SemilatticeSup α] [OrderBot α] :
    (1 : SupM α) = of ⊥ := rfl

end SupM

/-! ## 一般形 -/

variable {N : Type u} {G : Type v} [Monoid N] [Monoid G]

/-- **モノイドの半直積 `N ⋊[φ] G`。**`φ` は自己準同型でよい。 -/
structure MSemi (φ : G →* Monoid.End N) where
  /-- `N` の成分 -/
  left : N
  /-- `G` の成分 -/
  right : G

namespace MSemi

variable {φ : G →* Monoid.End N}

theorem ext' {a b : MSemi φ} (hl : a.left = b.left) (hr : a.right = b.right) :
    a = b := by cases a; cases b; simp_all

instance : Mul (MSemi φ) where
  mul a b := ⟨a.left * φ a.right b.left, a.right * b.right⟩

instance : One (MSemi φ) where
  one := ⟨1, 1⟩

@[simp] theorem mul_left (a b : MSemi φ) :
    (a * b).left = a.left * φ a.right b.left := rfl

@[simp] theorem mul_right (a b : MSemi φ) : (a * b).right = a.right * b.right := rfl

@[simp] theorem one_left : (1 : MSemi φ).left = 1 := rfl
@[simp] theorem one_right : (1 : MSemi φ).right = 1 := rfl

/-- **本当にモノイドをなす。**結合律に `φ` が準同型であることが効く。 -/
instance : Monoid (MSemi φ) where
  mul_assoc a b c := by
    refine ext' ?_ (mul_assoc _ _ _)
    show a.left * φ a.right b.left * φ (a.right * b.right) c.left
        = a.left * φ a.right (b.left * φ b.right c.left)
    rw [map_mul φ, map_mul (φ a.right), mul_assoc]
    rfl
  one_mul a := by
    refine ext' ?_ (one_mul _)
    show 1 * φ 1 a.left = a.left
    rw [map_one φ, one_mul]
    rfl
  mul_one a := by
    refine ext' ?_ (mul_one _)
    show a.left * φ a.right 1 = a.left
    rw [map_one (φ a.right), mul_one]

/-- 刻むだけ（`G` の側は単位）。 -/
def inl (n : N) : MSemi φ := ⟨n, 1⟩

/-- 進めるだけ（`N` の側は単位）。 -/
def inr (g : G) : MSemi φ := ⟨1, g⟩

theorem inl_mul (m n : N) : (inl m : MSemi φ) * inl n = inl (m * n) := by
  refine ext' ?_ (one_mul _)
  show m * φ 1 n = m * n
  rw [map_one φ]; rfl

theorem inr_mul (g h : G) : (inr g : MSemi φ) * inr h = inr (g * h) := by
  refine ext' ?_ rfl
  show 1 * φ g 1 = 1
  rw [map_one (φ g), mul_one]

theorem inl_mul_inr (n : N) (g : G) : (inl n : MSemi φ) * inr g = ⟨n, g⟩ := by
  refine ext' ?_ (one_mul _)
  show n * φ 1 1 = n
  rw [map_one φ]; show n * 1 = n; rw [mul_one]

/-- **どの元も「刻む」と「進める」の積に分かれる。** -/
theorem factor (a : MSemi φ) : a = inl a.left * inr a.right :=
  (inl_mul_inr a.left a.right).symm

/-- **捻れの正体。**`inr` を先に通すと `φ` が掛かる。 -/
theorem inr_inl_comm (n : N) (g : G) :
    (inr g : MSemi φ) * inl n = inl (φ g n) * inr g := by
  rw [inl_mul_inr]
  refine ext' ?_ (mul_one _)
  show 1 * φ g n = φ g n
  rw [one_mul]

/-- **`φ` が自明なら直積。**直積モノイドは半直積の特殊形である。 -/
theorem mul_of_trivial (h : ∀ g, φ g = 1) (a b : MSemi φ) :
    a * b = ⟨a.left * b.left, a.right * b.right⟩ := by
  refine ext' ?_ rfl
  show a.left * φ a.right b.left = a.left * b.left
  rw [h]; rfl

end MSemi

/-! ## `Semi f` はこの形である -/

section Instance

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-- 時計を `SupM (E ι α)` の自己準同型として見る。`⊔` と `⊥` を保つ。 -/
def clockEnd (f : ι → (α ≃o α)) :
    Multiplicative ℕ →* Monoid.End (SupM (E ι α)) where
  toFun k :=
    { toFun := fun a => SupM.of (clockPow f (Multiplicative.toAdd k) (SupM.out a))
      map_one' := by
        show SupM.of (clockPow f _ (⊥ : E ι α)) = SupM.of ⊥
        rw [clockPow_bot]
      map_mul' := fun a b => by
        show SupM.of (clockPow f _ (SupM.out a ⊔ SupM.out b))
            = SupM.of (clockPow f _ (SupM.out a) ⊔ clockPow f _ (SupM.out b))
        rw [clockPow_sup] }
  map_one' := by
    ext a
    show SupM.of (clockPow f 0 (SupM.out a)) = a
    rw [clockPow_zero]; rfl
  map_mul' j k := by
    ext a
    show SupM.of (clockPow f (Multiplicative.toAdd j + Multiplicative.toAdd k)
        (SupM.out a)) = _
    rw [clockPow_add]
    rfl

/-- **`Semi f` は標準的なモノイド半直積の実例である。**

`⊔` が可換なので `σ^{k}(B) ⊔ A = A · φ(k)(B)` の形にそのまま収まる。 -/
def semiMulEquiv (f : ι → (α ≃o α)) : Semi f ≃* MSemi (clockEnd f) where
  toFun p := ⟨SupM.of p.left, Multiplicative.ofAdd p.right⟩
  invFun q := ⟨SupM.out q.left, Multiplicative.toAdd q.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' p q := by
    refine MSemi.ext' ?_ rfl
    show SupM.of (clockPow f p.right q.left ⊔ p.left)
        = SupM.of p.left * (clockEnd f (Multiplicative.ofAdd p.right)
            (SupM.of q.left))
    show SupM.of (clockPow f p.right q.left ⊔ p.left)
        = SupM.of (p.left ⊔ clockPow f p.right q.left)
    rw [sup_comm]

end Instance

end HorizontalSum
