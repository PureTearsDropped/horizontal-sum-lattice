import HorizontalSum.Folding

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 作用を無限次元の行列として書く — 置換 × 対角

`Φ` の座標（`E` で添字づけた 0/1 ベクトル）で見ると、作用は次の形になる。

    Φ(A • B) = σ(Φ B) ∩ Φ A

    σ(·)   置換（時計は順序同型なので添字を並べ替えるだけ）
    ∩ Φ A  対角（`Φ A` の指示関数を掛ける）

つまり **`•` は「対角行列 × 置換行列」**であり、無限次元だが構造は単純である。
合成すると `σ` の冪が掛かり、定数項が `⊔` で合流する——有限模型で確かめた
「アフィン対の積 ＝ 2×2 三角行列の積」の、座標側の姿。 -/

/-- 時計は `⊔` を保つ（順序同型だから）。 -/
theorem clock_sup (f : ι → (α ≃o α)) (x y : E ι α) :
    clock f (x ⊔ y) = clock f x ⊔ clock f y := by
  rcases x with _ | ⟨i, a⟩ | _ <;> rcases y with _ | ⟨j, b⟩ | _ <;>
    first
      | rfl
      | (by_cases h : i = j
         · subst h; simp [clock, E.sup, map_sup]
         · simp [clock, E.sup, h])

/-- **作用の座標表示。**置換してから対角を掛ける。 -/
theorem Phi_act (f : ι → (α ≃o α)) (A B : E ι α) :
    Phi (act (clock f) A B) = (clockIso f) '' Phi B ∩ Phi A := by
  ext y
  show clock f B ⊔ A ≤ y ↔ _
  rw [sup_le_iff]
  refine and_congr_left (fun _ => ?_)
  constructor
  · intro h
    refine ⟨(clockIso f).symm y, ?_, by simp⟩
    have hB : (clockIso f) B ≤ y := h
    exact (clockIso f).le_symm_apply.mpr hB
  · rintro ⟨z, hz, rfl⟩
    exact (clockIso f).monotone hz

/-- **二回作用させると `σ` の冪が上がる。**アフィン合成の座標版。 -/
theorem Phi_act_twice (f : ι → (α ≃o α)) (A C B : E ι α) :
    Phi (act (clock f) A (act (clock f) C B))
      = (clockIso f) '' ((clockIso f) '' Phi B ∩ Phi C) ∩ Phi A := by
  rw [Phi_act, Phi_act]

/-- **定数項は `σ(C) ⊔ A` に合流する。**`[σ A][σ C] = [σ² , σ(C)⊔A]`。 -/
theorem act_comp_is_affine (f : ι → (α ≃o α)) (A C B : E ι α) :
    act (clock f) A (act (clock f) C B)
      = clock f (clock f B) ⊔ (clock f C ⊔ A) := by
  show clock f (clock f B ⊔ C) ⊔ A = _
  rw [clock_sup]
  ac_rfl

/-! ### 作用の正体は半直積モノイド — `E ⋊[σ] ℕ`

`•` そのものは積ではない（結合律が破れる）。**積になるのはその上位**で、
`(σ^k, A)` の対がなす**半直積モノイド**である。

    (E, ⊔, 𝓛)      可換冪等モノイド（結び半束）
    σ              そのモノイド準同型（`⊔` を保ち `𝓛` を `𝓛` に）
    E ⋊[σ] ℕ       半直積。(k₁,A₁)(k₂,A₂) = (k₁+k₂, σ^{k₁}(A₂) ⊔ A₁)
    E              その M-集合（モノイド作用を受ける）
    A • B          = (1, A) • B      ← **k = 1 の切り口にすぎない**

**モノイドの半直積は既知の構成である**（Zappa–Szép 積などの名で代数では
標準的）。新しいのはこの定義ではなく、`•` がその積の左成分だという同定
（`act_eq_mul_left`）のほうである。

自前で定義したのは Mathlib の都合による。`N ⋊[φ] G` は `[Group N] [Group G]`
と `φ : G →* MulAut N` を要求するが、こちらは `σ` が自己同型でなくモノイド
準同型でよく、`(E, ⊔)` も群ではない。Zappa–Szép 積も Mathlib には無い。

`2×2` 三角行列はこの半直積の標準的な**表現**である。 -/

/-- `σ` を `k` 回かける。 -/
def clockPow (f : ι → (α ≃o α)) : ℕ → E ι α → E ι α
  | 0, x => x
  | (n + 1), x => clock f (clockPow f n x)

@[simp] theorem clockPow_zero (f : ι → (α ≃o α)) (x : E ι α) :
    clockPow f 0 x = x := rfl

theorem clockPow_succ (f : ι → (α ≃o α)) (n : ℕ) (x : E ι α) :
    clockPow f (n + 1) x = clock f (clockPow f n x) := rfl

theorem clockPow_bot (f : ι → (α ≃o α)) (n : ℕ) :
    clockPow f n (⊥ : E ι α) = ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [clockPow_succ, ih]; rfl

theorem clockPow_sup (f : ι → (α ≃o α)) (n : ℕ) (x y : E ι α) :
    clockPow f n (x ⊔ y) = clockPow f n x ⊔ clockPow f n y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [clockPow_succ, ih, clock_sup, clockPow_succ, clockPow_succ]

theorem clockPow_add (f : ι → (α ≃o α)) (m n : ℕ) (x : E ι α) :
    clockPow f (m + n) x = clockPow f m (clockPow f n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add, clockPow_succ, ih, clockPow_succ]

/-- **半直積モノイド `E ⋊[σ] ℕ`。**対 `(A, k)` は「刻んだもの」と「進めた回数」。 -/
structure Semi (f : ι → (α ≃o α)) where
  /-- 定数項（刻んだもの） -/
  left : E ι α
  /-- 時計を進めた回数 -/
  right : ℕ

namespace Semi

variable {f : ι → (α ≃o α)}

instance : Mul (Semi f) where
  mul a b := ⟨clockPow f a.right b.left ⊔ a.left, a.right + b.right⟩

instance : One (Semi f) where
  one := ⟨⊥, 0⟩

@[simp] theorem mul_left (a b : Semi f) :
    (a * b).left = clockPow f a.right b.left ⊔ a.left := rfl

@[simp] theorem mul_right (a b : Semi f) :
    (a * b).right = a.right + b.right := rfl

@[simp] theorem one_left : (1 : Semi f).left = ⊥ := rfl
@[simp] theorem one_right : (1 : Semi f).right = 0 := rfl

theorem ext' {a b : Semi f} (hl : a.left = b.left) (hr : a.right = b.right) :
    a = b := by
  cases a; cases b; simp_all

/-- **半直積は本当にモノイドをなす。** -/
instance : Monoid (Semi f) where
  mul_assoc a b c := by
    refine ext' ?_ ?_
    · simp only [mul_left, mul_right, clockPow_sup, clockPow_add, sup_assoc]
    · simp only [mul_right, Nat.add_assoc]
  one_mul a := ext' (by simp) (by simp)
  mul_one a := ext'
    (by show clockPow f a.right (⊥ : E ι α) ⊔ a.left = a.left
        rw [clockPow_bot]; exact bot_sup_eq _)
    (by simp)

/-- **`E` はこのモノイドの作用を受ける。** -/
instance : MulAction (Semi f) (E ι α) where
  smul p x := clockPow f p.right x ⊔ p.left
  one_smul x := by
    show clockPow f 0 x ⊔ ⊥ = x
    simp
  mul_smul a b x := by
    show clockPow f (a * b).right x ⊔ (a * b).left
        = clockPow f a.right (clockPow f b.right x ⊔ b.left) ⊔ a.left
    simp only [mul_left, mul_right, clockPow_sup, clockPow_add, sup_assoc]

@[simp] theorem smul_def (p : Semi f) (x : E ι α) :
    p • x = clockPow f p.right x ⊔ p.left := rfl

/-- 束の元を「一歩進める作用」として見る。これで `A • B` と書ける。 -/
instance : Coe (E ι α) (Semi f) where
  coe A := ⟨A, 1⟩

@[simp] theorem coe_left (A : E ι α) : ((A : Semi f)).left = A := rfl
@[simp] theorem coe_right (A : E ι α) : ((A : Semi f)).right = 1 := rfl

/-- **時計が恒等なら、半直積は直積になる。**
直積モノイドは半直積の特殊形（作用が自明な場合）である。 -/
theorem mul_left_of_trivial (a b : Semi (fun _ : ι => OrderIso.refl α)) :
    (a * b).left = b.left ⊔ a.left := by
  show clockPow (fun _ : ι => OrderIso.refl α) a.right b.left ⊔ a.left = _
  congr 1
  induction a.right with
  | zero => rfl
  | succ n ih =>
      rw [clockPow_succ, ih]
      rcases b.left with _ | ⟨i, x⟩ | _ <;> rfl

/-- **直積モノイドは半直積の特殊形。**成分ごとの積になる。 -/
theorem is_direct_product_when_trivial
    (a b : Semi (fun _ : ι => OrderIso.refl α)) :
    (a * b).left = b.left ⊔ a.left ∧ (a * b).right = a.right + b.right :=
  ⟨mul_left_of_trivial a b, rfl⟩

end Semi

/-- **`•` は半直積の `k = 1` の切り口。**
作用の法則 `(p*q) • B = p • (q • B)` は本物なので、`•` と `*` を使ってよい。
`•` 自体は結合的でないので、積の記号を当てるのは誤りである。 -/
theorem act_eq_smul (f : ι → (α ≃o α)) (A B : E ι α) :
    act (clock f) A B = (A : Semi f) • B := by
  show clock f B ⊔ A = clockPow f 1 B ⊔ A
  rfl

/-- **作用は半直積の積の左成分そのもの。**（ユーザ指摘）

    ⟨A,1⟩ * ⟨B,1⟩ = (σ(B) ⊔ A, 2)
                     ─────┬────
                          └── これが A • B

だから**作用という概念すら要らず、`*` だけで書ける**。左成分を読むだけ。 -/
theorem act_eq_mul_left (f : ι → (α ≃o α)) (A B : E ι α) :
    act (clock f) A B = ((A : Semi f) * (B : Semi f)).left := rfl

/-- 右成分は「時計を何回進めたか」を数えている。 -/
theorem mul_right_counts (f : ι → (α ≃o α)) (A B : E ι α) :
    ((A : Semi f) * (B : Semi f)).right = 2 := rfl

/-- **積を繰り返すと左成分に作用の履歴が、右成分に歩数が溜まる。** -/
theorem mul_three (f : ι → (α ≃o α)) (A B C : E ι α) :
    ((A : Semi f) * (B : Semi f) * (C : Semi f)).left
      = clockPow f 2 C ⊔ (clock f B ⊔ A) ∧
    ((A : Semi f) * (B : Semi f) * (C : Semi f)).right = 3 := by
  constructor
  · show clockPow f (1 + 1) C ⊔ (clockPow f 1 B ⊔ A) = _
    rfl
  · rfl


/-! ### 二つの入れ方 — `inl`（刻む）と `inr`（進める）

半直積には標準的な入れ方が二つある（Mathlib の `SemidirectProduct` の
`inl` / `inr` と同じ形）。

    inl : (E, ⊔) → Semi     A ↦ ⟨A, 0⟩    刻むだけ・時計を進めない   ← 空間
    inr : (ℕ, +) → Semi     k ↦ ⟨𝓛, k⟩    進めるだけ・何も刻まない   ← 時間

そして `⟨A, 1⟩ = inl A * inr 1`——さっきの coe はこの二つの合成だった。 -/

namespace Semi

variable {f : ι → (α ≃o α)}

/-- 刻むだけ（時計を進めない）。 -/
def inl (A : E ι α) : Semi f := ⟨A, 0⟩

/-- 進めるだけ（何も刻まない）。 -/
def inr (k : ℕ) : Semi f := ⟨⊥, k⟩

@[simp] theorem inl_left (A : E ι α) : (inl A : Semi f).left = A := rfl
@[simp] theorem inl_right (A : E ι α) : (inl A : Semi f).right = 0 := rfl
@[simp] theorem inr_left (k : ℕ) : (inr k : Semi f).left = ⊥ := rfl
@[simp] theorem inr_right (k : ℕ) : (inr k : Semi f).right = k := rfl

/-- **`inl` は `(E, ⊔)` からの準同型。**刻みは `⊔` で合流する。 -/
theorem inl_mul (A B : E ι α) :
    (inl A : Semi f) * inl B = inl (B ⊔ A) := by
  refine ext' ?_ rfl
  show clockPow f 0 B ⊔ A = B ⊔ A
  rfl

/-- **`inr` は `(ℕ, +)` からの準同型。**進める回数は足される。 -/
theorem inr_mul (j k : ℕ) : (inr j : Semi f) * inr k = inr (j + k) := by
  refine ext' ?_ rfl
  show clockPow f j (⊥ : E ι α) ⊔ ⊥ = ⊥
  rw [clockPow_bot]
  exact sup_idem _

@[simp] theorem inl_bot : (inl ⊥ : Semi f) = 1 := rfl
@[simp] theorem inr_zero : (inr 0 : Semi f) = 1 := rfl

/-- **任意の元は「刻む」と「進める」の積に分解する。** -/
theorem inl_mul_inr (A : E ι α) (k : ℕ) :
    (inl A : Semi f) * inr k = ⟨A, k⟩ := by
  refine ext' ?_ (Nat.zero_add k)
  show clockPow f 0 (⊥ : E ι α) ⊔ A = A
  exact bot_sup_eq A

/-- **さっきの coe はこの二つの合成だった。** -/
theorem coe_eq_inl_mul_inr (A : E ι α) :
    (A : Semi f) = inl A * inr 1 := (inl_mul_inr A 1).symm

/-- **逆向きの積は捻れる。**`inr` が先だと `σ` が掛かる。
これが半直積が直積でない理由そのもの。 -/
theorem inr_mul_inl (A : E ι α) (k : ℕ) :
    (inr k : Semi f) * inl A = ⟨clockPow f k A, k⟩ := by
  refine ext' ?_ ?_
  · show clockPow f k A ⊔ ⊥ = clockPow f k A
    exact sup_bot_eq _
  · show k + 0 = k
    exact Nat.add_zero k

/-- **捻れの正体。**`inr k * inl A = inl (σ^k A) * inr k`。
時計を先に進めてから刻むのと、刻んでから進めるのが、`σ^k` だけずれる。 -/
theorem inr_inl_comm (A : E ι α) (k : ℕ) :
    (inr k : Semi f) * inl A = inl (clockPow f k A) * inr k := by
  rw [inr_mul_inl, inl_mul_inr]

end Semi


/-! ### 有限テンソルによる近似 — 作用の版

`trunc` は有限の部分束で、時計は一歩ごとに切り口を一つ伸ばす。作用も
`⊔` を一回足すだけなので、**同じ窓の中で閉じる**。 -/

theorem trunc_mono {m N N' : ℕ} (h : N ≤ N') {x : E (Fin m) ℤ}
    (hx : x ∈ trunc m N) : x ∈ trunc m N' := by
  obtain hb | ⟨i, a, rfl, ha⟩ := hx
  · exact Or.inl hb
  · exact Or.inr ⟨i, a, rfl, ha.trans (by exact_mod_cast h)⟩

/-- **作用しても切り口が一つ伸びるだけ。**⟸ `trunc_clock_step` + `trunc_sup_mem`。 -/
theorem trunc_act_step {m N : ℕ} {a b : E (Fin m) ℤ}
    (ha : a ∈ trunc m N) (hb : b ∈ trunc m N) :
    act (clock (fun _ : Fin m => shift1)) a b ∈ trunc m (N + 1) :=
  trunc_sup_mem (trunc_clock_step hb) (trunc_mono (Nat.le_succ N) ha)

/-- **T 歩の作用は `N + T` の窓に収まる。**
だから**有限テンソルで有限時間ぶんを厳密に計算できる**。
`trunc_approximates`（時計だけの版）の作用への拡張。 -/
theorem trunc_act_approximates :
    ∀ (T m N : ℕ) (as : List (E (Fin m) ℤ)), as.length = T →
      (∀ a ∈ as, a ∈ trunc m N) →
      ∀ {b : E (Fin m) ℤ}, b ∈ trunc m N →
        as.foldl (act (clock (fun _ : Fin m => shift1))) b ∈ trunc m (N + T) := by
  intro T
  induction T with
  | zero =>
      intro m N as hlen _ b hb
      obtain rfl : as = [] := List.eq_nil_of_length_eq_zero hlen
      simpa using hb
  | succ T ih =>
      intro m N as hlen hin b hb
      match as with
      | [] => simp at hlen
      | a :: rest =>
          have hrest : rest.length = T := by simpa using hlen
          have ha : a ∈ trunc m N := hin a (by simp)
          -- foldl は `act acc elem`＝`clock elem ⊔ acc` なので、b が作用する側
          have hstep := trunc_act_step hb ha
          have hin' : ∀ x ∈ rest, x ∈ trunc m (N + 1) := fun x hx =>
            trunc_mono (Nat.le_succ N) (hin x (by simp [hx]))
          have := ih m (N + 1) rest hrest hin' hstep
          have hN : N + 1 + T = N + (T + 1) := by omega
          simpa [List.foldl_cons, hN] using this

end HorizontalSum
