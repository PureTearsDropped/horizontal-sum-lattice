import HorizontalSum.Tensor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 畳み直せる条件 — 値づけが加法的であること

各時刻の値を one-hot で書くと、`𝓛` は**全 1**、`𝓦` は**one-hot** である
（`chi_allones_iff` / `chi_onehot_iff`）。

    e_a + e_b は one-hot ではない（二か所立つ ＝ 𝓛 の側へ戻る）

にもかかわらず混ぜられるのは、**添字から値への写像が加法的**で、和を一つの
添字に畳み直せるからである。ここではその同値を示す。 -/

/-- 歩幅の値づけ `val : ℤ → M` が**畳み直せる**とは、和が添字の和で表せること。 -/
def Foldable {M : Type*} [AddCommGroup M] (val : ℤ → M) : Prop :=
  ∀ a b : ℤ, val a + val b = val (a + b)

/-- **等差なら畳み直せる。**符号器が使っているのはこれ（`s_k = k · base`）。 -/
theorem foldable_of_smul {M : Type*} [AddCommGroup M] (v : M) :
    Foldable (fun k : ℤ => k • v) := fun a b => (add_smul a b v).symm

/-- **畳み直せるなら等差しかない。**⟸ `ℤ` からの加法準同型は `k ↦ k • val 1`。 -/
theorem smul_of_foldable {M : Type*} [AddCommGroup M] {val : ℤ → M}
    (h : Foldable val) (k : ℤ) : val k = k • val 1 := by
  have hz : val 0 = 0 := by
    have := h 0 0
    simpa using this.symm
  let f : ℤ →+ M := AddMonoidHom.mk' val (fun a b => (h a b).symm)
  have : f k = k • f 1 := by simpa using (map_zsmul f k 1)
  simpa [f] using this

/-- **これが「混ぜられる」の必要十分条件。** -/
theorem foldable_iff_smul {M : Type*} [AddCommGroup M] (val : ℤ → M) :
    Foldable val ↔ ∀ k : ℤ, val k = k • val 1 := by
  constructor
  · exact fun h => smul_of_foldable h
  · intro h a b
    rw [h a, h b, h (a + b), add_smul]

/-- 乗法版の「畳み直せる」。合成が積のときの条件。 -/
def FoldableMul {G : Type*} [CommGroup G] (val : ℤ → G) : Prop :=
  ∀ a b : ℤ, val a * val b = val (a + b)

/-- **等比なら畳み直せる。**`e^{in} = (e^i)^n` がこれ。 -/
theorem foldableMul_of_zpow {G : Type*} [CommGroup G] (v : G) :
    FoldableMul (fun k : ℤ => v ^ k) := fun a b => (zpow_add v a b).symm

/-- **畳み直せるなら等比しかない。**⟸ `ℤ` からの群準同型は `k ↦ (val 1)^k`。 -/
theorem zpow_of_foldableMul {G : Type*} [CommGroup G] {val : ℤ → G}
    (h : FoldableMul val) (k : ℤ) : val k = val 1 ^ k := by
  have h1 : val 0 = 1 := by
    have := h 0 0
    simpa using this.symm
  let f : Multiplicative ℤ →* G :=
    { toFun := fun k => val (Multiplicative.toAdd k)
      map_one' := h1
      map_mul' := fun a b => (h _ _).symm }
  simpa [f] using (f.map_zpow (Multiplicative.ofAdd 1) k)

/-- **加法と乗法は同じ定理の 双対の形。**どちらも `ℤ` からの準同型が
一意であることから出る。**どちらを採るかは「何を保ちたいか」で決まる。**

    保ちたい操作    値づけ         one-hot の値
    足し算（ミックス）  k • v（等差）   … −2base, −base, 0, +base, +2base …
    掛け算（位相合成）  v^k（等比）     … e^{−2i}, e^{−i}, 1, e^{i}, e^{2i} …

音声のミキシングは**足し算**なので加法側を採る。位相の合成は掛け算なので、
そちらを保ちたいなら `e^{ik}` が正しい値づけになる（`W^θ` の名札はこちら）。
両方を同時に保つことはできない——`e^{ia} + e^{ib} ≠ e^{i(a+b)}`。 -/
theorem additive_and_multiplicative_are_dual {M G : Type*}
    [AddCommGroup M] [CommGroup G] (v : M) (w : G) :
    Foldable (fun k : ℤ => k • v) ∧ FoldableMul (fun k : ℤ => w ^ k) :=
  ⟨foldable_of_smul v, foldableMul_of_zpow w⟩


/-- **`cos` は畳み直せない。**原案の `R cos(2πj/M)` が混ぜられなかった理由。 -/
theorem cos_not_foldable : ¬ Foldable (fun k : ℤ => Real.cos k) := by
  intro h
  have := h 0 0
  norm_num at this

/-- **まとめ。**値を one-hot で書いたとき、和を one-hot に畳み直せるのは
**値づけが等差のときだけ**である。等差 ⟺ 添字が群準同型 `(ℤ,+) → (M,+)`。

これは `superposition_iff_commutative`（重ね合わせ ⟺ 名札が可換）の
値の側の姿であり、音声符号化で `s_k = (k−w)·base` を使っている理由でもある。
`arccos` や `μ-law` のような非線形な値づけは、この性質を壊す。 -/
theorem mixing_needs_arithmetic_steps {M : Type*} [AddCommGroup M] (v : M) :
    Foldable (fun k : ℤ => k • v) ∧ ¬ Foldable (fun k : ℤ => Real.cos k) :=
  ⟨foldable_of_smul v, cos_not_foldable⟩


/-! ### 経路の重ね合わせ — 成り立つのは名札が可換なときだけ

符号器が保存しているのは「どの `W^{θ_n}` を通ったか」の**経路**であり、
ミキシングはその**重ね合わせ**である。成り立つ条件は一つに絞れる。

    名札の群が可換    ⟹  経路の順序が潰れ、終点は歩幅の和だけで決まる（重ね合わせ○）
    名札が非可換      ⟹  順序が残り、和では書けない（重ね合わせ×・干渉が出る）

`List.Perm.prod_eq` がその境目そのものである。 -/

/-- 経路の終点。`start` から `l` の歩幅を順に適用した先。 -/
def endpoint [Monoid G] (start : G) (l : List G) : G := pathAmp id l * start

@[simp] theorem endpoint_nil [Monoid G] (start : G) : endpoint start [] = start := by
  simp [endpoint]

/-- **可換なら、経路は歩幅の多重集合しか覚えない。**⟸ `List.Perm.prod_eq`。
だから順番を入れ替えても終点が変わらない——これが重ね合わせの前提。 -/
theorem endpoint_perm [CommMonoid G] (start : G) {l₁ l₂ : List G}
    (h : l₁.Perm l₂) : endpoint start l₁ = endpoint start l₂ := by
  simp [endpoint, amp_perm_invariant id h]

/-- **可換なら、二つの経路を「重ねる」と歩幅ごとの積になる。**
`ℤ` に取れば `Σδ_A + Σδ_B = Σ(δ_A + δ_B)` ——音声側で測った恒等式そのもの。 -/
theorem endpoint_zip [CommMonoid G] (s₁ s₂ : G) : ∀ (l₁ l₂ : List G),
    l₁.length = l₂.length →
    endpoint s₁ l₁ * endpoint s₂ l₂ = endpoint (s₁ * s₂) (List.zipWith (· * ·) l₁ l₂)
  | [], [], _ => by simp
  | a :: as, b :: bs, h => by
      have hl : as.length = bs.length := by simpa using h
      have := endpoint_zip s₁ s₂ as bs hl
      simp only [endpoint, pathAmp, List.map_cons, List.prod_cons, id_eq,
        List.zipWith_cons_cons] at this ⊢
      calc a * (as.map id).prod * s₁ * (b * (bs.map id).prod * s₂)
          = (a * b) * ((as.map id).prod * s₁ * ((bs.map id).prod * s₂)) := by
              simp [mul_comm, mul_assoc, mul_left_comm]
        _ = (a * b) * ((List.zipWith (· * ·) as bs).map id).prod * (s₁ * s₂) := by
              rw [this]; simp [mul_comm, mul_assoc, mul_left_comm]

/-- **非可換だと崩れる。**`Q8` で `[i, j]` と `[j, i]` は終点が違う。
だから重ね合わせは成り立たず、順序が残る（＝干渉の源）。 -/
theorem endpoint_not_perm_of_noncomm :
    ∃ (g h : QuaternionGroup 2), endpoint 1 [g, h] ≠ endpoint 1 [h, g] := by
  obtain ⟨g, h, hgh⟩ := q8_not_comm
  exact ⟨g, h, by simpa [endpoint, pathAmp] using hgh⟩

/-- **まとめ。**重ね合わせが成り立つかどうかは、名札の群が可換かで決まる。
音声符号化で `δ ∈ ℤ`（可換）を使っているから足せる。 -/
theorem superposition_iff_commutative :
    (∀ (s : Multiplicative ℤ) (l₁ l₂ : List (Multiplicative ℤ)),
        l₁.Perm l₂ → endpoint s l₁ = endpoint s l₂) ∧
      (∃ (g h : QuaternionGroup 2), endpoint 1 [g, h] ≠ endpoint 1 [h, g]) :=
  ⟨fun _ _ _ h => endpoint_perm _ h, endpoint_not_perm_of_noncomm⟩


/-! ### 軸の内側には足し算がある — 時計の合成

`⊔` は冪等で足し算ではないが、**軸の内側は順序つき群**であり、時計はその
平行移動である。だから**時計を重ねると指数が足される**。

これが音声符号化の側で「符号語を足すとミックスになる」として現れたものの正体。
使っているのは `⊔` ではなく、**一本の軸の内側の加法**である。 -/

/-- 速さ `k` の時計。`shift1` を `k` 回かけたもの。 -/
def shiftBy (k : ℤ) : ℤ ≃o ℤ := OrderIso.addRight k

@[simp] theorem shiftBy_apply (k a : ℤ) : shiftBy k a = a + k := rfl

/-- **時計を重ねると速さが足される。**`σ_j ∘ σ_k = σ_{j+k}`。 -/
theorem shiftBy_comp (j k a : ℤ) : shiftBy j (shiftBy k a) = shiftBy (j + k) a := by
  show a + k + j = a + (j + k)
  ring

theorem shift1_is_shiftBy_one (a : ℤ) : shift1 a = shiftBy 1 a := rfl

/-- 軸ごとの時計でも同じ。**束の上で時計が可換な群をなす。** -/
theorem clock_shiftBy_comp (j k : ι → ℤ) (x : E ι ℤ) :
    clock (fun i => shiftBy (j i)) (clock (fun i => shiftBy (k i)) x)
      = clock (fun i => shiftBy (j i + k i)) x := by
  rcases x with _ | ⟨i, a⟩ | _
  · rfl
  · show E.axis i (a + k i + j i) = E.axis i (a + (j i + k i))
    congr 1
    ring
  · rfl

/-- **T 歩の合成は速さ T の一歩に等しい。**⟸ 上。 -/
theorem clock_iterate_shiftBy (k : ℤ) (T : ℕ) (x : E ι ℤ) :
    (clock (fun _ : ι => shiftBy k))^[T] x = clock (fun _ : ι => shiftBy (T * k)) x := by
  induction T with
  | zero => rcases x with _ | ⟨i, a⟩ | _ <;> simp [clock, shiftBy]
  | succ T ih =>
      rw [Function.iterate_succ_apply', ih, clock_shiftBy_comp]
      congr 1
      funext i
      push_cast
      ring

/-- **これがミキシングの恒等式である。**
二つの歩みを重ねた結果は、歩幅を足した一つの歩みに等しい。
音声符号化では「符号語 `δ_A + δ_B` を復号するとミックスになる」として現れる。
`⊔` は使っていない——使っているのは**一本の軸の内側の加法**だけ。 -/
theorem mixing_identity (j k : ℤ) (i : ι) (a : ℤ) :
    clock (fun _ : ι => shiftBy j) (clock (fun _ : ι => shiftBy k) (E.axis i a))
      = E.axis i (a + (j + k)) := by
  show E.axis i (a + k + j) = E.axis i (a + (j + k))
  congr 1
  ring

/-- **足し算が在るのは軸の内側だけ。**軸をまたぐと `⊔` は `𝓦` に潰す。
だから「足せる」ことと「結べる」ことは別の操作である。 -/
theorem addition_is_inside_the_axis {i j : ι} (hij : i ≠ j) (a b : ℤ) :
    (E.axis i a : E ι ℤ) ⊔ E.axis j b = ⊤ ∧
      clock (fun _ : ι => shiftBy b) (E.axis i a : E ι ℤ) = E.axis i (a + b) :=
  ⟨axes_join_to_world hij a b, rfl⟩

end HorizontalSum
