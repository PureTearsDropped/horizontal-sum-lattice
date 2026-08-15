import HorizontalSum.Phase

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! # 位相・時計・作用 — 公理が一つも壊れないこと -/

/-! ## 位相で名付けた軸 — W^θ = W^(−θ) = W^(iθ) = W^(−iθ)

名札の型 `ι` は任意なので、**連続無限本の時間軸**をそのまま扱える。
位相 `θ ∈ ℂ` で名付ければ、四つ組 `θ, −θ, iθ, −iθ` は
（`θ ≠ 0` なら）相異なる四本の軸であり、上ではすべて同じ 𝓦 に至る。 -/

noncomputable instance instDecidableEqComplex : DecidableEq ℂ := Classical.decEq ℂ

/-- 位相に `i` を掛ける（四分の一回転）。順序同型。 -/
noncomputable def quarter : E ℂ α ≃o E ℂ α :=
  ofAxisEquiv (Equiv.mulLeft₀ Complex.I Complex.I_ne_zero)

theorem one_sub_I_ne_zero : (1 : ℂ) - Complex.I ≠ 0 :=
  sub_ne_zero.mpr (by simp [Complex.ext_iff])

theorem one_add_I_ne_zero : (1 : ℂ) + Complex.I ≠ 0 := by
  simp [Complex.ext_iff]

theorem phase_ne_neg {θ : ℂ} (h : θ ≠ 0) : θ ≠ -θ := fun he => by
  have h2 : (2 : ℂ) * θ = 0 := by linear_combination he
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact h h3

theorem phase_ne_mul_I {θ : ℂ} (h : θ ≠ 0) : θ ≠ Complex.I * θ := fun he => by
  have h2 : (1 - Complex.I) * θ = 0 := by linear_combination he
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact one_sub_I_ne_zero h3
  · exact h h3

theorem phase_ne_neg_mul_I {θ : ℂ} (h : θ ≠ 0) : θ ≠ -(Complex.I * θ) :=
  fun he => by
    have h2 : (1 + Complex.I) * θ = 0 := by linear_combination he
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact one_add_I_ne_zero h3
    · exact h h3

/-- **任意の θ, φ について W^θ = W^φ。**
四つ組に限る必要はない。位相がいくつあっても、相異なる軸は上で
必ず同じただ一つの 𝓦 に至る。`θ ≠ φ` は「同じ軸どうし」を
除くためだけの条件で、同じ軸なら結びは軸の中に留まる
（`same_axis_sup`）。 -/
theorem all_phases_one_world {θ φ : ℂ} (h : θ ≠ φ) (a b : α) :
    (E.axis θ a : E ℂ α) ⊔ E.axis φ b = ⊤ := axes_join_to_world h a b

/-- 双対。任意の θ, φ について、二本の軸は下では 𝓛 でだけ出会う。 -/
theorem all_phases_meet_at_lmonad {θ φ : ℂ} (h : θ ≠ φ) (a b : α) :
    (E.axis θ a : E ℂ α) ⊓ E.axis φ b = ⊥ := axes_meet_at_lmonad h a b

/-- **W^θ = W^(−θ) = W^(iθ) = W^(−iθ)** —
上の一般形の特別な場合。四つの位相の軸は相異なるが、
上ではどれも同じただ一つの 𝓦 に至る。 -/
theorem four_phases_one_world {θ : ℂ} (h : θ ≠ 0) (a b : α) :
    ((E.axis θ a : E ℂ α) ⊔ E.axis (-θ) b = ⊤) ∧
    ((E.axis θ a : E ℂ α) ⊔ E.axis (Complex.I * θ) b = ⊤) ∧
    ((E.axis θ a : E ℂ α) ⊔ E.axis (-(Complex.I * θ)) b = ⊤) :=
  ⟨axes_join_to_world (phase_ne_neg h) a b,
   axes_join_to_world (phase_ne_mul_I h) a b,
   axes_join_to_world (phase_ne_neg_mul_I h) a b⟩

/-- 双対。四つの位相の軸は下では 𝓛 でだけ出会う。 -/
theorem four_phases_meet_at_lmonad {θ : ℂ} (h : θ ≠ 0) (a b : α) :
    ((E.axis θ a : E ℂ α) ⊓ E.axis (-θ) b = ⊥) ∧
    ((E.axis θ a : E ℂ α) ⊓ E.axis (Complex.I * θ) b = ⊥) ∧
    ((E.axis θ a : E ℂ α) ⊓ E.axis (-(Complex.I * θ)) b = ⊥) :=
  ⟨axes_meet_at_lmonad (phase_ne_neg h) a b,
   axes_meet_at_lmonad (phase_ne_mul_I h) a b,
   axes_meet_at_lmonad (phase_ne_neg_mul_I h) a b⟩

/-! ## 作用 — 時計は一つ、速さは軸ごと -/

/-- 軸ごとに違う速さで進む時計。速さは軸の関数であって、束の元ごとではない。 -/
def clock (f : ι → (α ≃o α)) : E ι α → E ι α
  | .lmonad => .lmonad
  | .axis i a => .axis i (f i a)
  | .world => .world

@[simp] theorem clock_lmonad (f : ι → (α ≃o α)) :
    clock f (E.lmonad : E ι α) = E.lmonad := rfl
@[simp] theorem clock_axis (f : ι → (α ≃o α)) (i : ι) (a : α) :
    clock f (E.axis i a) = E.axis i (f i a) := rfl
@[simp] theorem clock_world (f : ι → (α ≃o α)) :
    clock f (E.world : E ι α) = E.world := rfl

theorem clock_bot (f : ι → (α ≃o α)) : clock f (⊥ : E ι α) = ⊥ := rfl

theorem clock_mono (f : ι → (α ≃o α)) : Monotone (clock f : E ι α → E ι α) := by
  rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) h <;> simp_all

theorem clock_injective (f : ι → (α ≃o α)) :
    Function.Injective (clock f : E ι α → E ι α) := by
  rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _) h <;> simp_all
  obtain ⟨rfl, hab⟩ := h
  exact (f i).injective hab

/-- 作用。`A • B = σ B ⊔ A`。 -/
def act (σ : E ι α → E ι α) (a b : E ι α) : E ι α := σ b ⊔ a

variable (f : ι → (α ≃o α))

/-- ⑦ `A • ⊥ = A`。⊥ は作用の右単位元。 -/
theorem seven (a : E ι α) : act (clock f) a ⊥ = a := by
  simp [act]

/-- ⑧ **分解則が生き残る。**軸ごとに速さが違っても壊れない。 -/
theorem eight (a b : E ι α) :
    act (clock f) a b = act (clock f) ⊥ b ⊔ act (clock f) a ⊥ := by
  simp [act]

/-- ⑥ 積み上げ ＝ 時間の矢印。 -/
theorem six (a b : E ι α) : a ≤ act (clock f) a b := le_sup_right

/-- ⑤ 働く者について単調。 -/
theorem five (a b c : E ι α) (h : a ≤ b) :
    act (clock f) a c ≤ act (clock f) b c := sup_le_sup_left h _

/-- ④ 対象について単調。 -/
theorem four (a : E ι α) : Monotone (act (clock f) a) :=
  fun _ _ h => sup_le_sup_right (clock_mono f h) _

/-- ⑨ `⊥ • −` は単射。 -/
theorem nine : Function.Injective (act (clock f) (⊥ : E ι α)) := by
  intro x y h
  exact clock_injective f (by simpa [act] using h)

/-- **公理は一つも壊れない。** -/
theorem clock_axioms :
    (∀ a : E ι α, act (clock f) a ⊥ = a) ∧
    (∀ a b : E ι α, act (clock f) a b = act (clock f) ⊥ b ⊔ act (clock f) a ⊥) ∧
    (∀ a b : E ι α, a ≤ act (clock f) a b) ∧
    (∀ a b c : E ι α, a ≤ b → act (clock f) a c ≤ act (clock f) b c) ∧
    (∀ a : E ι α, Monotone (act (clock f) a)) ∧
    Function.Injective (act (clock f) (⊥ : E ι α)) :=
  ⟨seven f, eight f, six f, five f, four f, nine f⟩


/-! # 公理から出る定理 — `Love.lean` をこの束の上で -/

/-! ## `Love.lean` をこの束の上で書き直す

`Love.lean` は有界束を**仮定して** `A • B = σ B ⊔ A` を特徴づけた。
ここではその定理群を、いま作った束の上で具体的に書き直す。

要点は一つ。**`clock f` は順序同型なので全射が無料で手に入る。**
`Love.lean` では全射を有限性から調達していた（`sigma_bijective`）が、
この束は無限（`infinite_of_infinite`）なのでその道は使えない。
それでも `only_lmonad_injective_of_surjective` の側は全射だけで通るので、
**`only_lmonad_is_traceable` は有限性なしでそのまま成立する。** -/

/-- 軸ごとの時計を順序同型として取り出す。 -/
def clockIso (f : ι → (α ≃o α)) : E ι α ≃o E ι α where
  toFun := clock f
  invFun := clock (fun i => (f i).symm)
  left_inv := by rintro (_ | ⟨i, a⟩ | _) <;> simp
  right_inv := by rintro (_ | ⟨i, a⟩ | _) <;> simp
  map_rel_iff' := by
    rintro (_ | ⟨i, a⟩ | _) (_ | ⟨j, b⟩ | _)
    all_goals first
      | exact Iff.rfl
      | exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by subst h1; exact (f i).le_iff_le.mp h2⟩,
               fun ⟨h1, h2⟩ => ⟨h1, by subst h1; exact (f i).le_iff_le.mpr h2⟩⟩

instance instNontrivial : Nontrivial (E ι α) :=
  ⟨⟨E.lmonad, E.world, by simp⟩⟩

/-- この束は無限。だから `Love.lean` の有限性の節は使えない。 -/
theorem infinite_of_infinite [Infinite α] (i : ι) : Infinite (E ι α) :=
  Infinite.of_injective (fun a => E.axis i a) (fun a b h => by simpa using h)

/-- **作用は `σ` ひとつで決まる。** `Love.form` に対応。 -/
theorem form (a b : E ι α) : act (clock f) a b = act (clock f) ⊥ b ⊔ a := by
  simp [act]

/-- **`σ ⊥ = ⊥`。** `Love.sigma_fixes_love`。 -/
theorem sigma_fixes_lmonad : act (clock f) (⊥ : E ι α) ⊥ = ⊥ := by simp [act]

/-- **すべての作用は `σ` を経由する。** `Love.factors_through_love`。 -/
theorem factors_through_lmonad (a b : E ι α) :
    act (clock f) a b = (fun x => x ⊔ a) (act (clock f) ⊥ b) := by simp [act]

/-- 後段は第二引数に依らない。`Love.second_stage_ignores_target`。 -/
theorem second_stage_ignores_target (a : E ι α) :
    ∀ b, act (clock f) a b = (fun x => x ⊔ a) (act (clock f) ⊥ b) :=
  factors_through_lmonad f a

/-- 後段は情報を捨てるだけ。`Love.second_stage_forgets`。 -/
theorem second_stage_forgets (a : E ι α) (ha : a ≠ ⊥) :
    ¬ Function.Injective (fun x : E ι α => x ⊔ a) := fun hinj =>
  ha (hinj (by simp : (⊥ : E ι α) ⊔ a = a ⊔ a)).symm

/-- 第一引数は `A • ⊥` から一意に定まる。`Love.actor_from_love`。 -/
theorem actor_from_lmonad {a a' : E ι α}
    (e : act (clock f) a ⊥ = act (clock f) a' ⊥) : a = a' := by
  simpa [act] using e

/-- 第二引数も `⊥ • B` から一意に定まる。`Love.target_from_love`。 -/
theorem target_from_lmonad {b b' : E ι α}
    (e : act (clock f) ⊥ b = act (clock f) ⊥ b') : b = b' := nine f e

/-- 順序は作用の像の含まれ方で書ける。`Love.order_is_love`。 -/
theorem order_is_lmonad (a b : E ι α) :
    a ≤ b ↔ act (clock f) a ⊥ ≤ act (clock f) b ⊥ := by simp [act]

/-- **`⊥` は作用を受けると動く。** `Love.love_takes_form`。 -/
theorem lmonad_takes_form : ¬ ∀ a : E ι α, act (clock f) a ⊥ = ⊥ := fun h =>
  absurd (by simpa [act] using h ⊤ : (⊤ : E ι α) = ⊥) top_ne_bot

/-- 逆向きの時計で元に戻る。 -/
theorem clock_symm_clock (y : E ι α) :
    clock f (clock (fun i => (f i).symm) y) = y := by
  rcases y with _ | ⟨i, a⟩ | _ <;> simp

/-- **`σ` は全射。**順序同型だから無料で出る。有限性を使わない。 -/
theorem sigma_surjective : Function.Surjective (act (clock f) (⊥ : E ι α)) :=
  fun y => ⟨clock (fun i => (f i).symm) y, by simp [act, clock_symm_clock]⟩

/-- **`⊥` 以外は単射でない。** `Love.only_love_injective_of_surjective` に対応。
`Love.lean` では全射を有限性から取っていたが、ここでは
`clock f` が順序同型であることから直接出るので、**無限でも成立する**。 -/
theorem only_lmonad_is_traceable (a : E ι α) (ha : a ≠ ⊥) :
    ¬ Function.Injective (act (clock f) a) := by
  intro hinj
  obtain ⟨b, hb⟩ := sigma_surjective f a
  have hbne : b ≠ ⊥ := by
    rintro rfl
    exact ha (by simpa [act] using hb.symm)
  have h1 : act (clock f) a ⊥ = a := seven f a
  have h2 : act (clock f) a b = a := by rw [form f a b, hb, sup_idem]
  exact hbne (hinj (h1.trans h2.symm)).symm

/-! ### この束でしか言えないこと -/

/-- `⊥` の作用は、ただ時計を進めること。 -/
theorem lmonad_acts_by_the_clock (b : E ι α) :
    act (clock f) ⊥ b = clock f b := by simp [act]

/-- 同じ軸の上での作用は、軸の中に留まる。 -/
theorem same_axis_act (i : ι) (a b : α) :
    act (clock f) (E.axis i a) (E.axis i b) = E.axis i ((f i) b ⊔ a) := by
  simp [act]

/-- **軸をまたぐ作用は 𝓦 になる — 全部を失う。**
禁止されてはいない。ただし何も残らない。 -/
theorem cross_axis_act {i j : ι} (h : i ≠ j) (a b : α) :
    act (clock f) (E.axis i a) (E.axis j b) = ⊤ := by
  simp [act, h, Ne.symm h]

end HorizontalSum
