import HorizontalSum.Branch

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

variable {ι : Type u} {α : Type v} [DecidableEq ι] [Lattice α]

/-! ### 履歴 — 戻れないこと、𝓦 が吸収すること

働きかけを列にして辿る。ここで出るのは三つ。

    **戻れない**（時計が増大的なら値は単調に増える）
    **𝓦 は吸収する**（一度着いたら出られない）
    **`⊥` から始めて全部 `⊥` なら `⊥` のまま**（唯一の定常点ではない）

ただし `trace_mono` が与えるのは **非減少**であって狭義増加ではない。
`𝓛 • 𝓛 = 𝓛`・`𝓦 • B = 𝓦` なので**同じ状態に留まることは起きる**。
言えるのは「下がらない」までで、「同じ状況が二度来ない」は出ない。

したがって「頻度が定義できない」も導けない。正確には、**この単一の履歴から
独立反復試行を内部に構成する仕組みを、まだ定義していない**。 -/

/-- 働きかけの列に沿って状態を辿る。 -/
def trace (f : ι → (α ≃o α)) (x : E ι α) (as : List (E ι α)) : E ι α :=
  as.foldl (fun s a => act (clock f) a s) x

@[simp] theorem trace_nil (f : ι → (α ≃o α)) (x : E ι α) : trace f x [] = x := rfl

@[simp] theorem trace_cons (f : ι → (α ≃o α)) (x a : E ι α) (as : List (E ι α)) :
    trace f x (a :: as) = trace f (act (clock f) a x) as := rfl

/-- **𝓦 は吸収する。**第二引数が 𝓦 なら値は 𝓦。 -/
theorem world_absorbing_target (f : ι → (α ≃o α)) (a : E ι α) :
    act (clock f) a ⊤ = ⊤ := by simp [act]

/-- 第一引数が 𝓦 でも値は 𝓦。 -/
theorem world_absorbing_actor (f : ι → (α ≃o α)) (b : E ι α) :
    act (clock f) ⊤ b = ⊤ := by simp [act]

/-- **戻れない。**時計が増大的なら、状態は履歴に沿って単調に増える。
だから「同じ状況をもう一度」が起きず、頻度が定義できない。 -/
theorem trace_mono (f : ι → (α ≃o α)) (hf : ∀ x : E ι α, x ≤ clock f x)
    (x : E ι α) (as : List (E ι α)) : x ≤ trace f x as := by
  induction as generalizing x with
  | nil => exact le_rfl
  | cons a as ih => exact le_trans (le_trans (hf x) le_sup_left) (ih _)

/-- **`⊥` から始めて全部 `⊥` なら、値は 𝓛 のまま動かない。**

注意: これは「𝓛 が唯一の定常点」ではない。`𝓦 • 𝓦 = 𝓦` なので `𝓦` も
不動点であり、一般に `σ` の不動点はすべて定常である。
言えるのは**始点が 𝓛 なら 𝓛 に留まる**ことだけである。 -/
theorem all_lmonad_stays (f : ι → (α ≃o α)) (as : List (E ι α))
    (h : ∀ a ∈ as, a = ⊥) : trace f (⊥ : E ι α) as = ⊥ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      have ha : a = ⊥ := h a (List.mem_cons_self ..)
      subst ha
      rw [trace_cons, show act (clock f) (⊥ : E ι α) ⊥ = ⊥ from by simp [act]]
      exact ih fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- **同じ軸の中なら 𝓦 に行かない。**一歩ぶん。 -/
theorem same_axis_never_world (f : ι → (α ≃o α)) (i : ι) (a b : α) :
    act (clock f) (E.axis i a) (E.axis i b) ≠ ⊤ := by
  rw [same_axis_act]
  simp

/-- **第一引数が全部同じ軸なら、履歴を通じて 𝓦 に行かない。**
𝓦 を呼ぶのは軸をまたぐ側だけである。 -/
theorem trace_stays_on_axis (f : ι → (α ≃o α)) (i : ι) (a : α)
    (as : List (E ι α)) (h : ∀ b ∈ as, ∃ y, b = E.axis i y) :
    ∃ z, trace f (E.axis i a) as = E.axis i z := by
  induction as generalizing a with
  | nil => exact ⟨a, rfl⟩
  | cons b as ih =>
      obtain ⟨y, rfl⟩ := h b (List.mem_cons_self ..)
      rw [trace_cons, same_axis_act]
      exact ih _ fun c hc => h c (List.mem_cons_of_mem _ hc)


/-! ### 始点はどこか — 「すべてに届く」から 𝓛 が出る

「始点は 𝓛 である」は**導けない。仮定である。**
ただし次の要求を置けば強制される。

    要求: **どの元にも履歴で届ける**

効いているのは **`x ≤ clock f x`**（⑥・`trace_mono`）である。
逆戻りしないので始点 `x` から届くのは `↑x` だけで、`↑x` が全体になるのは
`x = 𝓛` のときに限る。 -/

/-- **`⊥` から始めれば一歩で任意の元に届く。**`𝓛 • B = B` だから。 -/
theorem lmonad_can_become_anything (f : ι → (α ≃o α)) (y : E ι α) :
    trace f ⊥ [y] = y := by
  simp [trace, act]

/-- **すべての元に届く始点は 𝓛 ただ一つ。**
「どの元にも履歴で届ける」を要求すると、始点が 𝓛 に強制される。
これで始点は仮定でなく、より弱い要求からの帰結になる。
仮定 `hf` は「値が減らない」にあたる。 -/
theorem only_lmonad_can_become_anything (f : ι → (α ≃o α))
    (hf : ∀ x : E ι α, x ≤ clock f x) (x : E ι α)
    (h : ∀ y : E ι α, ∃ as, trace f x as = y) : x = ⊥ := by
  obtain ⟨as, has⟩ := h ⊥
  have hx := trace_mono f hf x as
  rw [has] at hx
  exact le_bot_iff.mp hx

end HorizontalSum
