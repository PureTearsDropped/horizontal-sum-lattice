import HorizontalSum.MonoidSemidirect

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u v

namespace HorizontalSum

/-! # 添字集合に順序を入れる — これは Mathlib に在る

水平和も一般形ではない。**添字集合に構造を入れる**方向にもう一段ある。

    順序和（縦積み）   添字集合が**鎖**    `i < j` なら `P i` の全部が `P j` の下
    水平和            添字集合が**反鎖**  異なる成分は比較不能
    その間            添字集合が**束**    lattice-based sum（El-Zekey ら 2013）

**そしてその台と順序は Mathlib に在る。**自前で書く必要はなかった。

    Sigma.LE      直和。`⟨i,a⟩ ⪯ ⟨j,b⟩ ⟺ i = j かつ a ⪯ b`   ← 添字が反鎖の場合
    Σₗ i, P i     レックス和。`i < j` または（`i = j` かつ `a ⪯ b`）← 添字が順序集合

`Σₗ` は `Data/Sigma/Order.lean` に `Preorder`・`PartialOrder`・`LinearOrder`
まで揃っている。ここでは**両端に特殊化することを確かめる**だけにする。

    lex_of_lt_index     `i < j` なら成分をまたいで下から上へ   順序和の振る舞い
    lex_incomparable    添字が比較不能なら成分も比較不能       水平和の振る舞い
    lex_total           添字が鎖なら異なる成分は必ず比較できる
    lex_le_iff_of_no_lt 添字に真の順序が無ければ**直和と一致**

つまり `Σₗ` は両端をちょうど繋いでいる。**このリポが埋めているのは、
そのうち「添字が反鎖」の場合に `⊥`,`⊤` を足して束にするところだけ**である。 -/

variable {I : Type u} {P : I → Type v} [Preorder I] [∀ i, Preorder (P i)]

/-- **添字が下なら、成分をまたいで下から上へ。**添字を鎖に取れば順序和になる。 -/
theorem lex_of_lt_index {i j : I} (hij : i < j) (a : P i) (b : P j) :
    (toLex ⟨i, a⟩ : Σₗ i, P i) ≤ toLex ⟨j, b⟩ := Sigma.Lex.le_def.2 (Or.inl hij)

/-- **添字が比較不能なら、成分も比較不能。**添字を反鎖に取れば水平和になる。 -/
theorem lex_incomparable {i j : I} (hne : i ≠ j) (hlt : ¬ i < j)
    (a : P i) (b : P j) : ¬ ((toLex ⟨i, a⟩ : Σₗ i, P i) ≤ toLex ⟨j, b⟩) := by
  rw [Sigma.Lex.le_def]
  rintro (h | ⟨h, _⟩)
  · exact hlt h
  · exact hne h

/-- 同じ添字なら成分の順序がそのまま移る。 -/
theorem lex_le_same (i : I) (a b : P i) :
    ((toLex ⟨i, a⟩ : Σₗ i, P i) ≤ toLex ⟨i, b⟩) ↔ a ≤ b := by
  rw [Sigma.Lex.le_def]
  constructor
  · rintro (h | ⟨e, h⟩)
    · exact absurd h (lt_irrefl _)
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

/-- **添字が鎖なら、異なる成分も必ず比較できる。**＝順序和そのもの。 -/
theorem lex_total {i j : I} (hij : i < j ∨ j < i) (a : P i) (b : P j) :
    ((toLex ⟨i, a⟩ : Σₗ i, P i) ≤ toLex ⟨j, b⟩) ∨
      ((toLex ⟨j, b⟩ : Σₗ i, P i) ≤ toLex ⟨i, a⟩) := by
  rcases hij with h | h
  · exact Or.inl (lex_of_lt_index h a b)
  · exact Or.inr (lex_of_lt_index h b a)

/-- 添字が線形なら、その仮定は `i ≠ j` だけで足りる。 -/
theorem lex_total_of_linear [LinearOrder I] {J : Type u} {Q : J → Type v}
    [LinearOrder J] [∀ j, Preorder (Q j)] {i j : J} (hij : i ≠ j)
    (a : Q i) (b : Q j) :
    ((toLex ⟨i, a⟩ : Σₗ j, Q j) ≤ toLex ⟨j, b⟩) ∨
      ((toLex ⟨j, b⟩ : Σₗ j, Q j) ≤ toLex ⟨i, a⟩) :=
  lex_total (lt_or_gt_of_ne hij) a b

/-- **添字に真の順序が無ければ、レックス和は直和に一致する。**

`Sigma.LE`（`⟨i,a⟩ ⪯ ⟨j,b⟩ ⟺ i = j かつ a ⪯ b`）と同じものになる。
つまり「添字が反鎖」の場合がちょうど水平和の台である。 -/
theorem lex_le_iff_of_no_lt (h : ∀ i j : I, ¬ i < j) {i j : I} (a : P i) (b : P j) :
    ((toLex ⟨i, a⟩ : Σₗ i, P i) ≤ toLex ⟨j, b⟩) ↔ ∃ e : i = j, (e ▸ a : P j) ≤ b := by
  rw [Sigma.Lex.le_def]
  constructor
  · rintro (hc | hc)
    · exact absurd hc (h i j)
    · exact hc
  · exact Or.inr

end HorizontalSum
