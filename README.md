# horizontal-sum-lattice

A bounded lattice whose ι-labelled chains meet only at `⊥` and join only at `⊤`
— the **horizontal sum** — together with its action and the algebra of its
labels. Lean 4 + Mathlib, **268 declarations audited, no `sorry`**.

> ⚠️ 生成AI使用・要検証 / AI-assisted; verify.
> 定理は Lean が確かめている（`tools/verify.py` が 268/268 を報告する）。
> 検証が及ばないのは**その外側**——文書の主張、「Mathlib に無い」という判断、
> 定理が意図した内容かどうか。そこは人の目で確かめてほしい。

```
git clone https://github.com/PureTearsDropped/horizontal-sum-lattice
cd horizontal-sum-lattice
lake exe cache get && lake build
python tools/verify.py            # 268/268
```

---

## 何を作っているか

`⊥` と `⊤` の間を、名札 `ι` で区別された `α` の鎖が渡る束。

```
⟨i,a⟩ ⪯ ⟨j,b⟩  ⟺  i = j かつ a ⪯ b     別の軸どうしは比較できない
⟨i,a⟩ ⊔ ⟨j,b⟩ = ⊤                     (i ≠ j) 上では ⊤ でだけ出会う
⟨i,a⟩ ⊓ ⟨j,b⟩ = ⊥                     (i ≠ j) 下では ⊥ でだけ出会う
```

これを `E ι α`、軸ごとに型が違ってよい一般形を `Family.T ι P` と書く。

## Mathlib に無いもの

台そのものは既存の構成である（`stdEquiv : E ι α ≃o WithBot (WithTop (Σ _ : ι, α))`）。
無いのは**束の構造**のほうである。

```
Sigma に束のインスタンス   無い（直和は束でない。別成分に上限が無い）
Sum.Lex（α ⊕ₗ β）         縦積み（α の全部が β の下）で別物
WithTop.lattice           台が既に束であることを要求
```

**私たちが `Order/` を当たった範囲では見つからなかった**——「束でない半順序に
`⊥`,`⊤` を足して束にする」構成である。`Family.instLattice` がそれにあたる。
見落としがあれば教えてほしい。

**十分条件であって必要条件ではない。** 各 `P i` が束なら全体は束になるが、逆は
成り立たない。二元の反鎖（束でない）に `⊥`,`⊤` を足すとダイヤモンド `M2` に
なり、これは束である（`Family.two_not_lattice` / `Family.two_hsum_has_lub`）。
`⊤` が上限を肩代わりするので、軸の中に上限が無くてよい。正しい条件は

```
T ι P が束  ⟺  各 P i で「上界を持つ対には最小上界が在る」（下も同様）
```

で、`Family.mid_isLUB_iff`（両向き）・`cross_isLUB`・`cross_isGLB` が場合を尽くす。

## 作用

`A • B = σ B ⊔ A`。これは**半直積モノイド `E ⋊[σ] ℕ` の積の左成分**である
（`act_eq_mul_left`）。空間方向の `inl` と時間方向の `inr` が捻れで繋がる。

```lean
inr k * inl A = inl (clockPow f k A) * inr k        -- inr_inl_comm
```

座標で見ると「置換 × 対角」のトロピカル・アフィン系で、合成は 2×2 三角行列の
積になる。

**モノイドの半直積も既知の構成である**（Zappa–Szép 積などの名で標準的）。
Mathlib の `SemidirectProduct` が `[Group N] [Group G]` を要求するため自前で
定義しただけで、新しいのは定義ではなく `•` がその積の左成分だという同定
（`act_eq_mul_left`）のほうである。

## 既存数学への接続

自作の構成を Mathlib の語彙に落とした 25 本が中心にある。

```
E ι α          WithBot (WithTop (Σ _ : ι, α))    stdEquiv
E ι α          Family.T ι (fun _ => α)           Family.eEquiv
act            半直積の積の左成分                  act_eq_mul_left
Phi / Down     Set.Ici / Set.Iic                 Phi_Down_are_intervals
chi            Set.indicator                     chi_eq_indicator
clockPow       Function.iterate                  clockPow_eq_iterate
pathAmp        List.prod                         pathAmp_eq_map_prod
shift1/shiftBy OrderIso.addRight                 shift_are_addRight
lrot / rrot    Equiv.mulLeft / mulRight          lrot_rrot_are_translations
Foldable       ℤ からの加法準同型                 foldable_iff_smul
qmat / cmat    ℍ / ℂ の正則表現                  qmat_mul_regular / cmat_mul
```

一つ、両向きの同値がある。**経路の重ね合わせが成り立つ ⟺ 名札の群が可換**
（`superposition_iff_commutative`）。`Q8` のような非可換な名札では `[i,j]` と
`[j,i]` の終点が違い、重ね合わせは成立しない。

## 代償

この束は分配的でもモジュラでもなく（`not_distributive`・`not_modular`）、
直積に分解できない（`complement_not_unique`）。原因は主張の中心そのもので、
**別々の軸は中間の高さで出会わず、必ず `⊤` まで飛ぶ**ことである。

---

## 構成

```
HorizontalSum.lean        根（全モジュールを import する）
HorizontalSum/
  Basic.lean              E の定義・順序・束・stdEquiv
  Rotation.lean           rot / conj / Four
  Group.lean              名札を群に取る・捩れ子・Q8
  Quad.lean               quad / aquad（Fin 4 → R）      ← 束を参照しない
  Matrix.lean             qmat / cmat                     ← 束を参照しない
  Phase.lean              位相で名付けた軸
  Action.lean             作用・時計・公理
  Confinement.lean        閉じ込め・直既約
  Branch.lean             多価の時計・錐
  Trace.lean              履歴・始点
  Coordinates.lean        Φ / Ψ
  Tensor.lean             無限次元・有限テンソル近似
  Folding.lean            Foldable・経路の重ね合わせ
  Semidirect.lean         半直積モノイド
  Bridge.lean             既存の道具との対応
  Family.lean             軸ごとに型が違う一般形・反例
  Cost.lean               非分配・非モジュラ
Audit.lean                全宣言に #print axioms を流す
```

## 文書

```
THEOREMS.md   宣言一覧。**機械生成**（tools/gen_theorems.py）。意味づけは入らない
DESIGN.md     設計と根拠、そして**何を主張しないか**
READING.md    この束を何と読むか。**定理は一つもこれに依存しない**
```

読みを Lean から分けてあるのは、読みが証明の一部だと誤解されないためと、
読みに同意しない人が定理だけを使えるようにするためである。

## 検証

`tools/verify.py` が `Audit.lean` の `#print axioms` 出力を読み、268 本が

- 受理されていること（Lean は受理した宣言にしか答えない）
- `sorryAx` を含まないこと
- `propext` / `Classical.choice` / `Quot.sound` 以外の公理に依らないこと

を確かめる。うち 7 本は公理をまったく使わない。

## 言えないこと

`DESIGN.md` に記録してある。主なものだけ挙げる。

```
頻度が定義できない     導けない。単一の履歴から独立反復試行を構成する
                     仕組みを、まだ定義していない
⊥ は唯一の定常点       違う。⊤ も不動点で、σ の不動点はすべて定常
時間の終わり           言えない。始まりも終わりも在ってよい
錐が埋まる            多価の時計を入れた場合のみ。単価では埋まらない
```

**先行研究を当たった結果。構成そのものは既知である。**

```
半直積モノイド          既知   Zappa–Szép 積。Mathlib は群版しか持たない
水平和（有界束）         既知   L, M の ⊥ どうし・⊤ どうしを**貼り合わせる**
水平和（有界半順序の族）   既知   任意の添字族。各成分は**半順序でよい**。
                            成分は ⊥,⊤ だけを共有し、異なる成分の元は比較不能
```

`Family.T ι P` は、各 `P i` に上下端を付けた bounded poset

```
P̂ i = WithBot (WithTop (P i))
```

の水平和に同型である。つまり**この一般形も既存の枠内**にある。任意の添字集合・
軸ごとに違う型・各成分は単なる半順序でよい、というところまで既知である。

一度「この版は未確認」と書いたが、**確かめたら既知だった**。過小主張も過大主張も、
確かめずに言えば同じ誤りである。

### では何が残るか — 形式化の側だけ

```
Mathlib に無い     Sigma に束のインスタンスが無い
                  Sum.Lex は縦積み（α の全部が β の下）
                  WithTop.lattice は台が既に束であることを要求
LUB/GLB の API    mid_isLUB_iff（両向き）・cross_isLUB・cross_isGLB を
                  再利用できる粒度で書いた
```

**LUB/GLB の特徴づけは水平和の定義からほぼ直接出るので、数学的な新規性としては
主張しない。** 同じ形の characterization theorem は探した範囲で見つからなかったが、
それは「言われていない」ではなく「わざわざ書くほどでもない」の可能性が高い。

このリポジトリの中身は**既知の構成の Lean 4 + Mathlib 形式化**である。
価値が在るとすればライブラリとしての再利用性で、数学的な新しさではない。

## ライセンス

0BSD。
