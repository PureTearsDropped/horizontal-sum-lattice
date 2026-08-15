"""リポジトリの整合を守るテスト。**Lean を起動しない**ので数秒で終わる。

定理そのものは Lean が確かめる（`python tools/verify.py`）。ここが見るのは
その周りで壊れやすいところ——生成物が古くないか、読みが混ざっていないか、
主張が文書と一致しているか。

    python -m unittest discover tests -v
"""

import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))

import gen_theorems as GT                                      # noqa: E402
from checked import CHECKED                                    # noqa: E402


class TheModulesLineUp(unittest.TestCase):
    """根が import するものと、実際に在るファイルが一致すること。"""

    def test_every_import_has_a_file(self):
        for name, path in GT.modules():
            with self.subTest(name):
                self.assertTrue(path.exists(), f'{path} が無い')

    def test_every_file_is_imported(self):
        imported = {n for n, _ in GT.modules()}
        on_disk = {p.stem for p in (ROOT / 'HorizontalSum').glob('*.lean')}
        self.assertEqual(on_disk - imported, set(),
                         'HorizontalSum/ に在るのに根が import していない')

    def test_each_module_opens_and_closes_the_namespace(self):
        for name, path in GT.modules():
            s = path.read_text()
            with self.subTest(name):
                self.assertEqual(s.count('namespace HorizontalSum'), 1)
                self.assertEqual(s.count('end HorizontalSum'), 1)

    def test_imports_form_a_chain_from_mathlib(self):
        """最初のモジュールだけが Mathlib を直接 import する。"""
        mods = GT.modules()
        self.assertIn('import Mathlib', mods[0][1].read_text())
        for name, path in mods[1:]:
            with self.subTest(name):
                self.assertRegex(path.read_text(), r'import HorizontalSum\.\w+')


class TheAuditCoversEverything(unittest.TestCase):
    """`Audit.lean` が `CHECKED` の全部を見ていること。"""

    def setUp(self):
        self.audit = (ROOT / 'Audit.lean').read_text()

    def test_every_checked_name_is_printed(self):
        for name, _ in CHECKED:
            with self.subTest(name):
                self.assertIn(f'#print axioms HorizontalSum.{name}', self.audit)

    def test_it_prints_nothing_else(self):
        printed = set(re.findall(r'#print axioms HorizontalSum\.(\S+)', self.audit))
        self.assertEqual(printed - {n for n, _ in CHECKED}, set())

    def test_the_count_is_stated_everywhere(self):
        self.assertEqual(len(CHECKED), 268)
        self.assertIn('268', (ROOT / 'README.md').read_text())


class TheGeneratedDocumentIsFresh(unittest.TestCase):
    """`THEOREMS.md` は生成物。**手で書かない。**"""

    def test_it_is_up_to_date(self):
        self.assertEqual((ROOT / 'THEOREMS.md').read_text(),
                         GT.render(GT.source()),
                         'python tools/gen_theorems.py で作り直すこと')

    def test_every_checked_name_appears_fully_qualified(self):
        s = (ROOT / 'THEOREMS.md').read_text()
        for name, _ in CHECKED:
            with self.subTest(name):
                self.assertIn(f'HorizontalSum.{name}', s)


class TheReadingIsKeptOutOfTheLean(unittest.TestCase):
    """読みは `READING.md` にだけ在る。**Lean 側にも `THEOREMS.md` にも無い。**"""

    def test_the_lean_carries_no_reading(self):
        src = GT.source()
        for w in ('愛', '世界', '相手', '超選択', '傷つけ', '選択肢'):
            with self.subTest(w):
                self.assertNotIn(w, src)

    def test_the_generated_document_carries_no_reading(self):
        s = (ROOT / 'THEOREMS.md').read_text()
        self.assertNotIn('/--', s)
        self.assertNotIn('愛', s)

    def test_the_reading_is_keyed_by_declaration(self):
        r = (ROOT / 'READING.md').read_text()
        for n in ('E.lmonad', 'seven', 'nine', 'confinement',
                  'only_lmonad_is_traceable', 'two_kinds_of_non_lmonad'):
            with self.subTest(n):
                self.assertIn(n, r)
        for w in ('愛', '世界'):
            with self.subTest(w):
                self.assertIn(w, r)


class TheClaimsAreBounded(unittest.TestCase):
    """**言い過ぎを止める。**過去に言い過ぎた箇所がそのまま残っていること。"""

    def setUp(self):
        self.design = (ROOT / 'DESIGN.md').read_text().replace('\n', '')
        self.readme = (ROOT / 'README.md').read_text().replace('\n', '')

    def test_frequency_is_not_claimed(self):
        self.assertIn('まだ定義していない', self.design)
        self.assertIn('導けない', self.design)

    def test_the_bottom_is_not_the_only_fixed_point(self):
        self.assertIn('唯一の定常点」**ではない**', self.design)

    def test_the_cone_is_not_claimed_filled(self):
        self.assertIn('埋まらない', self.design)

    def test_the_readme_separates_checked_from_unchecked_prior_art(self):
        """**確かめたことと確かめていないことを混ぜない。**

        一度「順序論では既知」と確かめずに断定した。過小主張も、確かめずに
        言えば過大主張と同じ誤りである。その区別を消させない。
        """
        self.assertIn('未確認', self.readme)
        self.assertIn('確かめていない', self.readme)
        self.assertIn('Zappa', self.readme)

    def test_the_readme_states_how_the_classical_horizontal_sum_differs(self):
        """古典的な水平和は**有界束の境界を貼り合わせる**構成で、別物である。"""
        self.assertIn('貼り合わせる', self.readme)
        self.assertIn('新しく足す', self.readme)

    def test_the_readme_says_sufficient_not_necessary(self):
        """反例を README にも残す。ここが一度間違えたところ。"""
        self.assertIn('必要条件ではない', self.readme)
        self.assertIn('two_not_lattice', self.readme)


class ThePackageIsSelfContained(unittest.TestCase):
    def test_the_lakefile_declares_the_library(self):
        s = (ROOT / 'lakefile.toml').read_text()
        self.assertIn('name = "HorizontalSum"', s)
        self.assertIn('name = "mathlib"', s)

    def test_the_toolchain_is_pinned(self):
        self.assertRegex((ROOT / 'lean-toolchain').read_text().strip(),
                         r'^leanprover/lean4:v\d+\.\d+\.\d+$')

    def test_the_manifest_is_present(self):
        """依存のコミットを固定するファイル。無いと半年後に壊れる。"""
        self.assertTrue((ROOT / 'lake-manifest.json').exists())

    def test_the_licence_is_zero_bsd(self):
        s = (ROOT / 'LICENSE').read_text()
        self.assertIn('Permission to use, copy, modify, and/or distribute', s)
        self.assertNotIn('retain the above copyright notice', s)


if __name__ == '__main__':
    unittest.main(verbosity=2)
