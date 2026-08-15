#!/usr/bin/env python3
"""`#print axioms` の出力を読んで、268 本が本当に通っているか確かめる。

`Audit.lean` は全宣言に `#print axioms` を流すだけのファイルである。Lean は
受理した宣言についてのみ答えるので、**答えが返ってきたこと自体が受理の証拠**に
なる。さらに依存公理を見て `sorryAx` が無いことを確かめる。

    python tools/verify.py            # ビルドして検証する
    python tools/verify.py --reuse    # 既にある出力を使う（開発用）

期待される公理は次の三つだけである。これは Mathlib の通常の土台で、
「証明していない」という意味ではない。

    propext           命題の外延性
    Classical.choice  選択公理
    Quot.sound        商の健全性

`sorryAx` が一つでも出たら失敗とする。
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from checked import CHECKED                                    # noqa: E402

NAMESPACE = 'HorizontalSum'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
CACHE = ROOT / '.audit-output.txt'

# 宣言名に `'` が入りうる（`relative_label_invariant'`）ので貪欲に取る。
ACCEPTED = re.compile(r"^'(.+)' depends on axioms: \[([^\]]*)\]$", re.M)
NO_AXIOM = re.compile(r"^'(.+)' does not depend on any axioms$", re.M)


def run_audit(timeout: int = 1800) -> str | None:
    """`lake env lean Audit.lean` を回して出力を返す。"""
    try:
        p = subprocess.run(['lake', 'env', 'lean', 'Audit.lean'],
                           cwd=ROOT, timeout=timeout,
                           capture_output=True, text=True)
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print(f'lake を起動できない: {e}')
        return None
    return p.stdout + p.stderr


def parse(out: str) -> dict:
    """宣言名 → 依存公理の集合。答えが無い宣言は入らない。"""
    got = {n: {a.strip() for a in ax.split(',') if a.strip()}
           for n, ax in ACCEPTED.findall(out)}
    got.update({n: set() for n in NO_AXIOM.findall(out)})
    return got


def report(got: dict) -> int:
    missing, tainted, extra, clean = [], [], [], []
    for name, _ in CHECKED:
        ax = got.get(f'{NAMESPACE}.{name}')
        if ax is None:
            missing.append(name)
        elif 'sorryAx' in ax:
            tainted.append(name)
        else:
            if not ax:
                clean.append(name)
            if ax - STANDARD:
                extra.append((name, sorted(ax - STANDARD)))

    n = len(CHECKED)
    ok = n - len(missing) - len(tainted)
    print(f'\n=== {ok}/{n} ===\n')
    print(f'  公理ゼロで通ったもの     {len(clean)}/{n}')
    print(f'  標準の三公理まで         {n - len(clean) - len(missing) - len(tainted)}/{n}')
    if extra:
        print(f'\n  **標準以外の公理に依存**  {len(extra)} 件')
        for name, ax in extra[:20]:
            print(f'    {name}: {", ".join(ax)}')
    if tainted:
        print(f'\n  **sorryAx を含む**  {len(tainted)} 件')
        for name in tainted[:20]:
            print(f'    {name}')
    if missing:
        print(f'\n  **受理されなかった**  {len(missing)} 件')
        for name in missing[:20]:
            print(f'    {name}')
    print()
    return 0 if not (missing or tainted or extra) else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reuse', action='store_true',
                    help='前回の出力を使う（Lean を回さない）')
    args = ap.parse_args(argv)

    if args.reuse and CACHE.exists():
        out = CACHE.read_text()
    else:
        out = run_audit()
        if out is None:
            return 2
        CACHE.write_text(out)
    return report(parse(out))


if __name__ == '__main__':
    sys.exit(main())
