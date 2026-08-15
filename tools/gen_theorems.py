#!/usr/bin/env python3
r"""`HorizontalSum/*.lean` から宣言を機械的に抜き出して `THEOREMS.md` を書く。

この文書には**意味づけを入れない**。入るのは Lean のソースに在るものだけ
——宣言名と、その型（定理なら主張そのもの）と、部・節の区切りである。
読み・解釈・動機は `DESIGN.md` / `READING.md` の側に置く。

    python tools/gen_theorems.py            # THEOREMS.md を書き出す
    python tools/gen_theorems.py --check    # 中身が最新かどうかだけ見る

抜き出しは字面で行う。`theorem`/`def`/`instance` などの行から、深さ 0 の
`:=` または行頭に戻るまでを一つの宣言とみなす。証明本体は捨てる。
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import List

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'THEOREMS.md'


def modules() -> list:
    """根 `HorizontalSum.lean` の import 順にモジュールを並べる。"""
    root = (ROOT / 'HorizontalSum.lean').read_text()
    names = re.findall(r'^import HorizontalSum\.(\w+)$', root, re.M)
    return [(n, ROOT / 'HorizontalSum' / f'{n}.lean') for n in names]


def source() -> str:
    """全モジュールを import 順に連結したもの。宣言の順序はこれで決まる。"""
    out = []
    for name, path in modules():
        out.append(f'/-! # {name} -/')
        out.append(path.read_text())
    return '\n'.join(out)

KINDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure',
         'inductive', 'noncomputable def')

#: 部の区切り `/-! # …`、節の区切り `/-! ## …` / `/-! ### …`
PART = re.compile(r'^/-!\s*(#+)\s*(.*?)(?:\s*-/)?\s*$')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive)\s+'
                  r'(\S*)')


def _strip_proof(block: str) -> str:
    """`:=` 以降（証明本体）と `where` 以降を落とし、型だけ残す。"""
    depth = 0
    i = 0
    while i < len(block):
        c = block[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and block.startswith(':=', i):
            return block[:i].rstrip()
        elif depth == 0 and block.startswith('\nwhere', i):
            return block[:i].rstrip()
        i += 1
    return block.rstrip()


#: 宣言の中に埋まっている説明用コメント。**意味づけなので落とす。**
DOCCOMMENT = re.compile(r'\s*/--.*?-/', re.S)


def _strip_docs(s: str) -> str:
    """`/-- … -/`（読み・動機）を落として、形式的な中身だけ残す。"""
    out = DOCCOMMENT.sub('', s)
    return '\n'.join(ln for ln in out.split('\n') if ln.strip())


def _dedent(s: str) -> str:
    lines = [ln.rstrip() for ln in s.split('\n')]
    while lines and not lines[-1]:
        lines.pop()
    return '\n'.join(lines)


def declarations(src: str) -> List[dict]:
    """部・節と宣言を、ソースに現れる順で返す。"""
    lines = src.split('\n')
    out: List[dict] = []
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = PART.match(ln)
        if m and not ln.startswith('/--'):
            title = m.group(2)
            if not title:                       # `/-! ## …` が次行に続く形
                i += 1
                title = lines[i].strip() if i < len(lines) else ''
            title = title.replace('-/', '').strip()
            out.append({'kind': 'head', 'level': len(m.group(1)), 'text': title})
            i += 1
            continue
        m = DECL.match(ln)
        if m:
            start = i
            i += 1
            while i < len(lines):
                nx = lines[i]
                if nx and not nx[0].isspace() and not nx.startswith(')'):
                    break
                i += 1
            block = '\n'.join(lines[start:i])
            out.append({'kind': m.group(1), 'name': m.group(2),
                        'text': _dedent(_strip_docs(_strip_proof(block)))})
            continue
        i += 1
    return out


def namespaces(src: str) -> dict:
    """宣言名 → 完全修飾名。`namespace` を追って前置する。"""
    stack: List[str] = []
    full = {}
    for ln in src.split('\n'):
        s = ln.strip()
        if s.startswith('namespace '):
            stack.append(s.split()[1])
        elif s.startswith('end ') and stack and s.split()[1:] == [stack[-1]]:
            stack.pop()
        else:
            m = DECL.match(ln)
            if m:
                full.setdefault(m.group(2), '.'.join(stack + [m.group(2)]))
    return full


HEADER = """# `HorizontalSum.lean` の宣言一覧

`HorizontalSum/*.lean` から機械的に抜き出したもの。**この文書に意味づけは入らない。**
在るのは宣言名と型（定理なら主張そのもの）だけで、読み・動機・解釈は
`DESIGN.md` / `READING.md` の側に置く。生成は `tools/gen_theorems.py`。

    定理・補題   {n_thm}
    定義・実装   {n_def}
    合計         {n_all}

すべて Lean 4 + Mathlib で受理済み（`sorryAx` なし）。検証は
`python tools/verify.py` が `#print axioms` の出力から確かめる。

順序はソースに現れる順。見出しはモジュール名と各ファイルの `/-! … -/` の区切り
そのものである。

---
"""


def render(src: str) -> str:
    decls = declarations(src)
    thm = sum(1 for d in decls if d['kind'] in ('theorem', 'lemma'))
    dfn = sum(1 for d in decls if d['kind'] in
              ('def', 'abbrev', 'instance', 'structure', 'inductive'))
    full = namespaces(src)
    body = [HEADER.format(n_thm=thm, n_def=dfn, n_all=thm + dfn)]
    seen_head = False
    for d in decls:
        if d['kind'] == 'head':
            hashes = '#' * min(d['level'] + 1, 4)
            body.append(f"\n{hashes} {d['text']}\n")
            seen_head = True
        else:
            if not seen_head:
                body.append('\n## 束の定義（部の区切りより前）\n')
                seen_head = True
            name = full.get(d['name'], d['name'])
            body.append(f"**`{name}`**\n\n```lean\n{d['text']}\n```\n")
    return '\n'.join(body).replace('\n\n\n', '\n\n') + '\n'


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true',
                    help='書き出さずに、最新かどうかだけ見る')
    args = ap.parse_args(argv)
    src = source()
    text = render(src)
    if args.check:
        cur = OUT.read_text() if OUT.exists() else ''
        if cur != text:
            print(f'{OUT.name} が古い。`python tools/gen_theorems.py` で作り直す。')
            return 1
        print(f'{OUT.name} は最新。')
        return 0
    OUT.write_text(text)
    print(f'{OUT.name}: {len(text.splitlines())} 行')
    return 0


if __name__ == '__main__':
    sys.exit(main())
