#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CaseSpec:
    family: str
    name: str
    depth: int
    deletes: int = 0


def clause(*lits: int) -> str:
    return " ".join(str(l) for l in lits) + " 0\n"


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def gen_up_chain(depth: int) -> tuple[str, str]:
    clauses = [clause(-1)]
    for v in range(1, depth):
        clauses.append(clause(v, -(v + 1)))
    clauses.append(clause(depth))
    formula = [
        f"p cnf {depth} {len(clauses)}\n",
        "e " + " ".join(str(v) for v in range(1, depth + 1)) + " 0\n",
        *clauses,
    ]
    return "".join(formula), ""


def gen_rup_twochain(depth: int) -> tuple[str, str]:
    left = list(range(2, depth + 2))
    right = list(range(depth + 2, 2 * depth + 2))
    clauses = [clause(-1, left[0])]
    for i in range(depth - 1):
        clauses.append(clause(-left[i], left[i + 1]))
    clauses.append(clause(-left[-1], -1))
    clauses.append(clause(1, right[0]))
    for i in range(depth - 1):
        clauses.append(clause(-right[i], right[i + 1]))
    clauses.append(clause(-right[-1], 1))
    max_var = right[-1]
    formula = [
        f"p cnf {max_var} {len(clauses)}\n",
        "e " + " ".join(str(v) for v in range(1, max_var + 1)) + " 0\n",
        *clauses,
    ]
    return "".join(formula), clause(-1)


def gen_delete_rup(depth: int, deletes: int) -> tuple[str, str]:
    left = list(range(2, depth + 2))
    right = list(range(depth + 2, 2 * depth + 2))
    duplicate = (1, right[0])
    clauses = [clause(-1, left[0])]
    for i in range(depth - 1):
        clauses.append(clause(-left[i], left[i + 1]))
    clauses.append(clause(-left[-1], -1))
    for _ in range(deletes + 1):
        clauses.append(clause(*duplicate))
    for i in range(depth - 1):
        clauses.append(clause(-right[i], right[i + 1]))
    clauses.append(clause(-right[-1], 1))
    max_var = right[-1]
    formula = [
        f"p cnf {max_var} {len(clauses)}\n",
        "e " + " ".join(str(v) for v in range(1, max_var + 1)) + " 0\n",
        *clauses,
    ]
    return "".join(formula), "".join(f"d {duplicate[0]} {duplicate[1]} 0\n" for _ in range(deletes)) + clause(-1)


def make_case(spec: CaseSpec) -> tuple[str, str]:
    if spec.family == "up_chain":
        return gen_up_chain(spec.depth)
    if spec.family == "rup_twochain":
        return gen_rup_twochain(spec.depth)
    if spec.family == "delete_rup":
        return gen_delete_rup(spec.depth, spec.deletes)
    raise ValueError(f"unknown family: {spec.family}")


def specs_for_profile(profile: str) -> list[CaseSpec]:
    if profile == "quick":
        return [
            CaseSpec("up_chain", "up_chain_00032", 32),
            CaseSpec("up_chain", "up_chain_00256", 256),
            CaseSpec("rup_twochain", "rup_twochain_00032", 32),
            CaseSpec("rup_twochain", "rup_twochain_00256", 256),
            CaseSpec("delete_rup", "delete_rup_00032_d0064", 32, 64),
            CaseSpec("delete_rup", "delete_rup_00256_d1000", 256, 1000),
        ]
    return [
        CaseSpec("up_chain", "up_chain_00032", 32),
        CaseSpec("up_chain", "up_chain_00064", 64),
        CaseSpec("up_chain", "up_chain_00128", 128),
        CaseSpec("up_chain", "up_chain_00256", 256),
        CaseSpec("up_chain", "up_chain_00512", 512),
        CaseSpec("up_chain", "up_chain_01024", 1024),
        CaseSpec("up_chain", "up_chain_02048", 2048),
        CaseSpec("up_chain", "up_chain_04096", 4096),
        CaseSpec("up_chain", "up_chain_08192", 8192),
        CaseSpec("rup_twochain", "rup_twochain_00016", 16),
        CaseSpec("rup_twochain", "rup_twochain_00032", 32),
        CaseSpec("rup_twochain", "rup_twochain_00064", 64),
        CaseSpec("rup_twochain", "rup_twochain_00128", 128),
        CaseSpec("rup_twochain", "rup_twochain_00256", 256),
        CaseSpec("rup_twochain", "rup_twochain_00512", 512),
        CaseSpec("rup_twochain", "rup_twochain_01024", 1024),
        CaseSpec("delete_rup", "delete_rup_00016_d0016", 16, 16),
        CaseSpec("delete_rup", "delete_rup_00032_d0064", 32, 64),
        CaseSpec("delete_rup", "delete_rup_00064_d0256", 64, 256),
        CaseSpec("delete_rup", "delete_rup_00128_d0512", 128, 512),
        CaseSpec("delete_rup", "delete_rup_00256_d0768", 256, 768),
        CaseSpec("delete_rup", "delete_rup_00512_d0960", 512, 960),
        CaseSpec("delete_rup", "delete_rup_01024_d1000", 1024, 1000),
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate deterministic synthetic DQDIMACS/DQRAT benchmark pairs.")
    parser.add_argument("--out", type=Path, required=True, help="output directory")
    parser.add_argument("--profile", choices=("quick", "full"), default="full", help="case set to generate")
    args = parser.parse_args()

    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    specs = specs_for_profile(args.profile)

    manifest_path = out / "manifest.tsv"
    with manifest_path.open("w", encoding="utf-8", newline="") as manifest_file:
        writer = csv.writer(manifest_file, delimiter="\t")
        writer.writerow(
            [
                "case",
                "family",
                "depth",
                "deletes",
                "max_var",
                "formula_clauses",
                "proof_steps",
                "formula_path",
                "proof_path",
                "formula_bytes",
                "proof_bytes",
            ]
        )

        for spec in specs:
            formula_text, proof_text = make_case(spec)
            family_dir = out / spec.family
            formula_path = family_dir / f"{spec.name}.dqdimacs"
            proof_path = family_dir / f"{spec.name}.dqrat"
            write_text(formula_path, formula_text)
            write_text(proof_path, proof_text)

            formula_lines = [line for line in formula_text.splitlines() if line and line[0] not in {"p", "e", "a", "d", "c"}]
            proof_steps = len([line for line in proof_text.splitlines() if line.strip()])
            max_var = 0
            for tok in formula_text.split():
                if tok.lstrip("-").isdigit():
                    max_var = max(max_var, abs(int(tok)))

            writer.writerow(
                [
                    spec.name,
                    spec.family,
                    spec.depth,
                    spec.deletes,
                    max_var,
                    len(formula_lines),
                    proof_steps,
                    formula_path.relative_to(out),
                    proof_path.relative_to(out),
                    formula_path.stat().st_size,
                    proof_path.stat().st_size,
                ]
            )

    readme = out / "README.md"
    write_text(
        readme,
        "\n".join(
            [
                "# Synthetic DQDIMACS/DQRAT Benchmarks",
                "",
                "This directory was generated by `scripts/generate_synthetic_benchmarks.py`.",
                "",
                "Families:",
                "- `up_chain`: unit-propagation-unsat formulas with empty proofs.",
                "- `rup_twochain`: nontrivial propositional unsat formulas certified by one RUP unit clause.",
                "- `delete_rup`: the same RUP core plus many clause deletions to stress proof-stream handling.",
                "",
                f"Profile: `{args.profile}`",
                f"Cases: `{len(specs)}`",
                "",
                "See `manifest.tsv` for the full case list and file sizes.",
                "",
            ]
        ),
    )


if __name__ == "__main__":
    main()
