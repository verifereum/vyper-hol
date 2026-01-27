#!/usr/bin/env python3
"""Export Venom IR (before/after a selected pass) from trace JSON.

Usage:
  scripts/venom_ir_export.py --config venom/tests/pass_trace_config.json

  scripts/venom_ir_export.py --pass algebraic_optimization \
    --json tests/vyper-test-exports/unit/ast/nodes/test_fold_compare.json \
    --out venom/tests/venom-ir-export --limit 5

Notes:
  - Uses a local Vyper checkout via sys.path.
  - Set VYPER_ROOT if the checkout is not at ./vyper.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any, Iterable
import sys

ROOT = Path(__file__).resolve().parents[1]
VYPER_ROOT = Path(os.getenv("VYPER_ROOT", ROOT.parent / "vyper"))
if not VYPER_ROOT.exists():
    raise SystemExit(
        f"Vyper checkout not found at {VYPER_ROOT}. "
        "Set VYPER_ROOT or clone Vyper at ./vyper."
    )
if str(VYPER_ROOT) not in sys.path:
    sys.path.insert(0, str(VYPER_ROOT))

from vyper.compiler.phases import CompilerData
from vyper.compiler.settings import OptimizationLevel, Settings
from vyper.venom.analysis.analysis import IRAnalysesCache
from vyper.venom.analysis.dfg import DFGAnalysis
from vyper.venom.analysis.liveness import LivenessAnalysis
from vyper.venom.basicblock import (
    IRBasicBlock,
    IRInstruction,
    IRLabel,
    IRLiteral,
    IROperand,
    IRVariable,
)
from vyper.venom.ir_node_to_venom import ir_node_to_venom
from vyper.venom.passes import FloatAllocas, MakeSSA, PhiEliminationPass, SimplifyCFGPass
from vyper.venom.passes.algebraic_optimization import (
    AlgebraicOptimizationPass,
    TRUTHY_INSTRUCTIONS,
)
from vyper.venom.passes.base_pass import InstUpdater

UINT256_MOD = 1 << 256


def _opcode_to_hol(op: str) -> str:
    if op == "div":
        return "Div"
    if op == "mod":
        return "Mod"
    return op.upper()


def _lit_to_hex(val: int) -> str:
    n = val % UINT256_MOD
    return hex(n)


def _encode_operand(op) -> dict[str, str]:
    if isinstance(op, IRLiteral):
        return {"lit": _lit_to_hex(op.value)}
    if isinstance(op, IRVariable):
        return {"var": op.name}
    if isinstance(op, IRLabel):
        return {"label": op.value}
    raise TypeError(f"unknown operand: {op} ({type(op)})")


def _encode_instruction(
    inst: IRInstruction, inst_id: int, hints: dict[str, bool] | None = None
) -> dict[str, Any]:
    payload = {
        "id": inst_id,
        "opcode": _opcode_to_hol(inst.opcode),
        "operands": [_encode_operand(op) for op in inst.operands],
        "outputs": [inst.output.name] if inst.output is not None else [],
    }
    if hints is not None:
        payload["hints"] = hints
    return payload


def _encode_block(
    bb: IRBasicBlock,
    next_id: int,
    inst_refs: list[tuple[IRInstruction, dict[str, Any]]] | None = None,
) -> tuple[dict[str, Any], int]:
    insts = []
    inst_id = next_id
    for inst in bb.instructions:
        inst_dict = _encode_instruction(inst, inst_id)
        if inst_refs is not None:
            inst_refs.append((inst, inst_dict))
        insts.append(inst_dict)
        inst_id += 1
    return {
        "label": bb.label.value,
        "instructions": insts,
    }, inst_id


def _encode_function(
    fn, inst_refs: list[tuple[IRInstruction, dict[str, Any]]] | None = None
) -> dict[str, Any]:
    blocks = []
    inst_id = 0
    for bb in fn.get_basic_blocks():
        enc, inst_id = _encode_block(bb, inst_id, inst_refs=inst_refs)
        blocks.append(enc)
    return {
        "name": fn.name.value,
        "blocks": blocks,
    }


class AlgebraicOptimizationPassWithHints(AlgebraicOptimizationPass):
    def __init__(self, analyses_cache, function):
        super().__init__(analyses_cache, function)
        self.hints: dict[IRInstruction, dict[str, bool]] = {}

    def run_pass(self):
        # Single algebraic pass + offset lowering; ignore iszero-chain.
        self.dfg = self.analyses_cache.request_analysis(DFGAnalysis)
        self.updater = InstUpdater(self.dfg)
        self._handle_offset()
        self._algebraic_opt()
        self.analyses_cache.invalidate_analysis(LivenessAnalysis)

    def _handle_inst_peephole(self, inst: IRInstruction):
        if inst.output is None or inst.is_volatile or inst.opcode == "assign" or inst.is_pseudo:
            return super()._handle_inst_peephole(inst)

        uses = self.dfg.get_uses(inst.output)
        is_truthy = all(i.opcode in TRUTHY_INSTRUCTIONS for i in uses)
        prefer_iszero = all(i.opcode in ("assert", "iszero") for i in uses)

        self.hints.setdefault(inst, {})
        self.hints[inst]["is_truthy"] = is_truthy
        self.hints[inst]["prefer_iszero"] = prefer_iszero

        return super()._handle_inst_peephole(inst)

    def _optimize_comparator_instruction(self, inst, prefer_iszero):
        cmp_flip = False
        if inst.output is not None:
            uses = self.dfg.get_uses(inst.output)
            if len(uses) == 1:
                after = uses.first()
                if after.opcode in ("iszero", "assert"):
                    if after.opcode == "iszero":
                        n_uses = self.dfg.get_uses(after.output)
                        if len(n_uses) == 1 and n_uses.first().opcode != "assert":
                            cmp_flip = True
                    else:
                        cmp_flip = True

        if not isinstance(inst.operands[0], IRLiteral):
            cmp_flip = False

        self.hints.setdefault(inst, {})
        self.hints[inst]["cmp_flip"] = cmp_flip
        self.hints[inst]["prefer_iszero"] = prefer_iszero

        return super()._optimize_comparator_instruction(inst, prefer_iszero)

def _run_prepasses(ac, fn) -> None:
    FloatAllocas(ac, fn).run_pass()
    SimplifyCFGPass(ac, fn).run_pass()
    MakeSSA(ac, fn).run_pass()
    PhiEliminationPass(ac, fn).run_pass()


def _run_algebraic_opt_with_hints(fn) -> AlgebraicOptimizationPassWithHints:
    ac = IRAnalysesCache(fn)
    _run_prepasses(ac, fn)
    opt = AlgebraicOptimizationPassWithHints(ac, fn)
    opt.run_pass()
    return opt


def _run_simple_pass(pass_cls, fn):
    ac = IRAnalysesCache(fn)
    _run_prepasses(ac, fn)
    p = pass_cls(ac, fn)
    p.run_pass()
    return p


PASS_REGISTRY: dict[str, dict[str, Any]] = {
    "algebraic_optimization": {
        "runner": _run_algebraic_opt_with_hints,
        "hints": True,
    },
}


def _iter_trace_sources(json_path: Path) -> Iterable[tuple[str, str]]:
    data = json.loads(json_path.read_text())
    for test_name, test in data.items():
        traces = test.get("traces", [])
        for i, tr in enumerate(traces):
            src = tr.get("source_code")
            if not isinstance(src, str) or src.strip() == "":
                continue
            yield f"{test_name}::trace{i}", src


def _compile_to_venom_ctx(source_code: str):
    settings = Settings(experimental_codegen=True, optimize=OptimizationLevel.GAS)
    data = CompilerData(source_code, settings=settings)
    ir_runtime = data.ir_runtime
    return ir_node_to_venom(ir_runtime)


def export_from_trace_file(
    json_path: Path, out_dir: Path, limit: int | None, pass_name: str
) -> int:
    out_dir.mkdir(parents=True, exist_ok=True)
    count = 0
    for name, src in _iter_trace_sources(json_path):
        if limit is not None and count >= limit:
            break
        try:
            ctx = _compile_to_venom_ctx(src)
        except Exception as e:  # pragma: no cover - best effort
            print(f"[skip] {name}: compile failed: {e}")
            continue

        functions = []
        for fn in ctx.get_functions():
            try:
                inst_refs: list[tuple[IRInstruction, dict[str, Any]]] = []
                before_enc = _encode_function(fn, inst_refs=inst_refs)
                spec = PASS_REGISTRY.get(pass_name)
                if spec is None:
                    raise ValueError(
                        f"unknown pass '{pass_name}' (available: {', '.join(PASS_REGISTRY)})"
                    )
                runner = spec["runner"]
                opt = runner(fn)
                after_enc = _encode_function(fn)
                for inst, inst_dict in inst_refs:
                    if spec.get("hints"):
                        hints = opt.hints.get(inst, {})
                        inst_dict["hints"] = {
                            "prefer_iszero": hints.get("prefer_iszero", False),
                            "is_truthy": hints.get("is_truthy", False),
                            "cmp_flip": hints.get("cmp_flip", False),
                        }
                    else:
                        inst_dict["hints"] = {
                            "prefer_iszero": False,
                            "is_truthy": False,
                            "cmp_flip": False,
                        }
            except Exception as e:  # pragma: no cover - best effort
                print(f"[skip] {name}::{fn.name.value}: pass failed: {e}")
                continue
            functions.append(
                {
                    "name": fn.name.value,
                    "before": before_enc,
                    "after": after_enc,
                    "iszero_subst": [],
                }
            )

        payload = {
            "test": name,
            "pass": pass_name,
            "functions": functions,
        }

        out_path = out_dir / ("venom_" + _sanitize_filename(name) + ".json")
        out_path.write_text(json.dumps(payload, indent=2))
        count += 1
        print(f"[ok] {out_path}")
    return count


def _sanitize_filename(s: str) -> str:
    keep = []
    for ch in s:
        if ch.isalnum() or ch in ("-", "_", "."):
            keep.append(ch)
        else:
            keep.append("_")
    return "".join(keep)[:150]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--pass",
        dest="pass_name",
        default="algebraic_optimization",
        help="pass to run (default: algebraic_optimization)",
    )
    ap.add_argument("--config", help="path to pass trace export config")
    ap.add_argument("--json", action="append", help="path to test json (repeatable)")
    ap.add_argument("--root", default="tests/vyper-test-exports", help="root to scan for json")
    ap.add_argument(
        "--out",
        default="venom/tests/venom-ir-export",
        help="output root directory",
    )
    ap.add_argument("--limit", type=int, default=5, help="limit traces per file")
    args = ap.parse_args()

    out_root = Path(args.out)

    def iter_json_files(root: Path | None, extra: list[Path]) -> list[Path]:
        files = list(extra)
        if root is not None and root.exists():
            files.extend(root.rglob("*.json"))
        unique = {p.resolve() for p in files}
        return sorted(unique)

    total = 0
    if args.config:
        config_path = Path(args.config)
        data = json.loads(config_path.read_text())
        if not isinstance(data, dict):
            raise ValueError("config must be an object mapping pass -> options")
        for pass_name, entry in data.items():
            if pass_name not in PASS_REGISTRY:
                print(f"[skip] unknown pass '{pass_name}' in config")
                continue
            if not isinstance(entry, dict):
                print(f"[skip] config entry for '{pass_name}' must be an object")
                continue
            json_list = [Path(p) for p in entry.get("json", [])]
            root_opt = entry.get("root")
            root = Path(root_opt) if root_opt else None
            limit = entry.get("limit", args.limit)
            out_dir = out_root / pass_name
            if root is None and not json_list:
                print(f"[skip] no json/root configured for pass '{pass_name}'")
                continue
            for jp in iter_json_files(root, json_list):
                if not jp.exists():
                    print(f"[skip] missing {jp}")
                    continue
                total += export_from_trace_file(jp, out_dir, limit, pass_name)
    else:
        json_files: list[Path] = []
        if args.json:
            json_files = [Path(p) for p in args.json]
            root = None
        else:
            root = Path(args.root)
        out_dir = out_root / args.pass_name
        for jp in iter_json_files(root, json_files):
            if not jp.exists():
                print(f"[skip] missing {jp}")
                continue
            total += export_from_trace_file(jp, out_dir, args.limit, args.pass_name)

    print(f"exported {total} trace(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
