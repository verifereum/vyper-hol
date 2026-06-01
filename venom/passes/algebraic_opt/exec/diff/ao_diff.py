#!/usr/bin/env python3
"""
Per-pass differential harness for the Venom algebraic-optimization pass.

Runs ONLY AlgebraicOptimizationPass on a parsed Venom function (isolating it
from every other pass, so a mismatch can be attributed to this pass alone) and
emits the function as JSON both before and after the pass.  The HOL side
imports the "before" JSON, runs `ao_transform_function`, and checks the result
against the "after" JSON modulo internal identity (inst ids).

Operand order is Python's INTERNAL order (`inst.operands`), which is what the
HOL pass model operates on.  Variable names have their leading '%' stripped;
literals are wrapped into [0, 2**256) and emitted as decimal strings.

Usage:
    python3 ao_diff.py <file-or-dir.venom> [<out-dir>]

Each input <name>.venom yields <out-dir>/<name>.json containing
{"name", "before": <fn>, "after": <fn>} per function (a list if several).
Run with the vyper venv and PYTHONPATH pointing at the vyper repo root, e.g.

    PYTHONPATH=/path/to/vyper /path/to/vyper/.venv/bin/python ao_diff.py corpus/
"""
import json
import os
import sys

from tests.venom_utils import parse_from_basic_block
from vyper.venom.analysis import IRAnalysesCache
from vyper.venom.basicblock import IRLabel, IRLiteral, IRVariable
from vyper.venom.passes import AlgebraicOptimizationPass

MASK256 = (1 << 256) - 1


def operand_to_json(op):
    if isinstance(op, IRLiteral):
        return {"lit": str(op.value & MASK256)}
    if isinstance(op, IRVariable):
        return {"var": op.value.lstrip("%")}
    if isinstance(op, IRLabel):
        return {"label": op.value}
    raise TypeError(f"unexpected operand {op!r} of type {type(op).__name__}")


# The HOL IR uses textual/source operand order, which is the REVERSE of
# Python's internal `inst.operands` for every opcode except the ones the
# parser leaves un-reversed (jmp/jnz/djmp/phi) and invoke (label arg fixed,
# rest reversed).  This inverts parser.py's reversal so the serialized order
# matches what the HOL pass expects (HOL op2 = Python operands[0]).
def textual_operands(inst):
    ops = list(inst.operands)
    if inst.opcode == "invoke":
        return [ops[0]] + list(reversed(ops[1:])) if ops else ops
    if inst.opcode in ("jmp", "jnz", "djmp", "phi"):
        return ops
    return list(reversed(ops))


def inst_to_json(inst):
    return {
        "opcode": inst.opcode,
        "operands": [operand_to_json(o) for o in textual_operands(inst)],
        "outputs": [o.value.lstrip("%") for o in inst.get_outputs()],
    }


def bb_to_json(bb):
    return {
        "label": bb.label.value,
        "instructions": [inst_to_json(i) for i in bb.instructions],
    }


def fn_to_json(fn):
    return {"name": fn.name.value, "blocks": [bb_to_json(bb) for bb in fn.get_basic_blocks()]}


def run_ao_on_function(fn):
    ac = IRAnalysesCache(fn)
    AlgebraicOptimizationPass(ac, fn).run_pass()


def diff_source(source: str):
    """Return a list of {name, before, after} records, one per function."""
    pre_ctx = parse_from_basic_block(source)
    befores = {name.value: fn_to_json(fn) for name, fn in pre_ctx.functions.items()}

    post_ctx = parse_from_basic_block(source)
    records = []
    for name, fn in post_ctx.functions.items():
        run_ao_on_function(fn)
        records.append({"name": name.value, "before": befores[name.value], "after": fn_to_json(fn)})
    return records


def process_file(path: str, out_dir: str):
    with open(path) as f:
        source = f.read()
    records = diff_source(source)
    payload = records if len(records) != 1 else records[0]
    base = os.path.splitext(os.path.basename(path))[0]
    out_path = os.path.join(out_dir, base + ".json")
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"wrote {out_path}")


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    target = argv[1]
    out_dir = argv[2] if len(argv) > 2 else (target if os.path.isdir(target) else os.path.dirname(target) or ".")
    os.makedirs(out_dir, exist_ok=True)
    if os.path.isdir(target):
        for name in sorted(os.listdir(target)):
            if name.endswith(".venom"):
                process_file(os.path.join(target, name), out_dir)
    else:
        process_file(target, out_dir)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
