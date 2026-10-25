# Reachable immutable padding probe (C1.6.8)

The accompanying `immutableReachableProbeScript.sml` has no admissions and checks
its saved theorem oracle tags. This is a counterexample to canonical staging in
the **current HOL compiler's lowered constructor**, not a claimed Verifereum
transaction counterexample or a pinned-Python parity result.

The dirty source is equivalent to:

```vyper
X: immutable(String[40])

@deploy
def __init__():
    b: String[1] = "b"
    X = "a"

@external
def get() -> String[40]:
    return X
```

The clean source omits `b`. Both deploy/runtime `check_contract` checks accept;
both constructors satisfy `constructor_call_free`. The literal annotation is
String[40], as required by the checker. `lowered_value_type` nevertheless gives
the produced bound String[1], so its allocation is 64 bytes. An earlier test
using a genuinely String[1] local assigned to X was rejected by the deploy
checker (exact type equality); it is NOT the final counterexample.

## Checked execution

* Resolve `o1_policy all_capabilities`, with finalizer `K SOME`.
* Lower and compile the actual runtime: 250 bytes.
* Lower deploy using those runtime bytes; run the exact O1 pipeline (all three
  optional check callbacks K T, as in `compile_vyper`). All stages succeed.
* Execute that complete context with `run_context 20`, starting from
  `init_venom_state "__deploy"` (in particular empty memory). `vs_code` supplies
  the actual runtime data, with `runtime_begin` mapped to its start at zero.
  This is an abstract Venom code/data-label environment, not the concrete EVM
  deploy code layout. No arbitrary allocation map or memory seed is supplied.
* Execution halts normally. Its returned bytes are the 250 runtime bytes plus
  a 96-byte section. The first 64 section bytes encode the length 1 and "a".
  The last word is **1**, not zero. The clean constructor instead returns the
  canonical encoding (checked separately with empty runtime data).

`padding_probe_source_slice` executes the actual entry-block instruction prefix
up to its first immutable store. The source is at 96 and its entire 96-byte read
slice is the first64 canonical bytes followed by word1. The actual allocation
certificate shows instruction15 is a 64-byte ALLOCA in lowering and ASSIGN96 in
the O1 result. Earlier b-literal/copy temporaries at96 and160 leave the copied
length word at160. Allocation reuse then puts the final a-literal at96 without
clearing160. The unrolled immutable store reads offsets96,128,160. The deploy
epilogue copies all96 staged bytes, preserving the noncanonical last word.

## Limits of the result

The kernel-closed inequalities disprove the proposed universal canonical-byte
staging claim for reachable compiled lowering executions. They do not alone
instantiate every hypothesis of e2e_deploy_correctness. No concrete EVM CREATE
execution, source load_contract execution, pinned-Python compilation or bytecode
parity comparison has been performed here. No claim is made that these two
different programs refute *every* possible value-only function (a same-program
pair would be needed). The fixed zero-padding encoder already used in the PLAN
is directly contradicted by the dirty execution.

No lowering/specification was repaired to remove this observation. Parent
canonical-staging work must remain gated for strategist/owner disposition.

## Pinned-Vyper follow-up (2026-10-23)

The original Alan run ended before Python parity validation. The companion
[`immutable_padding_probe.py`](../defs/bytecode/immutable_padding_probe.py)
now independently compiles the clean and dirty sources with Vyper 0.5.0a4,
commit cd74ce4f, optimization NONE, experimental code generation, Prague,
and no bytecode metadata. It executes the constructor bytecode in py-evm
0.12.1b1's Prague VM, then executes `get()` on the returned code.

| Constructor | Deploy bytes | Runtime bytes | Section bytes | Last section word | `get()` |
| --- | ---: | ---: | ---: | ---: | --- |
| Clean | 362 | 250 | 96 | 0 | `"a"` |
| Dirty | 463 | 250 | 96 | 1 | `"a"` |
| Conditional, `dirty = false` | 525 | 250 | 96 | 0 | `"a"` |
| Conditional, `dirty = true` | 525 | 250 | 96 | 1 | `"a"` |

The script also checks the required `p23_imm_uint256` fixture: the 125-byte
constructor returns the 82-byte runtime followed by the 32-byte encoding of
42, and calling the returned code's `get()` returns 42.

The conditional source replaces the constructor with:

```vyper
@deploy
def __init__(dirty: bool):
    b: String[1] = "b" if dirty else ""
    X = "a"
```

The two executions of this **same program** have the same final immutable
value `X = "a"`, but different returned section bytes. Both have identical
first 64 section bytes, encoding length 1 and `"a"`. This contradicts any
unique section-byte function of only `tops` and the final immutable values,
not just the particular zero-padding encoder. The constructor argument and
local `b` are not immutable declarations.

Reproduce from the repository root, substituting the pinned Vyper interpreter:

```sh
uv run --with py-evm==0.12.1b1 python \
  lowering/defs/bytecode/immutable_padding_probe.py \
  --vyper-python /path/to/pinned-vyper/bin/python
```

The script asserts the section length, runtime prefix, semantic return value,
and the four padding outcomes. Constructor arguments are appended to the
deploy bytecode, as required by Vyper's constructor ABI. These are actual EVM
bytecode executions, but they bypass CREATE transaction/account installation;
they are not a kernel-checked source `load_contract` or e2e theorem instance.
The new Python result establishes the behavior of pinned Vyper; the HOL probe
above independently establishes the reachable lowering behavior. Exact HOL
versus Python deployment-byte parity has not been checked by these probes.

The task's exact installed-code specification therefore needs an explicit
representation of actual padding bytes (with a value-decoding relation), or
a compiler behavior change that sacrifices pinned-Vyper bytecode parity.
The user approved the former on 2026-10-23. The revised boundary is
`immutables_section_rel tops imms section`; the original deterministic
encoder is retained as a possible canonical witness. This releases the old
canonical-staging design gate, while preserving the remaining proof and
parity requirements.
