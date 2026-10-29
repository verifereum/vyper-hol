# F23 — STOP must clear stale callee return data

**Intended maintainer:** Venom execution/halt semantics and codegen simulation.
**Disposition: FIXED here**, TASK023, landed `d76011e1`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

Initial caller state has `vs_returndata=[42w;7w]` left by a completed callee.
Execute **`instruction 0 STOP [] []`** (or a void-return block containing it).
Old `step_inst_base` returned `Halt (halt_state s)`, preserving those two bytes;
EVM STOP calls `set_return_data []` and completes our frame with empty return
bytes. A source function which calls a contract then returns NoneT should
therefore have empty external return bytes, not the prior callee's payload.
Current Venom returns exactly `Halt (halt_state (s with vs_returndata:=[]))`.
This is a literal terminal-state counterexample, not an executed external-call
transaction in this documentation task.

## Current owners, reference and actual prior witnesses

- [Execution](../../venom/defs/venomExecSemanticsScript.sml): STOP arm of
  `step_inst_base`; [state helpers](../../venom/defs/venomStateScript.sml), `halt_state`.
- [Permanent regressions](../../venom/proofs/stopReturndataScript.sml):
  `step_stop_clears_returndata`, `stop_after_callee_returndata`,
  `stop_stale_returndata_counterexample` (negates the old unconditional state equation).
- [Codegen client](../../venom/codegen/proofs/genBlockSimScript.sml):
  STOP halt simulation no longer needs old preexisting-empty-returndata guard.
- [Current return bytes](../../lowering/e2eDefsScript.sml): NoneT returns empty.

Pinned `vyper/codegen_venom/stmt.py`, `Stmt.lower_Return`841ff and
`_lower_external_return`918ff distinguish external void return and STOP;
`vyper/codegen/return_.py`, `make_return_stmt`, branches on function metadata.
This reference code corroborates use of EVM STOP, whose return-data behavior
is the target semantics, not an invented reference interpreter observation.
No separate named original101 fixture is needed for the stale-state witness;
TASK023's actual instruction/block regressions are the concrete affected tests.

## Reproduction and prior rebuilt evidence

Reproduce by reading the old STOP arm with
`git show c587772d:venom/defs/venomExecSemanticsScript.sml`, then the current
three equations with `[42w;7w]`. Read reference external-return dispatch and
historical PLAN's EVM STOP citation. TASK023 receipt records actual rebuilt
instruction/block/counterexample theorems and affected clients; no HOL ran here.
Related **memory/name offsets** and frozen GETFMP witness remain in [F21](F21-fixed-memory-and-names.md),
not renamed F23 defects. STOP clearing is not a proof of source-memory safety.

## Dynamic ABI decode remains a separate exemption, NOT fixed

Official PLAN **F17**, not F23, explains the dynamic decode exemption used by
this milestone. For target String[1], bytes are:
word0x20 (31 zero bytes+20), word1 (31 zero bytes+01), byte61,
**31 bytesFF**. Source strict `valid_enc` rejects dirty padding with
`RuntimeError "abi_decode invalid"`; lowered length/end checks accept "a".
No relaxing of source strict decoder occurred. The old wrap-around Venom-only
example is historical; current pointer checks must be inspected rather than
blindly copied as still live.

Current [source exemption](../../lowering/e2eDefsScript.sml),
`unspecified_behaviour_exempt` / `source_exempt`, exempts decoding only for
**exactly** that error message and a syntactically occurring dynamic ABI decode
target. This decoding exemption is program-wide; static-only invalid decoding
and `"abi_decode conversion"` are not exempt. Separately, the exact runtime error
`"convert empty bytes to signed"` is exempt because stale memory determines the
compiled signed-conversion result for empty bytes. An exempt run lacks result/effect correspondence, although the
top still supplies an actual EVM run. See
[source strict decoder](../../semantics/vyperABIScript.sml),
[lowered decoder](../../lowering/defs/abiEncoderScript.sml),
[dynamic fixture](../../lowering/defs/bytecode/eval/evalCompilerSubsetAbiBuiltinsScript.sml)
and [current audit](../compiler-proof-status-2026-10-09.md).
Pinned reference `vyper/codegen_venom/abi/abi_decoder.py`, `clamp_bytestring`,
checks length/end,
not a source strict-padding predicate; this is static reference evidence only.
Dynamic-decoding general correctness is DEFERRED under D9, not "fixed by STOP".

Historical PLAN: §4.4 F23,849–855; D14 STOP; §5.4 STOP; §6.3.
Old Venom746/EVM1561, `gen_inst_halt_sim`1407. Separate F17 padding at
§4.2 lines758–774/D9; source `valid_enc` contractABIScript967–988.
