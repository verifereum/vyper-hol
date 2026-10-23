# Focused internal-frame validation

Comparisons use VYPER_PIN `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, optimization
NONE, Prague, experimental codegen and no bytecode metadata. The locked Python
3.11 capture regenerated all 40 supplied programs' 80 AST JSON/hex payloads
byte-for-byte. Instrumented allocation captures called the unmodified original
allocator and asserted deploy/runtime equality with independent oracle outputs
for each of the 15 layout cases below. No oracle bytes came from HOL.

## Runtime eom comparison

These are runtime functions after the callee-first function passes, not constructor
copy-buffer sizes. `entry` denotes Python `runtime` / HOL `__entry`; internal names
are matched by source name, not compiler-generated numeric IDs. Values are bytes.
Each cell is `function: HOL / Python`.

| Source witness | Per-function eom |
|---|---|
| p02_int_local_string | entry: 256 / 256; bar: 128 / 128 |
| p47_len_of_string_call | entry: 128 / 128; f: 0 / 0 |
| p21_for_body_call | entry: 128 / 128; f: 64 / 64 |
| p10_int_diamond | entry: 96 / 96; h: 64 / 64; f: 96 / 96; g: 96 / 96 |
| p09_int_chain | entry: 96 / 96; g: 64 / 64; f: 96 / 96 |
| p74_int_ext_call | entry: 160 / 160; f: 160 / 160 |
| p41_int_local_and_call | entry: 96 / 96; g: 64 / 64; f: 96 / 96 |
| p58_int_bytes_local | entry: **256 / 320**; f: **128 / 192** |
| p45_for_body_call_loopvar | entry: 128 / 128; f: 64 / 64 |
| p62_for_body_call_clobber | entry: 128 / 128; f: 64 / 64 |
| p51_augassign_call | entry: 96 / 96; f: 64 / 64 |
| p11_int_deep | entry: 160 / 160; d: 64 / 64; c: 96 / 96; b: 128 / 128; a: 160 / 160 |
| p44_int_for_calls_int | entry: 64 / 64; g: 32 / 32; f: 64 / 64 |
| p60_int_view_reads_and_local | entry: 128 / 128; f: 96 / 96 |
| p108_int_halt_region_invoke_loop | entry: 96 / 96; f: 96 / 96; g: 32 / 32 |

37 of 39 function sizes agree. P58's pinned pre-allocation `f` has four 64-byte
allocations: return buffer, concat output, concat running-offset memory temporary,
and local. HOL uses three 64-byte allocations and carries the running offset in
SSA. Thus the input IR already differs before memory allocation (#566); the
64-byte frame difference is propagated to the caller. This is not a claim of
allocation-order equivalence for these different input IRs. The old flat-copy
classification from #549 does not apply to the now-matching p02/p47.

## P108 cleanup and placement

The exact `p108_int_halt_region_invoke_loop` source is the fenced program in
public issue #546, not a reconstruction from a shape description. Both checker
modes accept it; `supported_program` remains false. Both runtime bytecodes are
230 bytes, but are **not equal**:

* HOL places `f` at runtime offset `0x65`, then `g` at `0xa3`.
* Python places `g` at `0x65`, then `f` at `0xa4`.
* `f` occupies 62 bytes and `g` 63 bytes on each side. After matching those regions
  and relocating their PUSH2 jump destinations, the instruction sequences agree.
* Both retain the three cleanup POPs in `f`'s invoke-then-revert branch (HOL
  `0x94`, Python `0xd3`): `g` has a reachable CFG loop, so no cleanup promise is
  available for that region. The shared revert stub stays at `0xe2`.

All three frame sizes agree. The remaining difference is #546 function placement,
not a missing POP or changed memory frame. No #546 ordering implementation is
included here, and P108 is not added to the 34/40 MATCH count.

## P39/P40 behavior provenance

`check_behavior.py` executes each runtime in a fresh PragueVM with zero initial
storage, zero call value, gas 1,000,000, sender/origin `0x01` repeated 20 times and
recipient `0x02` repeated 20 times. Calldata is the selector of `foo(uint256)` plus
ABI-encoded 5. Captures used py-evm 0.12.1b1 and eth-abi 6.0.0, separately for the
pinned Python output and normative HOL output:

| Witness | Runtime bytes | Python return / slot 0 | HOL return / slot 0 |
|---|---:|---|---|
| p39_int_local_clobber | 133 | 5 / 6 | 5 / 6 |
| p40_int_for_clobber | 195 | 5 / 11 | 5 / 11 |

The permanent HOL fixture equalities establish the same pinned runtime bytes
after the allocation-order repair. The `.hex` file SHA256 values in
`oracle/provenance.json` are `aa7b604cbece2e3e26a8158f288105756eb2ce359440cd35b5dc80db9196d85e`
(p39) and `b05228ea196bca0b6b87de1d7e72b32b7ff491e972678b951ad45bb73b8b5c59`
(p40). Reproduce the pinned-byte behavior check from the repository root:

```text
uv run --with py-evm==0.12.1b1 --with eth-abi==6.0.0 python lowering/defs/bytecode/internal-frames/check_behavior.py Vyper lowering/defs/bytecode/internal-frames/oracle
```

The same script accepts a directory of independently exported HOL `.hex` files;
it does not generate or replace oracle outputs.

## Limits

The focused CI/core/proof and permanent fixture checks are reported in README.md.
The remaining six results among the supplied 40 programs are p43b, p57, p58 and
rc28 bytecode residuals, and rc23/rc27 compile-NONE. Their current source-level
causes are described there. Baseline proof admissions remain explicitly reported;
a clean focused build is not a claim that the entire compiler has no admissions.

Exact p106/e01/e02/p107 sources and the historical existing-MATCH control inventory
listed in README.md are still unavailable here. No named equality is inferred from
similar source shapes. No full-project or full-parity rollup build was performed.
