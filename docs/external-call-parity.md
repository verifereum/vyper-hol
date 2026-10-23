# External-call differential results

All 25 sources now match the pinned Vyper bytecode exactly. Before the fix, 18
of them differed. The sources are the 21 single-module sources and 4
multi-module probes from
[issue #555](https://github.com/verifereum/vyper-hol/issues/555). The fixes
cover five parts of one external call:

- **a06-03:** the selector is hashed from the call-site signature.
- **a06-04:** the result buffer has the memory size of the return type.
- **a06-05:** the decode `ADD` uses Vyper's operand order.
- **a06-09:** a composite `default_return_value` is materialized and stored
  with its type.
- **a06-10:** interface constructors are translated to `Acc Address`.

The stock HOL contract checker accepted every source in both deployment and
runtime modes. The multi-module probes were accepted both on the full module
list and on the main module alone.

The oracle is Vyper `0.5.0a4+cd74ce4f+commit.cd74ce4f`, pinned by `VYPER_PIN`.
It was built with experimental codegen, no optimization, the Prague EVM version,
and bytecode metadata disabled. The 23 retained JSON/bytecode fixtures in
`lowering/defs/bytecode/external-calls/oracle` and their dependency provenance
reproduce byte for byte with `prepare --corpus external-calls --check`. The
diagnostic probes used holbuild 0.11.4 with the stock checker and EVAL libraries
and the existing finite-map compset. No compiler evaluator substitution was
used.

**Baseline column.** These values are quoted from the probes recorded in issue
#555. Single-module sources were probed at `e260a297`. The multi-module sources
(`m*`) were probed at `0273aab9`. For `i09` and `c03`, the issue used a
throwaway checker fix (`account_item_type_def`, since landed in #576). With the
stock checker of that time their verdict was `CHECKER_REJECTS_REAL_ACCEPTS`.

**After column.** Measured on this branch, after all five parts and the
whitelist change, with the probe in `memory_store_witnesses.py`.

**Reading the cells.** `MATCH` means the deployment and runtime bytes are both
identical. A difference cell shows the HOL/Vyper runtime lengths and the first
differing runtime byte (zero-based). Whitelist membership (`supported_program`)
is given as baseline → after. It does not decide whether a source is compiled.
`P` marks the sources in `parity-fixtures.txt`, which have checked theorems
in `evalCompilerExternalCalls`.

| Source | Part | Whitelist | Baseline | After |
|---|---|---|---|---|
| `i15_iface_ret_iface_direct` P | a06-10 | T → T | 219/218 B, rt@54 | MATCH (218 B) |
| `i09_iface_ret_iface` P | a06-10 | T → T | 224/223 B, rt@54 | MATCH (223 B) |
| `c03_iface_address_attr` P | control (a06-10) | T → T | MATCH | MATCH (103 B) |
| `i02_iface_default_param` P | a06-03 | F → T | 207/207 B, rt@87 | MATCH (207 B) |
| `i03_two_ifaces_same_name` P | a06-03 | F → T | 209/209 B, rt@89 | MATCH (209 B) |
| `i13_ext_fn_before_iface` P | a06-03 | F → T | 207/207 B, rt@87 | MATCH (207 B) |
| `i01_name_clash_ext` | control (a06-03) | T → T | MATCH | MATCH (207 B) |
| `e04_ret_string` P | a06-04 | F → T | 367/365 B, rt@54 | MATCH (365 B) |
| `e05_ret_bytes` P | a06-04 | F → T | 365/363 B, rt@54 | MATCH (363 B) |
| `e06_ret_dynarray` | control (a06-04) | F → T | MATCH | MATCH (387 B) |
| `e09_ret_tuple_dyn` | control (a06-04) | F → T | MATCH | MATCH (379 B) |
| `e21_default_ret` P | a06-05 | F → T | 221/221 B, rt@182 | MATCH (221 B) |
| `e22_static_default` P | a06-05 | F → T | 220/220 B, rt@181 | MATCH (220 B) |
| `e29_default_ret_skip` P | a06-05 | F → T | 228/228 B, rt@197 | MATCH (228 B) |
| `e32_default_effect_extcall` | a06-05 | F → F | 319/319 B, rt@281 | MATCH (319 B) |
| `e34_default_effect_internal` | a06-05 | F → F | 259/259 B, rt@197 | MATCH (259 B) |
| `e30_default_ret_tuple` P | a06-09, a06-05 | F → F | 275/283 B, rt@54 | MATCH (283 B) |
| `e37_default_ret_string` P | a06-09, a06-04, a06-05 | F → T | 439/529 B, rt@53 | MATCH (529 B) |
| `e38_default_ret_local_array` P | a06-09, a06-05 | F → F | 305/313 B, rt@54 | MATCH (313 B) |
| `ctl_interface_calls` | control (corpus copy) | T → T | MATCH | MATCH (496 B) |
| `ctl_external_struct` | control (corpus copy) | T → T | MATCH | MATCH (173 B) |
| `m09_iface_extcall` | a06-03 (imported `.vy`) | F → T | 287/295 B, rt@54 | MATCH (295 B) |
| `m11_vyi_iface` | a06-03 (imported `.vyi`) | F → T | 219/223 B, rt@54 | MATCH (223 B) |
| `m12_erc20_extcall` | a06-03 (builtin `IERC20`) | F → T | 261/265 B, rt@54 | MATCH (265 B) |
| `m51_erc165_staticcall` | a06-03 (builtin `IERC165`) | F → T | 244/248 B, rt@54 | MATCH (248 B) |

The whitelist widening has three parts:

- **Any interface.** `supported_external_call_signature` and
  `supported_interface_method` are deleted. Calls through any interface are
  admitted, including imported and builtin interfaces.
- **Any value return.** `supported_external_return_type tops` is now
  `supported_value_type tops`.
- **Literal or name defaults.** `default_return_value` was admitted when it
  was a literal or a name. Since
  [#553](https://github.com/verifereum/vyper-hol/issues/553) (a06-07) the
  default is an ordinary operand: the semantics evaluates it before the call,
  in source order, as the lowering does, so any pure default is admitted.

The whitelist columns were measured before that change. `e32` and `e34` have
effectful defaults and stay outside the whitelist, since every external-call
operand must be pure. `e38` initializes a local array from a list literal,
which the statement whitelist does not admit.

The multi-module sources import `libp.vy` (`interface IFoo` with
`foo(uint256) -> uint256: view` and `bar(uint256): nonpayable`) and `ifoo.vyi`
(`foo(uint256) -> uint256`, view). The issue does not include these two files.
The versions used here give the same Vyper runtime lengths as the issue's
probes. The multi-module sources are probe-only: they have no committed
fixtures, because the witness library compiles single-module exports.

## Keyword operands

These sources cover the keyword operands of an external call and `send`
(#553); `e19_gas_kw` and `s02_send_gas` are the issue's witnesses. All match
the pinned Vyper bytecode exactly. Each is in `parity-fixtures.txt`, with a
checked theorem in `evalCompilerExternalCallKwargs`; `e29_default_ret_skip`
above also has one there.

| Source | What it covers | After |
|---|---|---|
| `e19_gas_kw` | extcall with a literal `gas=50000` | MATCH (196 B) |
| `e40_extcall_gas` | extcall with `gas=` | MATCH (242 B) |
| `e41_staticcall_gas` | staticcall with `gas=` | MATCH (239 B) |
| `e42_extcall_gas_value_order` | `gas=` before `value=`, lowered in source order | MATCH (256 B) |
| `e43_extcall_all_kwargs` | `value=`, `default_return_value=`, `gas=` | MATCH (304 B) |
| `e44_skip_contract_check` | void extcall with `skip_contract_check=True`: no `extcodesize` check | MATCH (169 B) |
| `e45_default_ret_ifexp` | a conditional-expression default | MATCH (291 B) |
| `s01_send` | `send` without `gas=` | MATCH (118 B) |
| `s02_send_gas` | `send(r, msg.value, gas=2300)` | MATCH (107 B) |

To reproduce, generate the oracle with the pinned Python environment, then run
`probe` in the worktree being tested:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus external-calls --fixtures /tmp/external-call-oracle --check
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus external-calls --repo WORKTREE --fixtures /tmp/external-call-oracle \
  --output RESULT_DIRECTORY
```
