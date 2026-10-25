# Folded-value validation: independent execution results

## Status and scope

The independent run on 2026-10-23 used the clean pinned checkout at `~/vyper`:
**30 witnesses MATCH**, four have bytecode mismatches, two immutable witnesses
return HOL `NONE`, and `method_id_var` has the expected actual Python rejection.
All 36 accepted ASTs pass both HOL checker modes. All four overflow executions
revert on py-evm 0.12.1b1 PragueVM. The seven required new fixtures are integrated
in `eval/foldedValueParityScript.sml`. The current split parity theories have
also passed a forced rebuild with checkpoint/proof-step reuse disabled; source
identities, exact-statement/tag audits, commands and logs are in
[`current verification`](../../../notes/validation/folded-value-2026-10-24/REPORT.md).
That report explicitly records the three pre-existing lowering CHEATs; this is
not a claim of globally cheat-free lowering correctness.

The complete rows, hashes, commands, logs, runtime observations and current
full-corpus rerun status are in
[`notes/validation/folded-value-2026-10-23/REPORT.md`](../../../notes/validation/folded-value-2026-10-23/REPORT.md).
Independent AST/layout and deploy/runtime bytes are in `folded-value-oracle/`.
Expected bytecode was generated only by pinned Python Vyper.

The two selector/ensure-tuple mismatches retain the #551 dependency: the current
`lower_abi_encode` accepts but does not use `ensure_tuple`. The other mismatches
are `rc09_abi_encode_data` (#554/#551) and `rr03_abi` (#567/#551); the `NONE`
results are `i12_immut_with_storage` and `p29_imm_multi` (#563). These are observed
validation failures, not passing or unexecuted cases. No dependency-owned
compiler fix or whitelist relaxation is included here.

Paths below are repository-relative. `folded-value-witnesses.txt` is the complete
37-stem inventory; each stem has a `.vy` file in `folded-value-sources/`.
`folded-value-parity-fixtures.txt` selects the seven required new parity sources.
The existing `supported-fixtures.txt`, frozen corpus, oracle outputs and whitelist
are deliberately unchanged. Comments in TASK were omitted from the copied
sources; declarations and executable statements are retained.

## Witness inventory (executed results are in the independent report)

| Stems | Role / required evidence |
|---|---|
| pow_folded_exp, pow_negfold_base | Checked literal-pow paths; byte equality and dual-runtime overflow reverts |
| fold_add, fold_pow_lit, fold_cmp, fold_not, fold_shift, fold_minmax | a10 operator/Call folds |
| fold_powmod, fold_addmod, fold_abs | In-whitelist a07 builtin folds |
| keccak_literal, len_string_lit | Literal-argument builtin folds; #569 validation dependency for bytestring hashing |
| method_id_b4, method_id_bytes, method_id_const, method_id_storage | MethodId replaced with a correctly typed folded literal, byte equality |
| method_id_var | Actual pinned-Vyper rejection (no annotated AST expected); hand-built HOL rejection is tested separately |
| enc_mid_const, enc_mid_methodid_call | Selector survives keyword translation, byte equality |
| enc_mid_bytes4lit, enc_ensF_string_mid, enc_ensF_uint_mid | Selector controls |
| enc_ensure_const, dec_unwrap_const | Boolean keyword constants |
| ctl03_abi_method_id, enc_ensT_uint_mid | Require MATCH when #551 is present; otherwise record that specific dependency |
| neg_lit, pow_neglit_base, lt_mixed_lit, boolop_and3 | Non-regression controls |
| i12_immut_with_storage, p29_imm_multi | Validation only; remaining immutable defects owned by #563 |
| c16_const_string_in_expr, c27_const_binop_fold | Validation only; remaining constant defects owned by #565 |
| rc09_abi_encode_data | Validation only; #554 / #551 |
| rr03_abi | Validation only; #567 / #551 |

Do not assume external dependencies are present just because their witnesses
exist. Do not repair those issues while recording this validation. Preserve the
`Exp` restriction pending #572 and the other supported-program restrictions.

## Local checks

Built `vyperCheckContractFrontendLibTestTheory` and
`vyperCheckContractLibTestTheory`, then `foldedValueValidationPrepTheory`.
The preparation theory imports both test theories, verifies all 37 sources
against the inventory, and audits their stored theorem tags (only DISK_THM
is allowed). It does not certify the Vyper source syntax or any parity claim.

The frontend tests cover folded/unfolded decoder constructors, all folded literal
kinds, nested folds, integer/range-bound extraction, valid ABI keywords and
rejection of malformed selectors/Boolean keywords. The checker test covers
residual hand-built MethodId rejection. These are local synthetic input checks,
not observations of the pinned compiler's ASTs for the new source files.
Existing translation boundary tests imply that a Call with a folded literal
translates as that literal, including MethodId when its metadata is supplied.
The independent report now records the external AST round trip for these exact
sources, including MethodId metadata and selector survival.

## External reproduction procedure

Run from the repository root with a command runner. Preserve stdout, stderr,
exit statuses and file hashes. First reproduce the existing corpus using the
verified clean checkout and isolated environment procedure in
`python-o1-bytecode-fixtures` (uv 0.10.11, managed Python 3.11.11, constraints
`python-o1-oracle-constraints.txt`, clean clone of VYPER_PIN). Check that VYPER_PIN
resolves to Vyper 0.5.0a4 commit cd74ce4f. No unverified system `vyper` substitute.

```sh
B=lowering/defs/bytecode
"$B/python-o1-bytecode-fixtures" --check --vyper-repo "$VYPER_REPO"
```

For the new artifacts retain a separately provisioned isolated `$VENV` built by
that same clone/install procedure (the wrapper removes its temporary venv).
Choose a fresh `$OUT` outside committed oracle directories. `$PIN` is the full
contents of VYPER_PIN. `$ROOT` is the absolute repository path.

```sh
B=lowering/defs/bytecode
mkdir -p "$OUT/sources" "$OUT/ast" "$OUT/logs"
grep -v '^method_id_var$' "$B/folded-value-witnesses.txt" > "$OUT/accepted.txt"
while read -r stem; do
  cp "$B/folded-value-sources/$stem.vy" "$OUT/sources/"
done < "$OUT/accepted.txt"
env -u PYTHONPATH -u PYTHONHOME -u PYTHONSTARTUP \
  "$VENV/bin/python" -I "$B/python_o1_bytecode_oracle.py" \
  --expected-commit "$PIN" --expected-python 3.11.11 --generator-uv 0.10.11 \
  --expected-install-root "$VENV" --sources "$OUT/sources" \
  --fixture-manifest "$OUT/accepted.txt" --output "$OUT/oracle"
while read -r stem; do
  "$VENV/bin/vyper" -f annotated_ast,layout "$OUT/sources/$stem.vy" \
    > "$OUT/ast/$stem.jsonl" 2> "$OUT/logs/$stem.ast.stderr"
  "$VENV/bin/python" tests/sanitize_check_contract_json.py \
    "$OUT/ast/$stem.jsonl" "$OUT/ast/$stem.json" \
    --replace "$OUT=folded-value-validation" --replace "$ROOT=."
done < "$OUT/accepted.txt"
"$VENV/bin/vyper" -f annotated_ast,layout \
  "$B/folded-value-sources/method_id_var.vy" \
  > "$OUT/ast/method_id_var.jsonl" 2> "$OUT/logs/method_id_var.stderr"
# Record the final command's exit status; a nonzero rejection is expected.
```

Fail visibly on an unexpected accepted-source export error; do not silently skip
it. Preserve provenance.json and all 36 independent `.hex` files. The generator
fixes optimize=NONE, evm_version=prague, experimental_codegen=True,
no bytecode metadata and verifies compiler/install identity. Never use HOL
output as its expected bytes. AST export and bytecode generation must use the
same pinned installation and exact source contents.

## Artifact consumption and required results

For each sanitized AST, use `vyperCheckContractFrontendLib.prepare_check_input`
and `vyperCheckContractLib.check_contract` in both deployment modes. Record the
translated tops and supported_program result, then evaluate
`compile_vyper (K SOME) (o1_policy all_capabilities) tops` and compare BOTH deploy
and runtime bytes with the independent `.hex`. Add a HOL test following
`eval/evalCompilerBytecodeControlScript.sml`: expected bytes are ordinary data,
and equality must be checked by compiler evaluation, never by injecting oracle
byte equalities as evaluator rewrites. The seven required fixture stems are in
`folded-value-parity-fixtures.txt`; their HOL input terms must come from the
actual sanitized ASTs, not guessed hand-written reduced programs.

Return a row for every manifest stem containing: source SHA256, AST/oracle
SHA256, both checker results, supported_program, HOL compile success,
deploy equality, runtime equality, verdict and dependency notes. Distinguish
NOT_RUN, compile failure, rejection and mismatch from MATCH. Record
method_id_var's actual Python rejection and reference the HOL rejection test.
Also return exact generator/runner versions, compiler commit and settings,
commands/logs and the source revision used. Repeat stale runs after source or
compiler changes.

Rerun the complete existing corpus using the wrapper's `--compare-hol` procedure
or its listed current holbuild targets, recording full results (not only cache
availability). The wrapper documents the separate opt-in evaluator settings;
the CLI supports `--tactic-timeout` for those opt-in runs. The current staged
seven-fixture proofs also build without changing the default tactic budget.

Finally execute `pow_folded_exp.f(2**90)` and
`pow_negfold_base.f(256)` on BOTH HOL and Python runtime bytecodes with minievm or
another named/versioned EVM implementation. Return calldata and runtime hashes,
execution logs, and all four revert results. Byte equality or a successful HOL
proof build alone is not a substitute for the requested execution evidence.
The preparation itself supplied no EVM runner; the independent run subsequently
used py-evm and retained all four execution receipts.
