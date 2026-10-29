# Checked-power certificate extraction

This reverse-extraction starts at `5b6a3f2a`, after comparison with `main...HEAD`.
The complete original proof code is preserved at
`issue-543-pre-split-39cb5ac1` (`39cb5ac1cc3534e83ee0ff49cb8b6e40aeb8d419`).
Reversing this extraction commit restores the removed certificates and their
integration; no admitted replacement for a proved power goal is introduced.

## Extracted work

The thirteen execution/certification theories `power{Bound,Run,Block,SignedRun,
TypedCounterexample,Guard,SignedExponent,Small,Endpoint,TypedRun,PositiveRun,
Checked,Frag}Props` (with `powerTypedCounterexample`'s actual theory/file name)
and `tests/powerLoweringPin.py` are removed. This includes their emitted-sequence,
real-block, raw-width regression and checked-expression certificates. The
execution wrapper `well_typed_unsigned_power_exponent_correct` and the power
fragment/operator integration are removed too.

`powerDomainProps` remains as an independent typing/domain/support-gate theory;
it no longer imports or audits execution certificates. `vyperPowerDomainTest`
remains because it tests **core checker** expression/AugAssign exponent-domain
rules, production checker conversion, and runtime/deploy checking boundaries,
not the optional lowering simulation. Their redundant standalone roots are
removed; `sourceElaborationAudit` still reaches and audits both independent
core theories. Source support gate-redundancy certificates remain independent.
Folded-value power parity fixtures/theories also remain: they exercise core
constant arithmetic, not the extracted checked-power simulation stack.

## Sound proof boundary, rather than baseline admission

On `main`, `binop_frag_pow` is admitted with the antecedent
`(bop = Exp \/ bop = ExpMod) /\ well_typed_binop ...` and arbitrary `bl`/`el`
literal options, plus typed operand values. That is not enough provenance for
checked exponentiation. Restoring its `Proof cheat QED` would replace a proved
checked-power case with an admission. It is deliberately **not** restored.

* `binop_frag_word_typed`, `binop_frag_typed`, and `compile_bop_word_sim` now
  explicitly exclude `Exp`. Existing unrelated ExpMod/shift admissions are
  unchanged, not new certificates.
* The proved operator-parametric `compile_bop_word_with_frag_sim` remains.
* `power_sim_ok cenv` names the exact optional induction step formerly proved
  by `compile_power_case_sim`. It is a proposition, not an axiom or a checker
  restriction.
* `compile_bop_case_sim`, `compile_bop_ok`, and the terminal `exprSimMain`
  induction expose that premise (binary dispatch requires it only for `Exp`).
  The full simulation theorem is conditional
  on `!cenv. power_sim_ok cenv`, rather than silently acquiring a power cheat.
  No executable checker, supported-source gate, or runtime meaning is weakened.

Reference checking found no proof clients applying the terminal
`compile_expr_sim{,_mutual}`/`compile_expr_vv_sim` theorems outside
`exprSimMain`; `vyperLoweringHol` imports the theory but does not apply them.
Reattaching the optional proof discharges the explicit premise and recovers
those former unconditional interfaces. Existing unrelated #636 admissions
remain outside the extracted power certificate closure.

## Preserved arithmetic and correctness fixes

No source constant arithmetic, Source/Meaning theory, sourceExpr legality,
integer exponent-domain check, MethodId fail-closed check, shared type-system
change, ABI runtime semantics, or production lowering definition is reverted.
In particular, this split does not conflate arithmetic correctness fixes with
optional proof certificates:

* The negative-base exponent-bound extension and negative endpoint allowance
  remain. Valid byte-aligned examples such as `(-2) ** 255 : int256` must retain
  the representable result `-2**255`, while the positive endpoint is rejected.
  These behaviors already exist on `main` and are not extracted.
* The additional `ODD exponent` condition on the signed literal-exponent lower
  bound remains. Its behavioral difference is at **raw non-byte widths**, e.g.
  `IntT 9`, exponent 2: `(-16)**2 = 256` must not pass a signed-9 bound. For a
  legal signed byte width, `bits - 1` is odd, so an even exponent cannot satisfy
  `(upper + 1)**exponent = 2**(bits - 1)`. Thus this guard is not a dependency
  needed solely to admit valid byte-aligned source programs, but retaining the
  independent correctness repair avoids regressing total raw lowering.
* The `IntT 1` post-EXP clamps and their shape helper also remain as independent
  total-lowering fixes (`+1` is not representable). `evaluate_type` rejects
  `IntT 1` and `IntT 9`; neither repair is a new source legality rule. They have
  no dependency on the extracted simulation theories.

## Validation

`holbuild -j4 build exprSimMainTheory powerDomainPropsTheory
vyperPowerDomainTestTheory` exits 1 at the unchanged prerequisite
`vyperTypeSystemTheory.target_mutable_static_maps_transfer`, line 661, fragment
`Induct` (`NO_TAC`). A separate `holbuild -j4 build vyperTypeSystemTheory`
reproduces the same failure. The modified simulation/domain proofs are therefore
**not build-validated**; no clean certificate build is claimed. The unrelated
baseline failure is neither modified nor masked.

`git diff --check`, removed-certificate reference checking, and preservation
checks against `5b6a3f2a` for all frontend/semantics/production-lowering files pass.
No new cheat or axiom is introduced. The preserved ref has identical extracted
power code to `5b6a3f2a`. Existing unrelated admitted general simulations remain.
