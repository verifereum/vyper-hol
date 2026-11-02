# TASK: Preserve assertion-combiner correctness with consuming GAS

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/passes/assert_combiner

## Theorem Statement (FROZEN)

```sml
Theorem ac_transform_function_correct_proof:
  !fuel ctx fn s.
    let fn' = ac_transform_function fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    wf_function fn /\
    fn_inst_wf fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
       ac_is_safe_between inst \/ inst.inst_opcode = ASSERT \/
       is_terminator inst.inst_opcode) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    ac_inv fn dfg s /\
    (* no_redefine: all instruction outputs are undefined in initial state *)
    (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
       MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s)) /\
    (* Combined invariant preservation for fn blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    (* Combined invariant preservation for fn' blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (ac_fresh_vars_fn fn))
               (execution_equiv UNIV)
               (\s1 s2. ?gs. execution_equiv UNIV s1
                 (s2 with vs_gas_readings := gs))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The public `ac_transform_function_correct` API has the same frozen statement.

## Completion Criteria

- Repair existing proof bodies and necessary proof-only helper statements for consuming GAS, retaining existing proofs wherever useful.
- Save both frozen theorems without new admissions.
- Build `assertCombinerCorrectnessTheory`; also check modified helper theories.
- On OK and Halt, preserve exact gas readings under the existing state/execution relations. Only Abort may forget the unconsumed suffix, exactly as the frozen statement says.
- If the frozen result is false, give a concrete counterexample rather than changing hypotheses.

## Build

`holbuild -j2 build assertCombinerCorrectnessTheory`

## Background

Every GAS now pops vs_gas_readings, returning zero on exhaustion. The assertion combiner retains all GAS instructions in their relative order on successful or halting paths. A failed early ASSERT can be deferred past GAS before the combined assertion aborts; unused readings then differ without observable behavior changing. The old abort equality was too strong.

The executable transform has a separately tracked instruction-ID allocation bug and the legacy invariant API has a separately tracked coverage limitation. Those are OUT OF SCOPE: preserve the existing executable definitions, ac_inv, theorem hypotheses, and inherited structural-preservation admissions. Do not repair those issues or restrict GAS away. This task makes only the approved gas migration of the existing theorem.

The old `ac_safe_between_effect_free` classification is false for GAS. Replace it with a correct effect-free-or-GAS helper and handle the paired GAS case; do not mark GAS effect-free or exclude it from safe-between.

## Domain Constraints

- Do not edit executable definitions (`assertCombinerDefsScript.sml`, `assertCombinerScript.sml`, semantics, state definitions).
- Do not change ac_inv, stage contracts, top-level hypotheses, source semantics, O1 composition, or the existing OK/Halt relations.
- Do not edit the inherited `ac_preserves_ssa_form` and `ac_preserves_wf_function` obligations; they belong to a separate structural repair.
- No new cheat/admission/axiom, no no-GAS restriction, no stronger premise.
- Preserve existing proofs; never replace an existing proof with cheat.
- Proof-only helpers may be restated where needed to expose GAS or the approved Abort relation. Flag every restatement in the completion report.
- Scope edits to assertion-combiner proof files and its correctness API. If a shared simulation lemma requires a generalization, add a proof-only version without modifying its existing consumers, or report the needed change.
- Keep the default 2.5-second tactic timeout. No TRY/ORELSE around proof search. Do not raise timeouts to make a proof pass.
- Do not edit other live workers' worktrees. Alan working files are not deliverables.

## Available Resources

- `venom/passes/assert_combiner/proofs/acBaseProofsScript.sml`
- `venom/passes/assert_combiner/proofs/acChainProofsScript.sml`
- `venom/passes/assert_combiner/proofs/acSimPrecondProofsScript.sml`
- `venom/passes/assert_combiner/proofs/acAbortProofsScript.sml`
- `venom/passes/assert_combiner/proofs/assertCombinerProofsScript.sml`
- `venom/passes/assert_combiner/assertCombinerCorrectnessScript.sml`
- `venom/passes/assert_combiner/defs/assertCombinerDefsScript.sml`
- `venom/defs/stateEquivScript.sml`, `venom/props/stateEquivPropsScript.sml`
- `venom/simulation/` block simulation definitions and proof lemmas

## Notes

The exact Abort relation migration was approved by argon after checking real GAS-retaining assertion-combiner output. No executable/API redesign is authorized here. The owner independently audits the frozen statement and forces proof replay after Alan finishes.
