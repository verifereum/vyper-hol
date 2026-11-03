# TASK: Bound existing effect-free output determinism replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_effect_free_output_determined_vars:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> PHI /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = FMP_PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = GETFMP ==> s1.vs_fmp = s2.vs_fmp) /\
    (inst.inst_opcode = INITIAL_FMP ==>
       s1.vs_initial_fmp = s2.vs_initial_fmp) /\
    (inst.inst_opcode = RETPC_PARAM ==>
       s1.vs_return_pc_token = s2.vs_return_pc_token) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
       s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
       s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
       s1.vs_immutables = s2.vs_immutables) /\
    (Eff_RETURNDATA IN read_effects inst.inst_opcode ==>
       s1.vs_returndata = s2.vs_returndata) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
       s1.vs_logs = s2.vs_logs) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v v1 = lookup_var v v2
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the actual default-limit failure in this existing proof without changing its statement.
- Build passSharedTransferTheory at the default tactic limit without new admissions.
- Preserve all existing definitions, other theorem statements, shared tactics and unrelated proof bodies.

## Build

`holbuild -j2 build passSharedTransferTheory`

## Background

Forced same-list validation encountered a 2.5-second timeout in the full opcode-classification gvs immediately after Cases_on inst.inst_opcode. A fresh independent audit checked the exact complete statement against every admitted producer, including BUMP aliasing, parameter/environment reads, malformed successful-step arities and GAS exclusion, and found PROVABLE without amendments. The existing proof is retained.

## Domain Constraints

- Edit only the named proof body and necessary local helpers in this theory.
- No definitions, axioms, admissions, stronger assumptions, opcode exclusions or source/executable semantics changes.
- Keep existing shared tactics and all previously completed GAS/remap/DFG/CFG/DRET repairs unchanged.
- Default 2.5-second tactic limit; no override and no TRY/ORELSE/FIRST around proof search.
- Report another prerequisite root before expanding scope; no speculative cleanup.
- Commit substantive source only, no generated records. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/passSharedTransferScript.sml: target and existing operand-transfer helper facts.
- venom/defs/venomExecSemanticsScript.sml: step_inst_base and opcode-specific equations.
- venom/defs/venomInstScript.sml: existing opcode classification.
- venom/defs/venomEffectsScript.sml: read and write effects.
- venom/proofs/venomInstProofs2Script.sml and venomInstProofs3Script.sml: reusable instruction preservation facts.

## Notes

The exact statement parsed in the forced failure. Owner independently audits its full statement before launch, then checks frozen schemas, default/CI forced replay and dependency tags after return.
