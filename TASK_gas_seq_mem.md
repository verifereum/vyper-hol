# TASK: Count actual GAS sites of a memory-safe straight-line fragment

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering

## Theorem Statement (FROZEN)
```sml
Theorem run_inst_seq_gas_path_mem:
  !code s t ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = OK t ==>
    gas_path_mem ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
```
Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria
- Prove the frozen theorem without admissions, axioms, new premises or definition changes.
- Build fragGasSeqMemTheory at the default 2.5s step limit.
- Reuse existing lemmas rather than adding duplicates, including local copies.

## Build
holbuild -j4 build fragGasSeqMemTheory

## Background
The source-consumption simulation needs counted paths of actual emitted fragments, with the memory checks attached to the same executed instructions. This theorem provides the target path for a successful straight-line fragment. It does not classify source reads or assume a source result; the enclosing construct supplies that relation separately.

## Domain Constraints
Only lowering/fragGasSeqMemScript.sml and prover task state may change. Keep the theorem statement byte for byte. Consumed helper lemmas may be added after searching existing results. No new definitions, TRY/ORELSE around search, timeout overrides or feature restrictions. Preserve every other source file.

## Available Resources
- lowering/fragGasSeqMemScript.sml
- lowering/fragGasPathMemScript.sml
- lowering/fragExecMemScript.sml
- lowering/fragExecScript.sml
- lowering/instMemFrontierScript.sml
- venom/proofs/gasCountScript.sml
- venom/compiler/memSafeRunScript.sml
- venom/proofs/venomInstProofsScript.sml

## Notes
An independent read-only audit classified this entire statement PROVABLE, including exhausted readings, arbitrary cursor indices, the empty sequence and every endpoint field. The owner parse check passed with the temporary placeholder in 219.393s; fragGasPathMemTheory also built. This new theorem's temporary placeholder must be removed. Do not run concurrently with another build in this worktree.
