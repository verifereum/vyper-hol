# TASK: Prove the memory-safe counted compiled MsgGas leaf

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering

## Theorem Statement (FROZEN)
```sml
Theorem msg_gas_mem_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) ==>
  ?w. gas_prefix 1 s.vs_gas_readings = [w] /\
    gas_path_mem_edge ctx func s 1
      (OK (update_var out w
        (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                   vs_inst_idx := SUC s.vs_inst_idx|>)))

Theorem compile_msg_gas_mem_path:
  compile_env_var MsgGas sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w.
    op = Var out /\ gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path_mem ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)))
```
Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria
- Prove compile_msg_gas_mem_path and its consumed instruction-edge helper without new admissions or hypotheses.
- Build msgGasSimTheory at the default 2.5s step limit.
- Preserve every original theorem and proof before msg_gas_mem_edge byte for byte, including the source and legacy gas-path theorems.

## Build
holbuild -j4 build msgGasSimTheory

## Background
The existing MsgGas path theorem counts one actual GAS event, including exhausted oracles. The new root retains exactly that path, target landing and suffix while certifying actual same-fuel memory safety. Its current helper proof stalls in broad simplification. Independent whole-statement audit returned PROVABLE for both exact schemas, including oracle exhaustion, arbitrary memory metadata and placement. The owner build reached both new statements after checking all earlier proofs. This is the actual explicit-read construct used by the full expression-frame theorem downstream.

## Domain Constraints
Only lowering/msgGasSimScript.sml at and after msg_gas_mem_edge plus prover task state may change. Statements stay byte for byte. No definition change, timeout override, TRY/ORELSE around search, new cheat or axiom. Search for existing helpers before adding one; export/move and reuse rather than copying, including local lemmas. Do not weaken memory safety or assume a nonempty gas stream. Existing proofs before the new helper are frozen.

## Available Resources
- lowering/msgGasSimScript.sml
- lowering/fragGasSeqMemScript.sml
- lowering/fragGasPathMemScript.sml
- lowering/fragGasPathScript.sml
- lowering/gasCountScript.sml
- lowering/fragExecMemScript.sml
- venom/compiler/memSafeRunScript.sml
- lowering/defs/exprLoweringScript.sml
- lowering/emitHelperPropsScript.sml

## Notes
The already-checked reusable straight_line_mem_edge is in fragGasSeqMemTheory. This task has no concurrent owner build. All old proofs remain intact; the two new proofs are the only permitted root changes.
