# TASK: Preserve memory-safe counted paths at raw jump boundaries

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/fragGasPathMemScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem gas_path_mem_edge_continue[local]:
  gas_path_mem_edge ctx fn s n (OK t) /\
  run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
  ?fuel'. run_from fuel' ctx fn s = out /\
    (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
```

The approved edge definition is also frozen:

```sml
Definition gas_path_mem_edge_def:
  gas_path_mem_edge ctx fn s n r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
      (revert_forward_at bb s.vs_inst_idx \/
       mem_safe_step fuel ctx inst s) /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx)) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions)) \/
       (?lbl. is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
              middle = OK (jump_to lbl s) /\ r = middle) \/
       (exit_result middle /\ r = middle))
End
```

Do not modify this statement or definition. Prove it as-is, or produce a counterexample. Every other existing definition and theorem statement is frozen too.

## Completion Criteria

1. `holbuild -j2 build fragGasPathMemTheory` passes after the memory continuation root and necessary same-theory proof repairs.
2. No new admissions, axioms, parser warnings, timeout overrides, or search-filtering TRY/ORELSE.
3. Preserve all existing statements, the exact actual instruction/count/memory checks, ordinary path erasure and full-execution continuation/completion.
4. Search existing helpers before adding one. Export or move matching local lemmas to their common owner instead of duplicating them.

## Build

```sh
holbuild -j2 build fragGasPathMemTheory
```

## Background

Generic lowering fragments may end with an actual loop-control jump before destination lookup or PHI processing. Their containing-function premise only promises the emitted fragment, not a destination block. The approved logical edge extension admits that raw actual jump endpoint alongside the existing PHI-entered successor. It preserves actual instruction execution, GAS counts and memory checks. Ordinary fragGasPathTheory already builds with the same extension; all its theorem statements are unchanged. This task repairs the memory-path continuation proof and any dependent same-theory proof affected by the new edge case.

## Domain Constraints

Independent audit answered PROVABLE for the exact memory continuation and dependent public results under these definitions. Add no destination-existence/no-PHI premise, arbitrary path, memory exemption, opcode restriction, or weakened theorem. No executable/source semantics changes. The original proof is retained. Existing unrelated admissions are not in scope; introduce none.

## Available Resources

- lowering/fragGasPathMemScript.sml: frozen extended memory edge, assigned continuation root, existing safety/exit/composition results.
- lowering/fragGasPathScript.sml: owner-checked ordinary path extension and unchanged continuation results.
- lowering/fragExecScript.sml and fragExecMemScript.sml: existing fragment runners and continuations.
- venom/proofs/memSafeRunScript.sml: actual memory-safe runner.
- venom/defs/venomExecSemanticsScript.sml: actual instruction/PHI semantics.

## Notes

The exact memory continuation root parsed in owner58795; its retained old proof fails because the new raw-jump goal reaches the old entered-case branch selection. The ordinary extension owner58770 passed in4.576s. All definitions and statements are frozen. This task supplies no new stage, top-level or source hypothesis.
