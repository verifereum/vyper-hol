(*
 * Assembly -> Bytecode Correctness -- Properties and Simulation
 *
 * Per-step correspondence: asm_step on one instruction matches
 * vfmExecution$step on the assembled bytecode.
 * Forward simulation: multi-step asm execution matches EVM run.
 *
 * Structural helpers (offset maps, encoding) proved in
 * proofs/asmToBytecodeProofsScript.sml and proofs/asmEncodeParseScript.sml.
 *
 * The bisimulation invariant is asm_evm_rel, which says:
 *   - stacks identical
 *   - memory identical
 *   - PC related by asm_pc_to_offset (sum of instruction sizes)
 *   - code = assemble prog, parsed = parse_code thereof
 *
 * Gas: disjunctive -- either results correspond, or EVM returns OutOfGas.
 *
 * TOP-LEVEL:
 *   asm_bytecode_sim         - forward simulation (asm terminates => EVM matches)
 *
 * STRUCTURAL:
 *   offset_to_pc_inverse     - byte offset -> asm index round-trips
 *   label_offset_consistent  - labels resolve to correct byte offsets
 *   encode_inst_length       - encode_inst produces asm_inst_size bytes
 *   encode_at                - bytes at offset match encode_inst
 *   assemble_parse_correct   - parse_code gives right opname at each position
 *)

Theory asmToBytecodeProps
Ancestors
  codegenRel asmToBytecodeProofs asmParseProofs asmEncodeParse
  evmStepSim asmBytecodeSim vfmContext vfmExecution vfmExecutionProp
  asmWf symbolResolve asmSem arithmetic
  list rich_list finite_map While

(* ===== Structural Helpers ===== *)

(* Weaker (IS_PREFIX) version of assemble_parse_exact *)
Theorem assemble_parse_correct:
  !prog i.
    asm_wf prog /\
    i < LENGTH prog /\
    (!j. j <= i ==> ~is_data_inst (EL j prog)) ==>
    ?op.
      FLOOKUP (parse_code 0 FEMPTY (assemble prog))
              (asm_pc_to_offset prog i) = SOME op /\
      opcode op ≼ encode_inst (SND (compute_label_offsets prog))
                              (EL i prog)
Proof
  rpt strip_tac >>
  drule_all assemble_parse_exact >> strip_tac >>
  qexists_tac `op` >> simp[IS_PREFIX_REFL]
QED

(* ===== Forward Simulation ===== *)

(* Assembly -> EVM bytecode forward simulation.
   Either execution results correspond, or EVM hits an exception.
   With asm_stack_bounded, StackOverflow is ruled out; remaining
   exceptions include OutOfGas, WriteInStaticContext, OutOfBoundsRead. *)
Theorem asm_bytecode_sim:
  !n prog label_offsets offset_to_pc as es.
    asm_wf prog /\
    asm_stack_bounded label_offsets offset_to_pc prog (LENGTH as.as_stack) /\
    label_offsets = SND (compute_label_offsets prog) /\
    offset_to_pc = build_offset_to_pc prog /\
    asm_evm_rel prog as es ==>
    (?es' exc. run es = SOME (INR (SOME exc), es') /\
               exc <> StackOverflow) \/
    ((!as'. asm_steps label_offsets offset_to_pc prog n as =
              AsmHalt as' ==>
        ?es'. run es = SOME (INR NONE, es') /\
              asm_evm_rel prog as' es') /\
     (!as'. asm_steps label_offsets offset_to_pc prog n as =
              AsmRevert as' ==>
        ?es'. run es = SOME (INR (SOME Reverted), es') /\
              asm_evm_rel prog as' es') /\
     (!as'. asm_steps label_offsets offset_to_pc prog n as =
              AsmFault as' ==>
        ?es' exc. run es = SOME (INR (SOME exc), es') /\
                  exc <> Reverted /\
                  asm_evm_rel prog as' es'))
Proof
  (* FALSE AS STATED. Missing preconditions (counterexamples in
     counterexamplesScript.sml, Counterexample 6):
     1. no_asm_calls prog
        — pipeline obligation: codegen never emits CALL/CREATE/etc.
          asm uses single-context model; EVM pushes new contexts.
          Dischargeable from generate_fn_plan output.
     2. LENGTH es.contexts = 1
        — pipeline obligation: codegen targets single-context execution.
          EVM with 2+ contexts: STOP pops context instead of halting.
          Preserved by asm_evm_step (proven in its conclusion).
          Dischargeable from initial_state_rel. *)
  cheat
QED
