(*
 * Assembly -> Bytecode Correctness -- Structural Properties
 *
 * Proved per-step correspondence and bounded forward simulation remain
 * in the evmStepSim and asmBytecodeSim ancestor theories.
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
 * STRUCTURAL:
 *   offset_to_pc_inverse     - byte offset -> asm index round-trips
 *   label_offset_consistent  - labels resolve to correct byte offsets
 *   encode_inst_length       - encode_inst produces asm_inst_size bytes
 *   encode_at                - bytes at offset match encode_inst
 *   assemble_parse_correct   - parse_code gives right opname at each position
 *
 * TOP-LEVEL:
 *   assemble_parse_correct   - prefix-form corollary of assemble_parse_exact
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
    asm_encoding_wf prog /\
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
