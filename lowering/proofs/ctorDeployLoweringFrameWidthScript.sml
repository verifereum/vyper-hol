Theory ctorDeployLoweringFrameWidth
Ancestors
  ctorDeployDefs e2eDeployDefs codegenEncodingWf symbolResolve
  planExec vfmOperation vfmContext asmParseProofs
Libs wordsLib finite_mapLib

Theorem label_width_65536_encoding:
  encode_inst (FEMPTY |+ ("target",65536)) (AsmPushLabel "target") =
    [97w;1w;0w;0w] /\
  FLAT (MAP (encode_inst (FEMPTY |+ ("target",65536)))
    (execute_plan 0 [SOPushLabel "target"; SOEmit "JUMP"])) =
    [97w;1w;0w;0w;86w]
Proof
  EVAL_TAC
QED

Theorem label_width_65536_parsing:
  FLOOKUP (parse_code 0 FEMPTY [97w;1w;0w;0w;86w]) 0 =
    SOME (Push 2 [1w;0w]) /\
  LENGTH (opcode (Push 2 [1w;0w])) = 3 /\
  word_of_bytes F (0w:256 word) (REVERSE [1w;0w]) = 256w /\
  FLOOKUP (parse_code 0 FEMPTY [97w;1w;0w;0w;86w]) 3 = SOME Stop /\
  FLOOKUP (parse_code 0 FEMPTY [97w;1w;0w;0w;86w]) 4 = SOME Jump
Proof
  `parse_opcode [97w;1w;0w;0w;86w] = SOME (Push 2 [1w;0w])` by
    (mp_tac (Q.SPECL [`2`, `[1w;0w]`, `[0w;86w]`] parse_opcode_push) >> simp[]) >>
  `parse_opcode [0w;86w] = SOME Stop` by
    simp[parse_opcode_cond_thm, wordsTheory.dimword_8] >>
  `parse_opcode [86w] = SOME Jump` by
    simp[parse_opcode_cond_thm, wordsTheory.dimword_8] >>
  `parse_code 0 FEMPTY [97w;1w;0w;0w;86w] =
    FEMPTY |+ (0,Push 2 [1w;0w]) |+ (3,Stop) |+ (4,Jump)` by
    (simp[Once parse_code_def, opcode_def] >>
     simp[Once parse_code_def, opcode_def] >>
     simp[Once parse_code_def, opcode_def] >>
     simp[Once parse_code_def]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, opcode_def,
       byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
       byteTheory.word_slice_alt_zero] >> EVAL_TAC
QED

(* Bounded feasibility audit (not a counterexample to deploy_ctor_body_frame).
   Producer chain: deploy_phases_def names codegen_assembly rpolicy
   dout.po_unit = SOME prog and deploy_bc = assemble prog.
   assembly_target_safe checks supported opcodes and push-data lengths;
   encode_inst / pad_bytes do not reject oversized resolved symbols.

   Requirement                         Diagnostic status
   ----------------------------------- ------------------------------------
   Supported/typed large source         MISSING: no concrete tops constructed.
   Deployment length >= 65536           RULED OUT by deploy_bc_size_bounded
                                        (ctorDeployInitcodeAsm, admitted until
                                        the codegen sync).
   Label offset 65536 in real assembly   No witness; compute_label_offsets_bound
                                        bounds offsets by SUM asm_inst_size.
                                        codegenEncodingWf's local
                                        sum_size_le_encode bounds that sum by
                                        assembled length for supported ops.
   Explicit assembler width rejection   ABSENT; synthetic encoding above keeps
                                        three immediate bytes after PUSH2.
   Reachable overflowing branch         MISSING, and incompatible with the
                                        preceding size/offset bounds under
                                        their supported-op hypotheses.
   Reachable unintended call            MISSING; concrete parser instead sees
                                        PUSH2 256, STOP, JUMP. STOP alone
                                        supplies no root call outcome.
   Bad installed-context outcome        MISSING: context-separation evidence
                                        does not supply an actual trace.

   codegen_assembly_asm_encoding_wf already packages a useful consumer
   interface under unit_shape_ok and assembled length < 65536. Its proof
   establishes the offset bound, rather than relying on assembler rejection.
   The admitted size supplier is not evidence that the executable compiler
   rejects oversized deployments. No syntactic
   or whole-trace confinement theorem is asserted here.
*)
