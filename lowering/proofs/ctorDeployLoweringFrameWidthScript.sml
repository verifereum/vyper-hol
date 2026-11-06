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

(* Historical encoding diagnostic only: the synthetic symbol at 65536
   encodes an extra byte following PUSH2. This is not a compiled deployment
   witness or a counterexample to deploy_ctor_body_frame. No deployment
   size bound is claimed here. If needed, the permitted deployment-bytecode
   bound is deploy_bc_size_bounded in ctorDeployInitcodeAsm, not a bound
   on arbitrary initcode plus appended arguments from deploy_state_rel. *)
