(* Opcode provenance for the pre-walk DRET desugaring pass. *)
Theory o1DretOpcodePreservation
Ancestors
  list venomInst dretDesugarDefs ctxLookupAgreeHelpers

Theorem expand_dret_pairs_absent[local]:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  EVERY (\i. i.inst_opcode <> op) emitted
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs(), mk_inst_def]
QED

Theorem replace_dret_inst_absent[local]:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  replace_dret_inst s cursor inst = SOME (out,s') ==>
  EVERY (\i. i.inst_opcode <> op) out
Proof
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def] >>
  metis_tac[expand_dret_pairs_absent]
QED

Theorem dret_desugar_insts_absent[local]:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  dret_desugar_insts s cursor insts = SOME (out,s') /\
  EVERY (\i. i.inst_opcode <> op) insts ==>
  EVERY (\i. i.inst_opcode <> op) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`cursor`,`s`] >>
  Induct_on `insts` >> rpt strip_tac >>
  gvs[dret_desugar_insts_def, AllCaseEqs()] >>
  metis_tac[replace_dret_inst_absent]
QED

Theorem dret_desugar_blocks_absent[local]:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  dret_desugar_blocks s cursor bbs = SOME (out,s') /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> op) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. i.inst_opcode <> op) bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`cursor`,`s`] >>
  Induct_on `bbs` >> rpt strip_tac >>
  gvs[dret_desugar_blocks_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_insts_absent]
QED

Theorem dret_desugar_function_opcode_absence:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  dret_desugar_function target s f = SOME (g,t) /\
  EVERY (\i. i.inst_opcode <> op) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> op) (fn_insts g)
Proof
  Cases_on `no_dret f`
  >- (strip_tac >> gvs[dret_desugar_function_def]) >>
  rpt strip_tac >>
  gs[dret_desugar_function_def, AllCaseEqs()] >>
  `EVERY (\bb. EVERY (\i. i.inst_opcode <> op) bb.bb_instructions)
      (first::rest)` by
    gvs[fn_insts_def, fn_insts_EVERY_block] >>
  `EVERY (\bb. EVERY (\i. i.inst_opcode <> op) bb.bb_instructions)
      (first'::rest')` by metis_tac[dret_desugar_blocks_absent] >>
  gvs[fn_insts_def, fn_insts_EVERY_block] >>
  `!opc xs new. EVERY (\i. i.inst_opcode <> opc) xs /\
            new.inst_opcode <> opc ==>
            EVERY (\i. i.inst_opcode <> opc)
              (insert_after_last_param new xs)` by
    (gen_tac >> Induct_on `xs` >> simp[insert_after_last_param_def] >>
     qx_gen_tac `head` >> qx_gen_tac `new` >> strip_tac >>
     Cases_on `EXISTS (\i. is_param_opcode i.inst_opcode) xs` >>
     Cases_on `is_param_opcode head.inst_opcode` >> simp[]) >>
  first_x_assum irule >> gvs[mk_inst_def]
QED
