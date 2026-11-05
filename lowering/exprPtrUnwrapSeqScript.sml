(* Concatenation at the indexed straight-line pointer trace boundary. *)
Theory exprPtrUnwrapSeq
Ancestors
  fragGasSeqPtr fragExec exprLoweringProps instIdxIndep venomExecSemantics
  venomState list arithmetic

Theorem inst_seq_ptr_append:
  !prefix s t G tn Gm tnm suffix Gf tnf.
    run_inst_seq prefix s = OK t /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    inst_seq_ptr D lo ctx fn PG G tn prefix s Gm tnm /\
    inst_seq_ptr D lo ctx fn PG Gm tnm suffix
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH prefix) Gf tnf ==>
    inst_seq_ptr D lo ctx fn PG G tn (prefix ++ suffix) s Gf tnf
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >>
  qexistsl_tac [`Gm`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tnm`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD1] >>
  `LENGTH prefix + (s.vs_inst_idx + 1) =
   SUC (LENGTH prefix) + s.vs_inst_idx` by decide_tac >>
  asm_rewrite_tac[]
QED
