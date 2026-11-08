(* Fixed stages of the runtime immutable copy, before cursor counting. *)
Theory exprPtrCodeCopySegments
Ancestors
  exprPtrUnwrapCodeEdges exprPtrUnwrapOffsetSegment exprPtrUnwrapFrames
  exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges decoderGhostFramePtr typedCopyPtr fragGasSeqPtr fragExec
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map exprLoweringProps immutableCopyExecution bodyPtrDefs venomExecProps codegenRel instIdxIndep ghostPcTransportPtr

Theorem code_copy_source_add_segment:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id ADD [src; Lit (n2w off)] [out]] s = OK t /\
  (!p. P p ==> p <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [src; Lit (n2w off)] [out]]
        (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [src; Lit (n2w off)] [out]) s =
     OK (update_var out (a+n2w off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  gvs[run_inst_seq_def] >>
  qexistsl [`step_prov PG G (mk_inst id ADD [src; Lit (n2w off)] [out])
      (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst id ADD [src; Lit (n2w off)] [out]) s
      (update_var out (a+n2w off) s) tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_copy_arith, op_taint_def,
       step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def,
       is_terminator_def, copy_len_binop_ghost_frame, copy_mk_immutable_taint] >>
  conj_tac
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[copy_len_binop_ghost_frame, step_taint_def, set_var_taint_def,
           mk_inst_def, FLOOKUP_UPDATE]) >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem code_copy_load_taint_frame:
  (step_taint (mk_inst id DLOAD [arg] [out]) s
    (update_var out value s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id DLOAD [arg] [out]) s
    (update_var out value s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id DLOAD [arg] [out]) s
    (update_var out value s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id DLOAD [arg] [out]) s
    (update_var out value s) tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, source_memory_write_ranges_def, range_bytes_def,
    store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def, update_var_def,
    FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]
QED

Theorem code_copy_load_segment:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id DLOAD [arg] [out]] s = OK t /\
  (!p. P p ==> p <> out) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id DLOAD [arg] [out]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. P p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. P p /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id DLOAD [arg] [out]) s =
    OK (update_var out (immutable_copy_read F a s) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, immutable_copy_read_def] >>
  gvs[run_inst_seq_def] >>
  qexistsl [`step_prov PG G (mk_inst id DLOAD [arg] [out])
    (update_var out (immutable_copy_read F a s) s)`,
    `step_taint (mk_inst id DLOAD [arg] [out]) s
      (update_var out (immutable_copy_read F a s) s) tn`] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_code_load,
    step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def,
    is_terminator_def, runtime_code_load_clean, code_copy_load_taint_frame] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[runtime_code_load_clean, code_copy_load_taint_frame] >>
  conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  conj_tac
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      simp[step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
