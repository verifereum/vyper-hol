(* Compiler-fresh offset temporaries preserve old pointer observations.
   Raw run endpoints are kept distinct from PC-advanced counted endpoints. *)
Theory bodyPtrMakeArrayOffsetFrame
Ancestors
  bodyPtrMakeArrayImmutableStep bodyPtrMakeArrayAdd exprSimCopy
  typedCopyPtr fragGasSeqPtr fragGasPathPtr context compileEnv
  exprLoweringProps emitHelper emitHelperProps venomInst venomState
  venomExecSemantics ptrDiscipline bodyPtrDefs words finite_map

Theorem immutable_byte_offset_raw_frame:
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand r u = SOME (a+n2w off) /\ copy_old_operand sb r /\
    op_taint tnf r = {} /\
    u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\
    u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all copy_runtime_offset >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      `s' = s` by gvs[copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      gvs[emitted_insts_def, inst_seq_ptr_def]) >>
  Cases_on `op` >> gvs[eval_operand_def, compile_lit_byte_offset_def, comp_return_def]
  >- (`s' = s` by gvs[copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      gvs[emitted_insts_def, inst_seq_ptr_def, eval_operand_def, op_taint_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  rename1 `r = Var out` >>
  qmatch_asmsub_abbrev_tac `emit_op ADD [left; Lit (n2w off)] sa` >>
  `s' = update_var out (a+n2w off) s` by
    (gvs[copy_runtime_frame_def, run_inst_seq_def, Once step_inst_base_def,
         mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `left`]) >>
  qexistsl_tac [`s'`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [left; Lit (n2w off)] [out]) s'`,
    `step_taint (mk_inst sa.cs_next_id ADD [left; Lit (n2w off)] [out]) s s' tn`] >>
  gvs[] >> drule_at Any emit_binop_old_frame >> simp[] >> strip_tac >>
  simp[inst_seq_ptr_def, ptr_inst_ok_copy_len_binop, op_taint_def,
       Once step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def,
       update_var_def] >>
  fs[lookup_var_def, update_var_def, mk_inst_def, Abbr `left`, eval_operand_def] >>
  simp[step_taint_def, set_var_taint_def, imm_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem immutable_offset_framed_ptr_path:
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    eval_operand r u = SOME (a+n2w off) /\ copy_old_operand sb r /\
    op_taint tnf r = {} /\
    u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p u k)
Proof
  strip_tac >> drule_all immutable_byte_offset_raw_frame >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule immutable_byte_offset_opcodes >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    fs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[] >>
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED
