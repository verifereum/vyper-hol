(* Memory footprint of the bytestring conversion read preamble. *)
Theory bodyMemTbConvertLoadMemory
Ancestors
  bodyMemTbConvertSourceMemory fragExecMem instMemFrontier bodyMemAssignTopCopyFacts
  fragGasSeqMem fragExec
  venomExecSemantics exprLowering emitHelperProps emitHelper compileEnv
  venomState venomInst context list rich_list words loweringSlice exprLoweringProps memSafeRun exprSimWordBuiltins

Theorem convert_load_bytestring_mem_ok:
  load_bytestring_as_word v opc sa = ((r,k),sb) /\
  (opc = SHR \/ opc = SAR) /\ eval_operand v s = SOME w /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  alloca_inv s /\ w2n w + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  gvs[load_bytestring_as_word_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0` by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  simp[below_frontier_MLOAD, mk_inst_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operands_def] >>
  `!n z. sa.cs_next_var <= n ==>
     eval_operand v (update_var (STRING #"%" (toString n)) z s) = SOME w` by
    metis_tac[eval_operand_update_not_fresh] >>
  simp[Once run_inst_seq_mem_ok_cons, inst_dload_in_section_def,
       step_inst_base_def, exec_pure2_def, eval_operands_def, eval_operand_def] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[])) >>
  simp[Once run_inst_seq_mem_ok_cons, GSYM mk_inst_def,
       below_frontier_MLOAD, eval_operand_def] >>
  (conj_tac >-
    (simp[lookup_var_update_var, update_var_def] >>
     mp_tac (Q.INST [`b` |-> `w`, `n` |-> `2`, `i` |-> `1`]
       topcopy_index_bound) >>
     simp[WORD_MULT_CLAUSES])) >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id + 2) MLOAD
      [Var (STRING #"%" (toString (sa.cs_next_var + 1)))]
      [STRING #"%" (toString (sa.cs_next_var + 2))])
    (update_var (STRING #"%" (toString (sa.cs_next_var + 1))) (w + 32w)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s))` >>
  simp[] >> irule run_inst_seq_mem_ok_every >>
  simp[inst_dload_in_section_def] >> rpt conj_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem convert_load_bytestring_path_mem:
  load_bytestring_as_word v opc sa = ((r,k),sb) /\
  (opc = SHR \/ opc = SAR) /\ eval_operand v s = SOME w /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  alloca_inv s /\ w2n w + 64 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_load_bytestring_mem_ok >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts sb.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[load_bytestring_as_word_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0` by decide_tac >>
     simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def,
          IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_APPEND]) >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
     LENGTH sb.cs_current_insts` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND] >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`emitted_insts sa sb`, `t`, `ctx`, `func`, `bb`] mp_tac) >>
  simp[IS_PREFIX_APPEND] >> metis_tac[]
QED
