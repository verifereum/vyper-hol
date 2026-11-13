(* Successful finite deployment prefix before argument registration. *)
Theory ctorDeployMemoryRunPtrPrefixPrepare
Ancestors
  loweringStateRelDefs
  slotCopyExecution compileEnv
  ctorDeployMemoryRunPtrPrefixRegisterAddress ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence context emitHelper emitHelperProps exprLoweringProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words arithmetic pred_set list rich_list codegenRel contextCodegenRel memLocDefs
  fragExec abiDecoderContract abiDecoderLoop

Theorem prefix_prepare_callvalue_step:
  step_inst_base (mk_inst iid CALLVALUE [] [x]) s =
    OK (update_var x s.vs_call_ctx.cc_callvalue s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_read0_def]
QED


Theorem prefix_prepare_callvalue_ptr:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid CALLVALUE [] [x]) s
Proof
  strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
    step_inst_non_invoke, prefix_prepare_callvalue_step, mk_inst_def,
    taint_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    update_var_def]
QED

Theorem prefix_prepare_zero_ptr:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid ASSIGN [Lit 0w] [x]) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid ASSIGN [Lit 0w] [x]) s =
     OK (update_var x 0w s)` by
    (irule slotCopyExecutionTheory.slot_copy_step_assign >>
     simp[venomStateTheory.eval_operand_def]) >>
  `step_inst fuel ctx (mk_inst iid ASSIGN [Lit 0w] [x]) s =
     OK (update_var x 0w s)` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
    taint_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    op_taint_def, update_var_def, mk_inst_def]
QED

Theorem prefix_prepare_callvalue_ghost:
  ghost_step fuel ctx PG G tn (mk_inst iid CALLVALUE [] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  simp[ghost_step_def, step_inst_non_invoke, prefix_prepare_callvalue_step,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    mk_inst_def]
QED

Theorem prefix_prepare_zero_ghost:
  ghost_step fuel ctx PG G tn (mk_inst iid ASSIGN [Lit 0w] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  `step_inst_base (mk_inst iid ASSIGN [Lit 0w] [x]) s =
     OK (update_var x 0w s)` by
    (irule slotCopyExecutionTheory.slot_copy_step_assign >>
     simp[venomStateTheory.eval_operand_def]) >>
  `step_inst fuel ctx (mk_inst iid ASSIGN [Lit 0w] [x]) s =
     OK (update_var x 0w s)` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  simp[ghost_step_def,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    op_prov_def, first_prov_def, op_taint_def, eval_operand_def, mk_inst_def]
QED

Theorem prefix_prepare_callvalue_run:
  emit_op CALLVALUE [] st = (out,middle) /\ fn_has_code st middle fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x s.vs_call_ctx.cc_callvalue s)
            with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) s.vs_call_ctx.cc_callvalue s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, exec_read0_def] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_prepare_callvalue_ptr, prefix_prepare_callvalue_ghost, update_var_def]
QED

Theorem prefix_prepare_zero_run:
  emit_op ASSIGN [Lit 0w] st = (out,middle) /\ fn_has_code st middle fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x 0w s) with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit 0w]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) 0w s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, eval_operand_def] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_prepare_zero_ptr, prefix_prepare_zero_ghost, update_var_def]
QED

Theorem prefix_prepare_fixed_region_emit:
  compile_fixed_region_with_id cap st = ((iid,buf),last) ==>
  iid = st.cs_next_id /\ buf.buf_size = cap /\
  emit_op ASSIGN [Lit 0w] st = (buf.buf_operand,last)
Proof
  simp[compile_fixed_region_with_id_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED


Theorem prefix_prepare_iszero_ghost:
  eval_operand a s = SOME 0w ==>
  ghost_step fuel ctx PG G tn (mk_inst iid ISZERO [a] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid ISZERO [a] [x]) s =
     OK (update_var x 1w s)` by
    (drule emitHelperPropsTheory.step_ISZERO >>
     simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  `step_inst fuel ctx (mk_inst iid ISZERO [a] [x]) s =
     OK (update_var x 1w s)` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  simp[ghost_step_def,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    mk_inst_def]
QED

Theorem prefix_prepare_iszero_run:
  emit_op ISZERO [a] st = (out,middle) /\ fn_has_code st middle fn /\
  eval_operand a s = SOME 0w /\ op_taint tn a = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x 1w s) with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[a]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) 1w s)` by
    (drule emitHelperPropsTheory.step_ISZERO >>
     simp[venomExecSemanticsTheory.bool_to_word_def] >>
     disch_tac >> simp[step_inst_non_invoke, mk_inst_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_iszero_ptr_step, prefix_prepare_iszero_ghost, update_var_def]
QED


Theorem prefix_prepare_assert_actual:
  emit_void ASSERT [a] st = ((),last) /\
  eval_operand a initial = SOME w /\ w <> 0w /\ op_taint tn a = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let t = initial with vs_inst_idx := LENGTH last.cs_current_insts
  in fresh_vars_wrt last t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG G tn t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `last.cs_current_bb = st.cs_current_bb /\
   last.cs_current_insts = st.cs_current_insts ++ [mk_inst st.cs_next_id ASSERT [a] []] /\
   last.cs_next_var = st.cs_next_var /\ last.cs_blocks = st.cs_blocks` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  `emitted_insts st last = [mk_inst st.cs_next_id ASSERT [a] []]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `frag_exec ctx st last (\s. s = initial)
     (\t. t = initial with vs_inst_idx := LENGTH last.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[run_inst_seq_def, step_inst_base_def,
       is_terminator_def, mk_inst_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  fs[fresh_vars_wrt_def] >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX last.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb initial.vs_inst_idx = SOME (mk_inst st.cs_next_id ASSERT [a] [])` by
    (gvs[IS_PREFIX_APPEND] >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  `lookup_block st.cs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx func PG G tn bb
      (initial with vs_inst_idx := SUC initial.vs_inst_idx)` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
     simp[ptr_safe_run_def, ADD1]) >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ASSERT [a] []) initial = OK initial` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  `~is_terminator (mk_inst st.cs_next_id ASSERT [a] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  `ptr_safe_block D lo fuel ctx func PG G tn bb initial` by
    (drule_all ptr_safe_block_step >> strip_tac >>
     fs[prefix_assert_ptr_step, prefix_assert_ghost_step] >> metis_tac[]) >>
  simp[ptr_safe_run_def]
QED




Theorem prefix_prepare_payable_layout:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),last) ==>
  cs_extends st last /\ st.cs_next_var <= last.cs_next_var
Proof
  Cases_on `payable` >>
  simp[comp_return_def,comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
       fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem prefix_prepare_region_layout:
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st = (imm,last) ==>
  cs_extends st last /\ st.cs_next_var <= last.cs_next_var
Proof
  Cases_on `cap > 0` >>
  simp[comp_return_def,comp_bind_def,comp_ignore_bind_def,compile_fixed_region_with_id_def,
       emit_op_def,fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

(* Same-witness semantic execution and ghost continuation through both optional stages. *)
