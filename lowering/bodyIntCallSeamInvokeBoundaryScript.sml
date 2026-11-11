(* Static INVOKE boundary, independent of argument evaluation and staging. *)
Theory bodyIntCallSeamInvokeBoundary
Ancestors
  bodyIntCallCompletedModes bodyIntCallEmitBoundary emitHelperProps
  fragExec fcgDefs venomExecSemantics venomInst venomState compileEnv
  list rich_list

Theorem emitted_invoke_boundary:
  fn_has_code sm sn func /\
  sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++
    [mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs] ==>
  MEM (mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs) (fn_insts func) /\
  (!t. t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)) /\
  (!ctx. lookup_function func.fn_name ctx.ctx_functions = SOME func ==>
    fn_directly_calls ctx func.fn_name lbl)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
    SOME (mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs)
     bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `MEM (mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs) (fn_insts func)` by
    metis_tac[lookup_block_fn_insts] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[mk_inst_def, decode_invoke_def]) >>
  rpt strip_tac >> simp[fn_directly_calls_def] >>
  qexistsl_tac [`mk_inst sm.cs_next_id INVOKE (Label lbl::ops) outs`,`ops`] >>
  simp[mk_inst_def]
QED

Theorem emitted_void_invoke_boundary:
  emit_void INVOKE (Label lbl::ops) sm = (u,sn) /\
  fn_has_code sm sn func ==>
  (!t. t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)) /\
  (!ctx. lookup_function func.fn_name ctx.ctx_functions = SOME func ==>
    fn_directly_calls ctx func.fn_name lbl)
Proof
  Cases_on `u` >> strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_void_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  drule_all emitted_invoke_boundary >> metis_tac[]
QED

Theorem emitted_multi_invoke_boundary:
  emit_multi_op INVOKE (Label lbl::ops) nret sm = (results,sn) /\
  fn_has_code sm sn func ==>
  (!t. t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)) /\
  (!ctx. lookup_function func.fn_name ctx.ctx_functions = SOME func ==>
    fn_directly_calls ctx func.fn_name lbl)
Proof
  strip_tac >> drule emit_multi_op_result >> strip_tac >>
  drule emitted_invoke_boundary >>
  disch_then (qspecl_then [`outs`,`ops`,`lbl`] mp_tac) >>
  (impl_tac >- gvs[]) >> metis_tac[]
QED
