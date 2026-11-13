(* Stack-word argument staging leaves the return-buffer allocation as the
   sole instruction before INVOKE.  Its owner is recovered at that execution. *)
Theory tupleAssignImmutableDeployIntEntryWord
Ancestors
  exprSimAlloc exprSimConcatResult loweringHalt exprLowering exprLoweringProps
  fragGasMode loweringStateRelDefs compileEnv venomState venomInst
  finite_map list rich_list

Theorem word_stage_shape[local]:
  !vals flags tys ce sa ops sb.
    LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
    EVERY I flags /\
    EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals /\
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) ==>
    sb = sa /\
    ops = MAP (\vv. case vv of StackValue ty op => op
                            | LocatedValue ty p => p.ptr_operand) vals
Proof
  Induct >> simp[compile_stage_intcall_args_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `flags` >> Cases_on `tys` >> gvs[] >>
  gvs[compile_stage_intcall_args_def, unwrap_value_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem tuple_immutable_intcall_word_entry_owned:
  compile_alloc_buffer sz st1 = (buf,st2) /\
  compile_stage_intcall_args ce vals flags tys st2 = (arg_ops,st3) /\
  LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
  EVERY I flags /\
  EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals /\
  fn_has_code st1 st3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st1 /\ stmt_state_rel ctx func ce cx es s /\
  sz < dimword (:256) /\ origin.cs_next_id <= st1.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st1.cs_current_bb /\
  s.vs_inst_idx = LENGTH st1.cs_current_insts ==>
  ?t b.
    gas_marked_path F ctx func s 0 (OK t) /\
    FLOOKUP t.vs_allocas st1.cs_next_id = SOME (b,sz) /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    b + sz < dimword (:256) /\
    origin.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id < st3.cs_next_id /\
    ~t.vs_halted /\ t.vs_current_bb = st3.cs_current_bb /\
    t.vs_inst_idx = LENGTH st3.cs_current_insts /\
    (!name lb lsz. local_region ce es.scopes t name lb lsz ==>
      b + sz <= lb \/ lb + lsz <= b) /\
    (!x. not_fresh_at st1 x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\
    arg_ops = MAP (\vv. case vv of StackValue ty op => op
                                | LocatedValue ty p => p.ptr_operand) vals
Proof
  strip_tac >> drule_all word_stage_shape >> strip_tac >> gvs[] >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts st1 st2 =
    [mk_inst st1.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString st1.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  drule concat_straight_gas_path >>
  disch_then (qspecl_then [`ctx`, `s`, `t`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  qexistsl [`t with vs_inst_idx := LENGTH st2.cs_current_insts`, `w2n w`] >>
  gvs[gas_marked_path_def, eval_operand_def, lookup_var_def,
      regions_disjoint_def, local_region_def] >> metis_tac[]
QED
