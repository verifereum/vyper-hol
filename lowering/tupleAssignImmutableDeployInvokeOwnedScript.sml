(* Actual INVOKE execution and owned tuple-return continuations. *)
Theory tupleAssignImmutableDeployInvokeOwned
Ancestors
  tupleAssignImmutableDeployIntMemoryOwned
  tupleAssignImmutableDeployIntStackOwned intCallStep fragGasPath fragGasMode
  venomState venomExecSemantics loweringStateRelDefs intCallFrame
  bodyIntCallSeams exprSimCopy exprSimDefs list rich_list

Theorem invoke_owned_step[local]:
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops t = SOME argv /\ setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs' /\
  LENGTH inst.inst_outputs = LENGTH ir.iret_values ==>
  ?u. bind_outputs inst.inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state t cs')) = SOME u /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
    ~u.vs_halted /\
    gas_marked_path F ctx func t (gas_count_step fuel ctx inst t)
      (OK (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >> drule_all step_inst_invoke_intret >> strip_tac >>
  rename1 `step_inst fuel ctx inst t = OK u` >>
  `u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
   u.vs_halted = t.vs_halted` by metis_tac[step_inst_invoke_OK_control] >>
  qexists `u` >> simp[gas_marked_path_def] >>
  `gas_path_edge ctx func t (gas_count_step fuel ctx inst t)
    (OK (u with vs_inst_idx := SUC t.vs_inst_idx))` by
    (simp[gas_path_edge_def] >> qexists `fuel` >>
     simp[venomInstTheory.is_terminator_def]) >>
  `~(u with vs_inst_idx := SUC t.vs_inst_idx).vs_halted` by simp[] >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_0]
QED

Theorem tuple_immutable_invoke_memory_owned_path:
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops t = SOME argv /\ setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs' /\
  LENGTH inst.inst_outputs = LENGTH ir.iret_values /\
  intcall_callee_exit func ce cx rtv 0 (SOME w) n t (INL v) ee (IntRet ir cs') /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
  (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!name lb lsz. local_region ce scopes t name lb lsz ==>
    w2n w + sz <= lb \/ lb + lsz <= w2n w) ==>
  ?u. gas_marked_path F ctx func t (gas_count_step fuel ctx inst t) (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb /\
    u.vs_inst_idx = SUC t.vs_inst_idx /\
    eval_operand p.ptr_operand u = SOME w /\ p.ptr_location = LocMemory /\
    FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
    origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
    type_memory_bytes ce (TupleT stys) <= sz /\
    val_in_memory rtv v (w2n w) u.vs_memory /\
    (!name lb lsz. local_region ce scopes u name lb lsz ==>
      w2n w + sz <= lb \/ lb + lsz <= w2n w)
Proof
  strip_tac >> drule_all invoke_owned_step >> strip_tac >>
  drule_all tuple_immutable_memory_return_owned >> strip_tac >>
  qexists `u with vs_inst_idx := SUC t.vs_inst_idx` >>
  simp[eval_operand_def, lookup_var_def, local_region_def] >>
  gvs[local_region_def, lookup_var_def] >> metis_tac[]
QED

(* Source restoration is a separate full-call obligation. Here it is supplied
   only at the concrete bind result; no ownership or path is assumed there. *)
Theorem tuple_immutable_invoke_stack_owned_path:
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops t = SOME argv /\ setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs' /\
  LENGTH inst.inst_outputs = LENGTH ir.iret_values /\ ALL_DISTINCT inst.inst_outputs /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs')) = SOME returned /\
  intcall_callee_exit func cenv cx (TupleTV tvs) ret_count NONE n t (INL v) ee
    (IntRet ir cs') /\ 0 < ret_count /\
  results = MAP Var inst.inst_outputs /\
  store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
  local_ptrs_reserved cenv sa /\
  (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
  (!x. MEM x inst.inst_outputs ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv si /\
  (!x. MEM x inst.inst_outputs ==> ~not_fresh_at si x) /\
  (!x. rbuf.buf_operand = Var x ==> ~MEM x inst.inst_outputs) /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) v /\
  EVERY (\etv. ?t'. is_word_type t' /\
    evaluate_type (get_tenv cx) t' = SOME etv) tvs /\
  stmt_state_rel ctx func cenv cx es
    (returned with vs_inst_idx := SUC t.vs_inst_idx) /\
  eval_operand rbuf.buf_operand t = SOME w /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
     w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint (w2n w) (32 * LENGTH results) off (type_memory_size itv)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = sa.cs_current_bb /\
  SUC t.vs_inst_idx = LENGTH sa.cs_current_insts /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  type_memory_bytes cenv (TupleT stys) <= sz /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
     w2n w + sz <= lb \/ lb + lsz <= w2n w) ==>
  ?u. gas_marked_path F ctx func t (gas_count_step fuel ctx inst t) (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\
    vv_holds cenv cx (TupleT stys) (Value v)
      (LocatedValue (TupleT stys) (base_ptr rbuf)) es u /\
    eval_operand rbuf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
    origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    type_memory_bytes cenv (TupleT stys) <= sz /\
    (!name lb lsz. local_region cenv es.scopes u name lb lsz ==>
       w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all invoke_owned_step >> strip_tac >>
  `u = returned` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  drule_all bind_outputs_lookup >> strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  `returned.vs_labels = t.vs_labels` by
    (Cases_on `ir.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `eval_operand rbuf.buf_operand returned = SOME w` by
    (Cases_on `rbuf.buf_operand` >> gvs[eval_operand_def]) >>
  qpat_x_assum `returned = _ with vs_vars := _` kall_tac >>
  `MAP (\op. eval_operand op returned) (MAP Var inst.inst_outputs) =
     MAP SOME ir.iret_values` by
    (irule LIST_EQ >> simp[EL_MAP, eval_operand_def]) >>
  `!x. not_fresh_at si x ==> lookup_var x returned = lookup_var x t` by
    metis_tac[] >>
  `!name lb lsz. local_region cenv es.scopes returned name lb lsz ==>
      local_region cenv es.scopes t name lb lsz` by
    (rpt strip_tac >> drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  `intret_vals_match (TupleTV tvs) v ir.iret_values /\ ir.iret_values <> []` by
    (gvs[intcall_callee_exit_def, expr_exit_def] >> strip_tac >> gvs[]) >>
  `!name lb lsz. local_region cenv es.scopes
      (returned with vs_inst_idx := LENGTH sa.cs_current_insts) name lb lsz <=>
      local_region cenv es.scopes returned name lb lsz` by
    simp[local_region_def, lookup_var_def] >>
  mp_tac (Q.INST [`results` |-> `MAP Var inst.inst_outputs`,
    `s0` |-> `returned with vs_inst_idx := LENGTH sa.cs_current_insts`,
    `ws` |-> `ir.iret_values`] tuple_immutable_stack_return_owned_path) >>
  (impl_tac >- (simp[MEM_MAP, eval_operand_def, lookup_var_def] >>
                rpt conj_tac >> rpt strip_tac >> metis_tac[])) >>
  disch_then (qx_choose_then `sfinal` strip_assume_tac) >>
  qexists `sfinal` >> simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `!n lb lsz. local_region _ _ sfinal n lb lsz ==> _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  `gas_marked_path F ctx func t (gas_count_step fuel ctx inst t + 0)
     (OK sfinal)` suffices_by simp[] >>
  irule gas_marked_path_then >>
  qexists `returned with vs_inst_idx := LENGTH sa.cs_current_insts` >> simp[]
QED
