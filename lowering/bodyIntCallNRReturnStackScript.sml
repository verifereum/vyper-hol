(* Count the decoded stack-result store after restoring the caller successor.
   The resource reference is the restored successor s, not the INVOKE state t. *)
Theory bodyIntCallNRReturnStack
Ancestors
  bodyIntCallFamCallIntReturnRun fragGasPath compileEnv
  intCallResult loweringStateRelDefs exprLoweringProps venomState
  finite_map list rich_list

Theorem intcall_decoded_stack_return:
  store_multi_results buf.buf_operand results 0 si = ((),sb) /\
  local_ptrs_reserved ce si /\
  buf.buf_operand = Var p /\ not_fresh_at si p /\
  (!x. MEM (Var x) results ==> not_fresh_at si x) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\ value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
  intret_vals_match tv v ws /\ ws <> [] /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 es' sa s0 s /\
  sa.cs_next_var <= si.cs_next_var /\
  eval_operand buf.buf_operand s = SOME w /\
  MAP (\op. eval_operand op s) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!id lb lsz. local_region ce es'.scopes s id lb lsz ==>
    w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (!id lb lsz. local_region ce es0.scopes s0 id lb lsz ==>
    local_region ce es'.scopes s id lb lsz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint (w2n w) (32 * LENGTH results) off
      (type_memory_size itv)) /\
  allocas_above lo s /\
  (!a k. P a k ==> a + k <= w2n w \/ w2n w + 32 * LENGTH results <= a) /\
  fn_has_code si sb func /\ ~s.vs_halted /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_path ctx func t n (OK s) ==>
  ?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts si sb)))
      (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es' out /\ wb_frame ce es0 es' sa s0 out /\
    eval_operand buf.buf_operand out = SOME w /\
    val_in_memory tv v (w2n w) out.vs_memory /\
    FLOOKUP out.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
    (!id lb lsz. local_region ce es'.scopes out id lb lsz ==>
      w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
    allocas_above lo out /\ out.vs_allocas = s.vs_allocas /\
    out.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at si x ==> lookup_var x out = lookup_var x s) /\
    (!a k. P a k ==> mem_bytes_at a k out.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule_all intcall_stack_buffer_run_resources >> strip_tac >>
  drule_all intcall_store_run_counted_resources >> strip_tac >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  conj_tac
  >- (irule gas_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
