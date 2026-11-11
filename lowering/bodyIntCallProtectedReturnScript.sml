(* Protected regions and reserved operands across reachable Return suffixes. *)
Theory bodyIntCallProtectedReturn
Ancestors
  bodyIntCallReachableReturn bodyIntCallReturnCopy valueCopy compileEnv loweringStateRelDefs exprLoweringProps
  exprSimDefs intCallReturnMem fragExec emitHelper instIdxIndep rich_list
  fragGasPath vyperContext loweringPosts intCallResult
  stmtLowering stmtSimDefs context finite_map vyperState
  valueEncoding venomState venomExecSemantics venomInst emitHelperProps
  vyperTyping words list

Theorem protected_store_memory_run:
  !cenv src dst ty sa sb s tenv tv v sw dw P reserved.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\
    (!b sz. P b sz ==> regions_disjoint b sz (w2n dw) (type_memory_size tv)) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      val_in_memory tv v (w2n dw) u.vs_memory /\
      (!b sz. P b sz ==>
        mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
      (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  rpt strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      metis_tac[regions_disjoint_def]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, venom_state_component_equality]) >>
  gvs[venom_state_component_equality]
QED

Theorem protected_store_memory_ret_path:
  compile_store_memory ce src dst ty ty sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!b sz. P b sz ==> regions_disjoint b sz (w2n bw) (type_memory_size tv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?n ir u. gas_path ctx func s n (IntRet ir u) /\
    (!b sz. P b sz ==> mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all protected_store_memory_run >> strip_tac >>
  `eval_operand rpc u = SOME pc` by
    (drule_all store_result_operand_frame >> simp[]) >>
  `sm.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  qpat_assum `fn_has_code sa sm func`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id RET [rpc] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  qspecl_then [`sm`, `sb`, `func`, `[mk_inst sm.cs_next_id RET [rpc] []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (s.vs_inst_idx + LENGTH (emitted_insts sa sm)) =
     SOME (mk_inst sm.cs_next_id RET [rpc] [])` by
    (gvs[same_blocks_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    gvs[venom_state_component_equality] >>
  `gas_path ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS)
      (emitted_insts sa sm)))
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)))` by
    (irule run_inst_seq_ret_path >> simp[] >>
     qexistsl_tac [`sm.cs_next_id`, `rpc`] >> gvs[]) >>
  goal_assum (drule_at Any) >>
  gvs[eval_op_inst_idx, venom_state_component_equality]
QED

Theorem protected_internal_memory_return_counted:
  compile_internal_return ce (SOME src) rpc 0 ty ty elems (SOME dst) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx (es with scopes := []) s /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!b sz. P b sz ==> regions_disjoint b sz (w2n bw) (type_memory_size tv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?n ir u. gas_path ctx func s n (IntRet ir u) /\
    intret_mem_q func ce cx tv bw v (es with scopes := []) (IntRet ir u) /\
    (!b sz. P b sz ==> mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `?sm. compile_store_memory ce src dst ty ty sa = ((),sm) /\
        emit_inst RET [rpc] [] sm = ((),sb)` by
    (qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
     Cases_on `compile_store_memory ce src dst ty ty sa` >>
     rename1 `compile_store_memory _ _ _ _ _ _ = (unit,sm)` >>
     Cases_on `unit` >> simp[] >> metis_tac[]) >>
  `cs_extends sa sm` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     first_x_assum drule >> strip_tac >>
     drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `?n ir u. gas_path ctx func s n (IntRet ir u) /\
    (!b sz. P b sz ==> mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule protected_store_memory_ret_path >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `ir`, `u`] >> simp[] >>
  drule_all compile_internal_return_memory_size_bound_frag >>
  disch_then (mp_tac o SPEC_ALL) >> strip_tac >>
  drule exit_fragment_path_post >> simp[exit_result_def] >>
  disch_then irule >> simp[exit_result_def] >>
  qexistsl_tac [`func`, `n`, `s`] >> simp[]
QED
