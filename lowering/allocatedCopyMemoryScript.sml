(* Memory counting for same-type stores between allocated regions. *)
Theory allocatedCopyMemory
Ancestors
  bodyCopyMemory bodyDeclMemoryCore exprSimBufferStore exprSimMemUnwrap
  exprLowering context compileEnv loweringPosts exprSimMemDefs exprSimProps
  valueEncodingProps emitHelperProps emitHelper instMemFrontier memSafeRun
  fragExecMem exprLoweringProps venomInst venomState list rich_list

Theorem allocated_store_memory_mem_ok:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ ~is_bytestring_type ty ==>
   !sw. eval_operand src s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >> gvs[]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory tv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  Cases_on `is_bytestring_type ty`
  >- (`?len. mload (w2n sw) s = n2w len /\
             val_store_size tv v = 32 + 32 * word_size len` by
        metis_tac[buffer_typed_bytestring_header] >>
      `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
      `w2n sw + val_store_size tv v <= s.vs_alloca_next` by
        (fs[expr_store_bound_def] >>
         qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
      gvs[compile_store_memory_def] >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `sw`] >> simp[] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `type_memory_size tv = 0`
  >- gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
         emitted_insts_def, run_inst_seq_mem_ok_def] >>
  `w2n sw + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  gvs[compile_store_memory_def] >> irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `sw`] >> simp[]
QED

Theorem allocated_store_memory_no_gas:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `is_word_type ty` >>
  Cases_on `is_bytestring_type ty` >>
  gvs[compile_store_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, compile_copy_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def] >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
      emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

Theorem allocated_store_memory_path_mem:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ ~is_bytestring_type ty ==>
   !sw. eval_operand src s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule allocated_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     simp[] >> qexists `v` >> fs[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  drule_all (SRULE [] buffer_store_memory_encoding) >> strip_tac >>
  gvs[] >> rename1 `run_inst_seq _ s = OK t` >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule allocated_store_memory_no_gas >> strip_tac >>
  drule_all exprSimMemUnwrapTheory.straight_path_mem >> simp[]
QED
