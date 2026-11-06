(* Shared concrete execution endpoints for local tuple copies. *)
Theory assignTuplePtrLocalCopyRun
Ancestors
  fragGasSeqPtr fragGasPathPtr tupleTargetStoreRun tupleTargetStoreProps
  valueCopy valueEncodingProps stmtSimProps stmtSimDefs loweringPosts
  stmtLowering exprLowering exprLoweringProps context compileEnv
  venomState venomExecSemantics venomInst fragExec emitHelper emitHelperProps
  finite_map rich_list list arithmetic localPtrsProps vyperState
  loweringSlice exprSimProps stmtSimAssignStore tupleLocalStoreRun vyperLookup

Theorem emitted_sequence_path_ptr:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists `l` >> REFL_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
    LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  simp[]
QED

Theorem tuple_local_copy_run_state_ptr:
  compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  val_in_memory entry.type v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv ty = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?dw. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) u /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `if is_bytestring_type ty then val_store_size entry.type v <= type_memory_size entry.type
   else type_memory_size entry.type <= type_memory_size entry.type` by
    (simp[] >> metis_tac[val_store_size_le]) >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  `(if is_word_type ty then sw = typed_val_to_w256 entry.type v
    else val_in_memory entry.type v (w2n sw) s.vs_memory)` by simp[] >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq _ s = OK u` >>
  reverse conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  irule stmt_state_rel_write_local >>
  first_assum (irule_at Any) >> simp[] >>
  qexists `s` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `u.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `u with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  irule immutables_rel_mem_agree >> qexists `s` >> simp[] >>
  reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) (w2n dw) sz` by
    (qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ id b sz ==> _` drule >> simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem tuple_local_copy_code_shape_ptr:
  compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
  simp[compile_store_memory_def] >> rpt strip_tac >>
  Cases_on `type_memory_bytes cenv ty` >>
  gvs[compile_copy_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, DROP_APPEND1,
       mk_inst_def, is_terminator_def]
QED
