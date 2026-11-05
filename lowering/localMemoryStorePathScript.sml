(* Actual execution boundaries for stores into memory-backed locals. *)
Theory localMemoryStorePath
Ancestors
  stmtSimAssignMem stmtSimAssignStore vyperLookup valueCopy valueCopyBytes fragGasSeq fragGasMode fragExec
  context emitHelper emitHelperProps compileEnv exprLoweringProps loweringSlice
  list rich_list finite_map venomInst venomState exprSimProps arithmetic

Theorem compile_store_memory_compatible_no_gas[local]:
  !cenv src dst ty sty sa sb.
    compile_store_memory cenv src dst ty sty sa = ((),sb) /\
    ~is_word_type ty /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory cenv src dst ty ty sa = ((),sb)` by
    (Cases_on `ty = sty` >> gvs[] >>
     metis_tac[compile_store_memory_bytestring_src]) >>
  qpat_x_assum `compile_store_memory _ _ _ _ sty _ = _` kall_tac >>
  Cases_on `is_bytestring_type ty` >>
  gvs[compile_store_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, comp_bind_def, LET_THM,
      emit_op_def, fresh_var_def, emit_inst_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, emit_void_def, comp_return_def,
      emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[] >>
  rename1 `compile_copy_memory dst src n sa = ((),sb)` >>
  Cases_on `n` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def,
      emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      emit_def, emitted_insts_def, mk_inst_def, GSYM APPEND_ASSOC,
      DROP_LENGTH_APPEND]
QED

Theorem compile_store_memory_compatible_frame[local]:
  !cenv src dst ty sty sa sb s tenv tv stv v sw dw bound.
    compile_store_memory cenv src dst ty sty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type ty /\
    evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
    value_has_type tv v /\ val_wf tv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    (if is_bytestring_type ty then val_store_size tv v <= bound
     else type_memory_size tv <= bound) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + bound <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory cenv src dst ty ty sa = ((),sb) /\
   val_in_memory tv v (w2n sw) s.vs_memory` by
    (Cases_on `ty = sty` >- gvs[] >> gvs[] >> conj_tac
     >- metis_tac[compile_store_memory_bytestring_src] >>
     drule_all bytestring_val_in_memory_transfer >> simp[]) >>
  drule compile_store_memory_run_frame_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `tv`, `v`, `sw`, `dw`, `bound`] mp_tac) >>
  simp[]
QED

Theorem compile_store_memory_compatible_raw:
  !cenv src dst ty sty sa sb s tenv tv stv v sw dw.
    compile_store_memory cenv src dst ty sty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type ty /\
    evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
    value_has_type tv v /\ value_has_type stv v /\ val_wf tv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/
         w2n dw + MIN (type_memory_size stv) (type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule compile_store_memory_compatible_frame >>
  simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[] >>
  Cases_on `ty = sty`
  >- (gvs[] >> simp[val_store_size_le]) >>
  gvs[] >>
  `val_store_size tv v = val_store_size stv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_wf stv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  simp[MIN_DEF] >> metis_tac[val_store_size_le]
QED

Theorem compile_store_memory_compatible_path:
  !cenv src dst ty sty sa sb s tenv tv stv v sw dw ctx func.
    compile_store_memory cenv src dst ty sty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    ~is_word_type ty /\
    evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
    value_has_type tv v /\ val_wf tv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_compatible_no_gas >> strip_tac >>
  `(if is_bytestring_type ty then
      val_store_size tv v <= type_memory_size tv
    else type_memory_size tv <= type_memory_size tv)` by
    simp[val_store_size_le] >>
  drule_all compile_store_memory_compatible_frame >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb)
           (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
      LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  simp[gas_marked_path_def] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, same_blocks_def, lookup_var_def] >>
  asm_rewrite_tac[]
QED

(* The ancestor's immutable-copy helper is private. *)
Theorem local_copy_immutables[local]:
  stmt_state_rel ctx func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ n <= sz /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a len. a + len <= b \/ b + n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[] >> reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ id b sz ==> _` drule >> simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem local_memory_store_raw_rel:
  !ctx func cenv cx es s t id p sz pre env entry rest v sa dw stv.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dw /\ local_ptrs_reserved cenv sa /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a len. a + len <= w2n dw \/
      w2n dw + MIN (type_memory_size stv) (type_memory_size entry.type) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `local_backed func p s (w2n dw) sz /\ w2n dw + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `local_region cenv es.scopes s id (w2n dw) sz` by simp[local_region_def] >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[MIN_DEF] >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule stmt_state_rel_write_local >>
  goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >> simp[] >>
  qexistsl [`s`, `dw`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at _ x ==> _` irule >>
      fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. a + len <= _ \/ _ + type_memory_size _ <= a ==> _`
        irule >> decide_tac) >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem local_memory_store_path:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv sty stv.
    compile_store_memory cenv src (Var p) ty sty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!a len. a + len <= w2n dw \/
           w2n dw + MIN (type_memory_size stv) (type_memory_size tyv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  drule_all compile_store_memory_compatible_raw >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
    (es with scopes :=
      pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule local_memory_store_raw_rel >>
     goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >> simp[] >>
     qexistsl [`dw`, `s`, `sa`, `stv`] >> simp[] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule_all compile_store_memory_compatible_no_gas >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb)
           (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
      LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  simp[gas_marked_path_def] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, same_blocks_def, lookup_var_def,
      stmt_state_rel_inst_idx] >> asm_rewrite_tac[]
QED
