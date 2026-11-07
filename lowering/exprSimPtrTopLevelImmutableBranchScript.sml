(* Compiler and source interfaces for runtime immutable aggregate names. *)
Theory exprSimPtrTopLevelImmutableBranch
Ancestors
  exprSimPtrTopLevelImmutablePost exprSimPtrTopLevelImmutableCopy exprSimTopLevelImmutable exprSimPtrTopLevelStorageAlloc
  exprSimSource exprSimUnwrapProps vyperInterpreter vyperState vyperValueOperation
  exprSimHyps exprSimHypsDefs exprSimCopy exprSimStorageCopy exprLowering exprLoweringProps
  exprSimProps context compileEnv fragExec emitHelperProps immutableCopyExecution
  loweringPosts vyperAST venomState words list venomInst venomExecSemantics instIdxIndep rich_list

Theorem toplevel_immutable_branch_compile:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann /\
  ~cenv.ce_is_ctor /\
  lower_value compile_expr cenv ty (TopLevelName ann (src,id)) sa = (op,sb) ==>
  type_memory_bytes cenv ann = 32*type_slot_size tv /\
  type_memory_size tv = type_memory_bytes cenv ann /\
  type_memory_bytes cenv ann < dimword (:256) /\
  ?buf sm.
    compile_alloc_buffer (type_memory_bytes cenv ann) sa = (buf,sm) /\
    compile_imm_copy_to_memory F cenv.ce_imm_alloca (Lit (n2w off))
      buf.buf_operand (type_slot_size tv) 0 sm = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  `expr_body_pre cenv cx env (TopLevelName ann (src,id)) es` by
    metis_tac[expr_sim_pre_body_pre] >>
  drule_all toplevel_storage_copy_capacity >> strip_tac >>
  drule_all toplevel_storage_copy_word_count >> strip_tac >>
  `type_memory_size tv = type_memory_bytes cenv ann` by
    (drule expr_body_pre_copy_ok >> simp[expr_type_def]) >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, mk_ptr_def,
       compile_ensure_in_memory_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> Cases_on `_0` >> gvs[]
QED

Theorem toplevel_immutable_copy_memory_frame:
  compile_imm_copy_to_memory F imm (Lit a) (Var root) (type_slot_size tv) 0 sa = ((),sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME w /\
  immutable_copy_ghost_frame sa s G tn sb t H tm 0 (32*type_slot_size tv) w /\
  w2n a + type_memory_size tv < dimword (:256) /\
  w2n w + type_memory_size tv < dimword (:256) ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size tv <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >>
  `copy_old_operand sa (Lit a) /\ copy_old_operand sa (Var root) /\
   eval_operand (Lit a) s = SOME a /\ eval_operand (Var root) s = SOME w` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all copy_runtime_run >> strip_tac >>
  `s' = t` by gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  irule runtime_code_copy_memory_frame >> metis_tac[]
QED

Theorem toplevel_immutable_branch_value_post:
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  off+type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx fn cenv cx es s ==>
  vv_post ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s
    (es with gas_obs := []) (Value v)
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s
Proof
  strip_tac >>
  `read_result cx (PlaceR (ImmutablePlace src id []))
     (es with gas_obs := []) = (INL v,es with gas_obs := [])` by
    gvs[read_result_def, read_place_def, get_immutables_def,
      get_address_immutables_def, lift_option_type_def, bind_def, return_def,
      evaluate_subscripts_def, lift_sum_def] >>
  drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
  irule toplevel_immutable_post >> simp[] >> metis_tac[]
QED

Theorem toplevel_immutable_expr_post_inst_idx[local,simp]:
  expr_post ctx fn ce cx e es sa sb s0 es' v op (s with vs_inst_idx := k) <=>
  expr_post ctx fn ce cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def, lookup_var_def,
       stmt_state_rel_inst_idx, local_region_def]
QED

Theorem toplevel_immutable_run_expr_post:
  unwrap_value cenv (LocatedValue ann p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type ann /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
        type_memory_bytes cenv ann = type_memory_size tv) /\
  vv_post ctx fn cenv cx e es sa sm s0 es' (Value v) (LocatedValue ann p) s /\
  run_inst_seq (emitted_insts sm sb) (s with vs_inst_idx := k) = OK t ==>
  expr_post ctx fn cenv cx e es sa sb s0 es' v op t
Proof
  strip_tac >>
  `ann = post_value_type cenv e` by gvs[vv_post_def, vv_holds_def] >>
  gvs[] >> drule_all runtime_code_copy_run_post_physical >> strip_tac >>
  `code = emitted_insts sm sb` by gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def]) >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`s`,`k`] mp_tac) >>
  simp[exec_result_map_def] >> strip_tac >> gvs[]
QED

Theorem toplevel_immutable_alloc_copy_sequence:
  compile_alloc_buffer nb sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  immutable_copy_ghost_frame sm (u with vs_inst_idx := k)
    (Ga:(string,num # num) fmap) ta sb t H tm off nb (w:bytes32) ==>
  run_inst_seq (emitted_insts sa sb) (s with vs_inst_idx := k) = OK t
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq (emitted_insts sa sm) (s with vs_inst_idx := k) =
    OK (u with vs_inst_idx := k)` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`,`k`] mp_tac) >> simp[exec_result_map_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
         IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  simp[] >> drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
  fs[immutable_copy_ghost_frame_def, copy_runtime_frame_def]
QED

Theorem toplevel_immutable_alloc_copy_code:
  compile_alloc_buffer nb sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n off sm = ((),sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code sa sm fn /\ fn_has_code sm sb fn
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  drule code_copy_insts >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, emitted_blocks_def] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS]
QED

Theorem toplevel_immutable_alloc_endpoint_bound:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ nb < dimword (:256) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  eval_operand buf.buf_operand u = SOME w ==>
  w2n w+nb < dimword (:256)
Proof
  strip_tac >>
  drule_all (runtime_code_copy_alloc_run |>
    Q.INST [`src` |-> `Lit (0w:bytes32)`, `a` |-> `0w:bytes32`] |>
    SRULE[eval_operand_def]) >> strip_tac >> gvs[]
QED

Theorem toplevel_immutable_endpoint_value_post[local]:
  unwrap_value cenv (LocatedValue ann (mk_ptr (Lit a) LocCode)) sa = (Var p,sb) /\
  ~cenv.ce_is_ctor /\ ~is_word_type ann /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  type_memory_bytes cenv ann = type_memory_size tv /\
  vv_post ctx fn cenv cx (TopLevelName ann nsid) es sa sa s0
    (es with gas_obs := []) (Value v) (LocatedValue ann (mk_ptr (Lit a) LocCode)) s0 /\
  run_inst_seq (emitted_insts sa sb) (s0 with vs_inst_idx := k) = OK t /\
  lookup_var p t = SOME w ==>
  expr_post ctx fn cenv cx (TopLevelName ann nsid) es sa sb s0
    (es with gas_obs := []) v (Var p) t /\
  val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory
Proof
  strip_tac >>
  `expr_post ctx fn cenv cx (TopLevelName ann nsid) es sa sb s0
     (es with gas_obs := []) v (Var p) t` by
    (irule toplevel_immutable_run_expr_post >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl [`ann`,`k`,`mk_ptr (Lit a) LocCode`,`s0`,`sa`] >>
     simp[mk_ptr_def] >> gvs[]) >>
  simp[] >> gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
    expr_type_def, eval_operand_def] >> metis_tac[]
QED

Theorem toplevel_immutable_return_buf_cursor[local,simp]:
  return_buf_ptr d ce G tn (s with vs_inst_idx := k) <=>
  return_buf_ptr d ce G tn s
Proof
  Cases_on `d` >> simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
  rename1 `SOME z` >> PairCases_on `z` >>
  simp[bodyPtrDefsTheory.return_buf_ptr_def, bodyPtrDefsTheory.ptr_covers_def,
       lookup_var_def]
QED

Theorem toplevel_immutable_ghost_cursor[local,simp]:
  ghost_inv d ce cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv d ce cx es G tn s
Proof
  simp[bodyPtrDefsTheory.ghost_inv_def, bodyPtrDefsTheory.ptr_covers_def,
       bodyPtrDefsTheory.stor_taint_ok_def, lookup_var_def]
QED

Theorem toplevel_immutable_value_cursor[local,simp]:
  ptr_val_ok cx ann v op G tn (s with vs_inst_idx := k) <=>
  ptr_val_ok cx ann v op G tn s
Proof
  simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def]
QED

Theorem toplevel_immutable_buffer_cursor[local,simp]:
  ptr_buf_ok ce e op G (s with vs_inst_idx := k) <=> ptr_buf_ok ce e op G s
Proof
  simp[bodyPtrDefsTheory.ptr_buf_ok_def]
QED

Theorem toplevel_immutable_sequence_bb[local]:
  compile_alloc_buffer nb sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n off sm = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  drule code_copy_insts >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND, DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by
    (gvs[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def,
         IS_PREFIX_APPEND, EVERY_MEM, is_terminator_def] >>
     rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  reverse conj_tac >- gvs[same_blocks_def] >>
  irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `step_inst 0 ARB i ss1 = OK ss2` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  metis_tac[venomInstProofsTheory.step_preserves_control_flow]
QED

Theorem compile_toplevel_immutable_aggregate_sim_ptr:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  off+type_memory_size tv < dimword (:256) /\ ~is_word_type ann ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[bodyPtrDefsTheory.expr_sim_ptr_def] >>
  `vv_post ctx fn cenv cx (TopLevelName ann (cenv.ce_module,id)) es sa sa s0
    (es with gas_obs := []) (Value v)
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s0` by
    (irule toplevel_immutable_branch_value_post >> simp[] >> metis_tac[]) >>
  drule_all toplevel_immutable_branch_compile >> strip_tac >>
  drule_all toplevel_immutable_alloc_copy_code >> strip_tac >>
  `compile_alloc_buffer (32*type_slot_size tv) sa = (buf,sm) /\
   32*type_slot_size tv < dimword (:256)` by metis_tac[] >>
  drule_all toplevel_immutable_alloc_copy_run >>
  disch_then (qspecl_then [`tn0`,`PG`,`G0`,`cx_dead cx`] strip_assume_tac) >>
  `unwrap_value cenv (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) sa =
     (Var p,sb)` by
    (drule compile_toplevel_immutable_ptr >>
     disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >>
     gvs[lower_value_def, comp_bind_def]) >>
  `run_inst_seq (emitted_insts sa sb)
     (s0 with vs_inst_idx := LENGTH sm.cs_current_insts) = OK t` by
    (irule toplevel_immutable_alloc_copy_sequence >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `type_memory_bytes cenv ann = type_memory_size tv` by metis_tac[] >>
  drule_all toplevel_immutable_endpoint_value_post >> strip_tac >>
  qpat_x_assum `type_memory_bytes cenv ann = type_memory_size tv` kall_tac >>
  `val_store_size tv v <= 32*type_slot_size tv` by
    (drule val_store_size_le >> decide_tac) >>
  `ptr_val_ok cx ann v (Var p) H tm t /\
   ptr_vv_ok cx ann (Value v) (StackValue ann (Var p)) es H tm t /\
   ptr_buf_ok cenv (TopLevelName ann (cenv.ce_module,id)) (Var p) H t` by
    (irule toplevel_immutable_clean_pointer_post >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME w` by simp[eval_operand_def] >>
  `w2n w+type_memory_size tv < dimword (:256)` by
    (drule_all toplevel_immutable_alloc_endpoint_bound >> gvs[]) >>
  suspend "immutable_endpoint_finish"
QED

Resume compile_toplevel_immutable_aggregate_sim_ptr[immutable_endpoint_finish]:
  `not_fresh_at sm p` by metis_tac[cj 7 storage_copy_alloc_layout] >>
  `w2n ((n2w off):bytes32)+type_memory_size tv < dimword (:256)` by
    (simp[w2n_n2w] >> `off < dimword (:256)` by decide_tac >> simp[]) >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory /\
   (!i len. i+len <= w2n w \/ w2n w+type_memory_size tv <= i ==>
     mem_bytes_at i len t.vs_memory = mem_bytes_at i len u.vs_memory)` by
    (`compile_imm_copy_to_memory F cenv.ce_imm_alloca (Lit (n2w off))
        (Var p) (type_slot_size tv) 0 sm = ((),sb)` by metis_tac[] >>
     `lookup_var p (u with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME w` by
       gvs[lookup_var_def] >>
     drule_all toplevel_immutable_copy_memory_frame >> strip_tac >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!i. i < w2n w \/ w2n w+32*type_slot_size tv <= i ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory` by
    (rpt strip_tac >> `i+1 <= w2n w \/ w2n w+type_memory_size tv <= i` by
       (gvs[] >> decide_tac) >> metis_tac[]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) H tm t` by
    (irule (INST_TYPE [alpha |-> ``:256``] toplevel_immutable_alloc_copy_ghost_inv) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl [`32*type_slot_size tv`,`w`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ghost_kept cenv es sa G0 tn0 s0 H tm` by
    (irule exprSimPtrLiteralBufferTheory.literal_ghost_kept >> simp[] >> metis_tac[]) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`,`es`,`H`,`tm`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[] >> conj_tac
  >- (simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
           return_def, raise_def, read_result_def, read_place_def,
           get_immutables_def, get_address_immutables_def,
           evaluate_subscripts_def, lift_sum_def]) >>
  gvs[expr_type_def] >>
  qpat_x_assum `buf.buf_operand = Var p`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  drule_all toplevel_immutable_sequence_bb >> simp[]
QED

Finalise compile_toplevel_immutable_aggregate_sim_ptr
