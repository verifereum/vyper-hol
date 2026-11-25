(* The copied base only allocates, unwraps and stores at the same type. *)
Theory entryCreateSubscriptSnapshot
Ancestors
  createSizeConcreteSnapshots entryCreateEffectFocus compilerInstructionSuffix
  exprSimAbiGasBridge exprLoweringProps exprLowering loweringShapeDefs
  context emitHelper compileEnv fragExec list rich_list pair venomInst bodySim
  createCtorMaterializeSource createCtorMaterializeStore entryCreateSnapshotBandPrefix
  entryCreateSubscriptSnapshotLayout gasShadowCompileConvert exprSimSubscriptArray
  bodyFullIfExpReach abiEncodeArgsCase abiEncodeMaterialize exprOperandVar exprSimProps
  gasOriginPtrLabels bodyFullPathHistory bodyFullHashKeccakFixed abiBufferAllocationCode
  aggregateEvaluatedLayout relation exprSimSubscriptArraySource bodySimExprCases
  exprSimSource exprSimHyps vyperStorageFootprint stmtLoweringMono gasShadowState
  bodyPtrDefs loweringPosts bodyMemoryDefs stateRelProj abiBuiltinAllocation venomState

Definition snapshot_admin_def:
  snapshot_admin i <=> ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]
End

Definition snapshot_admin_compile_def:
  snapshot_admin_compile m <=> !s.
    ci_mono s (SND (m s)) /\ EVERY snapshot_admin (added_insts s (SND (m s)))
End

Theorem snapshot_admin_bind[local]:
  snapshot_admin_compile m /\ (!v. snapshot_admin_compile (k v)) ==>
  snapshot_admin_compile (comp_bind m k)
Proof
  simp[snapshot_admin_compile_def] >> strip_tac >>
  irule added_insts_bind_every >> simp[]
QED

Theorem snapshot_admin_ignore[local]:
  snapshot_admin_compile m /\ snapshot_admin_compile k ==>
  snapshot_admin_compile (comp_ignore_bind m k)
Proof
  simp[snapshot_admin_compile_def] >> strip_tac >>
  irule added_insts_ignore_every >> simp[]
QED

Theorem snapshot_admin_primitives[local,simp]:
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_op opc ops)) /\
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_inst opc ops outs)) /\
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_void opc ops)) /\
  snapshot_admin_compile (compile_alloc_buffer n) /\
  snapshot_admin_compile (new_block l) /\
  snapshot_admin_compile (fresh_label tag) /\
  snapshot_admin_compile fresh_var /\
  snapshot_admin_compile (comp_return v)
Proof
  pure_rewrite_tac[snapshot_admin_compile_def] >> rpt conj_tac
  >- (strip_tac >> gen_tac >> Cases_on `emit_op opc ops s` >>
      drule added_insts_emit_op >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (strip_tac >> gen_tac >> Cases_on `emit_inst opc ops outs s` >>
      drule added_insts_emit_inst >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (strip_tac >> gen_tac >> Cases_on `emit_void opc ops s` >>
      drule added_insts_emit_void >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (gen_tac >> Cases_on `compile_alloc_buffer n s` >>
      drule added_insts_allocate >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (gen_tac >> Cases_on `new_block l s` >> drule added_insts_new_block >> simp[])
  >- (gen_tac >> Cases_on `fresh_label tag s` >> drule added_insts_fresh_label >> simp[])
  >- simp[ci_mono_fresh_var, fresh_var_def, added_insts_def,
          state_insts_def, all_blocks_def, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  simp[added_insts_return_every]
QED

fun snapshot_steps defs =
  rpt (FIRST [CHANGED_TAC (simp defs), gen_tac,
              irule snapshot_admin_bind, irule snapshot_admin_ignore,
              conj_tac, IF_CASES_TAC]);

Theorem snapshot_admin_location_ops[local,simp]:
  snapshot_admin_compile (compile_imm_load_word ctor imm op) /\
  snapshot_admin_compile (compile_imm_store_word imm op v) /\
  snapshot_admin_compile (compile_lit_byte_offset op n)
Proof
  Cases_on `imm` >> Cases_on `ctor` >> Cases_on `op` >>
  snapshot_steps [compile_imm_load_word_def, compile_imm_store_word_def,
                  compile_lit_byte_offset_def]
QED

Theorem snapshot_admin_ptr_ops[local,simp]:
  snapshot_admin_compile (compile_ptr_load ctor imm loc op) /\
  snapshot_admin_compile (compile_ptr_store ctor imm loc op v)
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  snapshot_steps [compile_ptr_load_def, compile_ptr_store_def]
QED

Theorem snapshot_admin_word_loop[local,simp]:
  snapshot_admin_compile
    (compile_word_copy_loop_base src dst count_op ll sl ctor imm)
Proof
  snapshot_steps [compile_word_copy_loop_base_def, LET_DEF]
QED

Theorem snapshot_admin_imm_copy[local,simp]:
  !n off. snapshot_admin_compile (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> snapshot_steps [compile_imm_copy_to_memory_def]
QED

Theorem snapshot_admin_ensure[local,simp]:
  snapshot_admin_compile (compile_ensure_in_memory op loc bytes n ctor imm)
Proof
  Cases_on `loc` >> snapshot_steps
    [compile_ensure_in_memory_def, LET_DEF, compile_storage_to_memory_def,
     compile_transient_to_memory_def, compile_word_copy_loop_def,
     compile_word_copy_loop_op_def]
QED

Theorem snapshot_admin_unwrap[local,simp]:
  snapshot_admin_compile (unwrap_value ce vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >>
  Cases_on `p.ptr_location` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem snapshot_admin_copy_memory[local,simp]:
  snapshot_admin_compile (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def]
QED

Theorem snapshot_admin_array[local]:
  vv_type vv = ArrayT et bd ==>
  snapshot_admin_compile (compile_snapshot_vv ce T vv)
Proof
  strip_tac >>
  snapshot_steps [compile_snapshot_vv_def, compile_materialize_vv_def,
                  is_word_type_def, is_bytestring_type_def, LET_DEF,
                  compile_store_memory_def, compile_copy_memory_def]
QED

Theorem snapshot_added_insts_cover[local]:
  cs_extends a b /\ MEM i (frag_code a b) ==> MEM i (added_insts a b)
Proof
  strip_tac >> qpat_x_assum `cs_extends a b` mp_tac >>
  simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  Cases_on `new = []`
  >- gvs[frag_code_def, emitted_insts_def, added_insts_def,
         state_insts_def, all_blocks_def, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  `?l. (LAST new).bb_instructions = a.cs_current_insts ++ l` by fs[] >>
  qpat_x_assum `MEM i (frag_code a b)` mp_tac >>
  simp[added_insts_def, state_insts_def, all_blocks_def, REVERSE_APPEND,
       FLAT_APPEND, MAP_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG, NULL_EQ,
       frag_code_def, MEM_FLAT, MEM_MAP, MEM_REVERSE,
       DECIDE ``a - (b + a) = 0n``, DECIDE ``a - (b + (c + a)) = 0n``] >>
  simp[MEM_FLAT, MEM_MAP, MEM_REVERSE]
QED

Theorem subscript_snapshot_opcode_inventory:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd ==>
  create_cut_code {} sm sc /\ EVERY snapshot_admin (frag_code sm sc)
Proof
  strip_tac >> conj_tac
  >- (qpat_assum `compile_snapshot_vv _ _ _ _ = _`
        (fn th => mp_tac (Q.INST [`ce` |-> `ce`, `copy` |-> `T`,
                                 `a` |-> `sm`, `vv` |-> `bvv`]
           create_vv_snapshot_cut_code) >> simp[th])) >>
  drule snapshot_admin_array >> simp[snapshot_admin_compile_def] >>
  disch_then (qspecl_then [`ce`, `sm`] mp_tac) >> simp[] >>
  simp[EVERY_MEM, ci_mono_def] >> metis_tac[snapshot_added_insts_cover]
QED

Theorem subscript_snapshot_visit_inventory:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd /\
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code sm sc func ==>
  create_operand_cut sm sc explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all subscript_snapshot_opcode_inventory >> strip_tac >>
  irule create_effect_suffix_cut >> fs[snapshot_admin_def, EVERY_MEM] >> metis_tac[]
QED

(* The materialization producers expose the same traversal and ghosts used by
   the ordinary continuation.  Certify confinement before packaging them. *)
Theorem subscript_snapshot_confined_landing:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\ create_layout sm sc /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~array_slot_base ce obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  gas_shadow_state sm shadow_sm /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
  ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
  (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok ce obj p.ptr_operand G1 s) /\
  (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
               eval_operand (vv_operand bvv) s = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!m. mem_agree_outside tn1.t_mem s.vs_memory m ==>
                    val_in_memory rt v (w2n w) m)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?shadow_sc u Gc tnc q w atv.
    compile_snapshot_vv ce T bvv shadow_sm = (cvv,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
    val_wf atv saved /\ value_has_type atv saved /\
    lookup_var q u = SOME w /\ not_fresh_at sc q /\
    ptr_covers Gc tnc q u (type_memory_size atv) /\
    (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==>
         val_in_memory atv saved (w2n w) m) /\
    vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gc,tnc) /\
      stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
    local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
    u.vs_labels = s.vs_labels /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    wb_frame ce es mid sa s0 u /\
    (~expr_has_effect obj ==> pure_frame ce func es sa s0 u) /\
    create_expr_prefix sm sc explicit ctx func s [] u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `post_value_type ce obj = expr_type obj` by metis_tac[expr_body_pre_subscript_base_type] >>
  `expr_body_pre ce cx env obj (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_array_subscript_base,expr_body_pre_gas_obs] >>
  `arg_type_fits (lowered_value_type ce obj) (expr_type obj)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type obj) /\ ~is_bytestring_type (expr_type obj)` by
    simp[is_word_type_def,is_bytestring_type_def] >>
  `post_value_type ce obj = lowered_value_type ce obj` by
    metis_tac[materialize_post_lowered_classify] >>
  `vv_type bvv = ArrayT et bd` by (drule_all compile_array_vv_type >> simp[]) >>
  `lowered_value_type ce obj = ArrayT et bd` by metis_tac[] >>
  `~is_word_type (lowered_value_type ce obj) /\ ~is_bytestring_type (lowered_value_type ce obj)` by
    simp[is_word_type_def,is_bytestring_type_def] >>
  suspend "compile"
QED

Resume subscript_snapshot_confined_landing[compile]:
  `ci_mono sa sm /\ ci_mono sm sc` by
    metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,pairTheory.SND] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sc` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  Cases_on `compile_snapshot_vv ce T bvv shadow_sm` >>
  rename1 `compile_snapshot_vv ce T bvv shadow_sm = (cvv',shadow_sc)` >>
  `cvv' = cvv /\ gas_shadow_state sc shadow_sc` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`cenv` |-> `ce`,`copy_flag` |-> `T`,`vv` |-> `bvv`]
         gas_shadow_compiles_snapshot_vv)) >>
     disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >> simp[]) >>
  `ext_call_arg_value (lowered_value_type ce obj) bvv = bvv` by
    (Cases_on `bvv` >> fs[vv_type_def,ext_call_arg_value_def]) >>
  Cases_on `compile_materialize_vv ce (lowered_value_type ce obj) bvv sm` >>
  rename1 `compile_materialize_vv ce _ bvv sm = (dst,sc')` >>
  `cvv = LocatedValue (ArrayT et bd) (mk_ptr dst LocMemory) /\ sc' = sc` by
    (`compile_materialize_vv ce (ArrayT et bd) bvv sm = (dst,sc')` by metis_tac[] >>
     qpat_x_assum `compile_snapshot_vv ce T bvv sm = _` mp_tac >>
     simp[compile_snapshot_vv_def,is_word_type_def,comp_bind_def,comp_return_def]) >>
  qpat_x_assum `sc' = sc` SUBST_ALL_TAC >>
  suspend "source"
QED

Resume subscript_snapshot_confined_landing[source]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post H ctx func ce cx obj (es with gas_obs := gs) sa sm s0 mid raw bvv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s` by simp[vv_post_initial_gas] >>
  `ghost_kept_at lo ce (es with gas_obs := gs) sa G0 tn0 s0 G1 tn1` by
    (simp[ghost_kept_at_def] >> fs[ghost_kept_at_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func ce cx mid s /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w)` by fs[vv_post_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `return_buf_frame d ce sm s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`sa`] >> simp[]) >>
  `vyperState$bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs) = (INL saved,mid)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all (REWRITE_RULE [ETA_THM] abi_args_success_ready) >> simp[] >> strip_tac >>
  `(!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0)` by
    metis_tac[body_inv_no_phi] >>
  `compile_materialize_vv ce (lowered_value_type ce obj)
      (ext_call_arg_value (lowered_value_type ce obj) bvv) sm = (dst,sc)` by metis_tac[] >>
  `type_memory_bytes ce (lowered_value_type ce obj) + 64 < dimword (:256)` by
    metis_tac[] >>
  `MAP FDOM (es with gas_obs := gs).scopes = MAP FDOM mid.scopes` by simp[] >>
  drule_all ctor_materialize_source_arrival_framed >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`buf`,`sk`,`su`,`src`,`p`,`dw`,`atv`,`sw`,`z`,`Gz`,`tz`,`inst`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume subscript_snapshot_confined_landing[store]:
  `ci_mono sm sk /\ ci_mono sk su /\ ci_mono su sc` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `sm.cs_next_id <= su.cs_next_id /\ su.cs_next_id <= sc.cs_next_id /\
   sm.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sc.cs_next_var` by
    fs[ci_mono_def] >>
  qabbrev_tac `HP = \H. valid_horizon cx st0 H mid.storage_trace` >>
  `HP H0` by simp[Abbr `HP`] >>
  `!H. HP H ==> stmt_state_rel H ctx func ce cx mid z /\
       ghost_inv_at (DF H) lo d ce cx mid Gz tz z` by metis_tac[Abbr `HP`] >>
  `type_memory_size atv = (if is_bytestring_type (lowered_value_type ce obj)
      then val_store_size atv saved else type_memory_size atv)` by simp[is_bytestring_type_def] >>
  `!name b len. local_region ce mid.scopes z name b len ==>
      w2n dw + type_memory_size atv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     qpat_assum `!n b l. local_region ce mid.scopes z n b l ==> _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name b len. local_region ce (es with gas_obs := gs).scopes s0 name b len ==>
      w2n dw + type_memory_size atv <= b \/ b + len <= w2n dw` by
    (qpat_assum `!n b l. local_region ce _ s0 n b l ==> regions_disjoint _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  drule_all ctor_materialize_store_arrival_framed >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "package"
QED

Resume subscript_snapshot_confined_landing[package]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gu,tu) /\
    stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid Gu tu u` by
    (qx_gen_tac `H` >> strip_tac >>
     `HP H` by simp[Abbr `HP`] >>
     qpat_assum `!H. HP H ==> stmt_state_rel H _ _ _ _ mid u /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> conj_tac
     >- (qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] (OK z,Gz,tz) /\ _`
           (qspec_then `H` (drule_then strip_assume_tac)) >>
         qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] _`
           (qspec_then `DF H` assume_tac) >>
         qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (s,G1,tn1) [] _`
           (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >> simp[]) >>
     qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[vv_post_def]) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] (OK u,Gu,tu) /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  suspend "confinement"
QED

Resume subscript_snapshot_confined_landing[confinement]:
  qabbrev_tac `C = \a b. ?i. ctor_segment_fetch func a = SOME i /\
    sm.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
    i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b` >>
  `RTC C s z` by
    (qpat_assum `RTC _ s z` mp_tac >> ho_match_mp_tac RTC_MONOTONE >>
     simp[Abbr `C`] >> rpt strip_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `RTC C z u` by
    (qpat_assum `RTC _ z u` mp_tac >> ho_match_mp_tac RTC_MONOTONE >>
     simp[Abbr `C`] >> rpt strip_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `create_expr_prefix sm sc explicit ctx func s [] u` by
    (irule snapshot_computed_empty_prefix >>
     simp[entryCreateFocusSpecTheory.create_operand_at_def] >>
     conj_tac
     >- (qexists_tac `C` >> conj_tac
         >- (simp[Abbr `C`] >> rpt strip_tac >>
             drule_all subscript_snapshot_band_fetch >> strip_tac >>
             fs[entryCreateFocusSpecTheory.create_operand_at_def] >> metis_tac[])
         >> metis_tac[RTC_TRANS]) >>
     qexists_tac `T` >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections]) >>
  suspend "frames"
QED

Resume subscript_snapshot_confined_landing[frames]:
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history func u` by metis_tac[body_full_path_alloca_history] >>
  `u.vs_labels = s.vs_labels` by metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G1 x /\ op_taint tu (Var x) = op_taint tn1 (Var x)` by
    (rpt strip_tac >> `not_fresh_at su x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `sm.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `return_buf_frame d ce sc u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sm s` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu` by
    (qpat_assum `ghost_kept_at lo ce (es with gas_obs := gs) sa G0 tn0 s0 Gu tu`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> simp[ghost_kept_at_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame ce es mid sa s0 u` by
    (qpat_assum `wb_frame ce (es with gas_obs := gs) mid sa s0 u`
       (mp_tac o REWRITE_RULE [wb_frame_def,locals_kept_def,popped_kept_def]) >>
     simp[wb_frame_def,locals_kept_def,popped_kept_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "ownership"
QED

Resume subscript_snapshot_confined_landing[ownership]:
  `sm.cs_next_id < sk.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ sm = (buf,sk)`
       (mp_then Any mp_tac abi_builtin_alloc_buffer_shape) >>
     simp[loweringShapeRulesTheory.emit_op_eq] >> strip_tac >> gvs[]) >>
  `sm.cs_next_id < sc.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv` by metis_tac[] >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size atv)` by metis_tac[] >>
  `not_fresh_at sc p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP u.vs_allocas aid = SOME entry` by metis_tac[] >>
  `vv_own ce cx (ArrayT et bd) sm sc mid (Value saved)
       (LocatedValue (ArrayT et bd) (mk_ptr (Var p) LocMemory)) u` by
    (simp[vv_own_def,mk_ptr_def,vyperStateTheory.read_result_def,
          vyperStateTheory.return_def,eval_operand_def] >>
     disj1_tac >> qexistsl_tac [`sm.cs_next_id`,`w2n dw`,`type_memory_size atv`] >>
     simp[val_footprint_le] >> rpt strip_tac >>
     qpat_assum `!n b l. local_region ce mid.scopes u n b l ==> _`
       (drule_then mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`u`,`Gu`,`tu`,`p`,`dw`,`atv`] >> simp[] >>
  qpat_x_assum `~expr_has_effect obj ==> pure_frame ce func _ sa s0 u`
    (mp_tac o REWRITE_RULE [pure_frame_gas_obs]) >> simp[]
QED

Finalise subscript_snapshot_confined_landing
