(* The reached static aggregate row: compute the head address, restore the
   saved operand at its unwrap interval, and copy into the head extent. *)
Theory bodyAbiTupleStaticRowMods
Ancestors
  bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferPhaseMods bodyAbiEncodePackedPostMods
  abiEncodeValuesMetadata abiEncodeValuesPhases abiEncodeValuesPrefixFrame
  abiEncodeValuesStatic abiEncodeValuesStaticPrefix abiEncodeValuesSource
  bodyAbiTupleBufferStateMods abiEncoderOpenInput
  abiCallerTupleLayout abiDecodeRanges allocaSiteResource fragGasOriginPtr fragGasOriginPtrLoop
  exprOperandVar
  bodyPtrDefs exprLoweringProps compileEnv venomInst venomState venomMemDefs
  vyperContext vyperValue vyperTyping vyperABI contractABI valueEncodingDefs
  finite_map list pred_set words
Libs horizonTypeLib

Theorem static_head_address[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  h + hs <= capacity - dst_offset /\
  emit_op ADD [Var dst; Lit (n2w h)] a = (head,b) /\
  fn_has_code a b func ==>
  ?hp u1 G1 t1. head = Var hp /\ not_fresh_at b hp /\ ptr_covers G1 t1 hp u1 hs /\
    eval_operand head u1 = SOME (n2w (pbase+dst_offset+h)) /\
    window_phase ctx func a b {} [] u u1 /\ abi_encode_exec_frame func u u1 /\
    (!x. not_fresh_at a x ==> FLOOKUP G1 x = FLOOKUP Gu x /\
      op_taint t1 (Var x) = op_taint tu (Var x)) /\
    t1.t_mem = tu.t_mem /\ t1.t_stor = tu.t_stor /\ t1.t_trans = tu.t_trans /\
    t1.t_imm = tu.t_imm /\ u1.vs_memory = u.vs_memory /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK u1,G1,t1)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac abi_tuple_buffer_resources_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
  `pbase+capacity <= u.vs_alloca_next` by
    (drule_all_then ACCEPT_TAC alloca_site_registered_below) >>
  `pbase+dst_offset+(capacity-dst_offset) <= u.vs_alloca_next` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by (strip_tac >> res_tac) >>
  irule abi_encode_values_head_address >>
  asm_rewrite_tac[] >> qexistsl [`capacity-dst_offset`,`dst`] >> asm_rewrite_tac[]
QED

Theorem static_row_store[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix b u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  fn_inst_ids_distinct func /\
  MEM owner (fn_insts func) /\ owner.inst_id = shared /\
  owner.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ hs = abi_member_head_size at /\
  h + hs <= capacity-dst_offset /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var hp) u = SOME (n2w (pbase+dst_offset+h)) /\
  ptr_covers Gu tu hp u hs /\ not_fresh_at b hp /\ (!x. src = Var x ==> not_fresh_at b x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_store_memory ce src (Var hp) ty ty b = ((),c) /\ fn_has_code b c func ==>
  ?z Gz tz. mem_bytes_at (pbase+dst_offset+h) hs z.vs_memory = enc at av /\
    window_phase ctx func b c {} [(pbase+dst_offset+h,hs)] u z /\
    abi_encode_exec_frame func u z /\
    (!j. pbase+dst_offset+h <= j /\ j < pbase+dst_offset+h+hs ==> j NOTIN tz.t_mem) /\
    (!x. not_fresh_at b x ==> FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    (!j. (j < pbase+dst_offset+h \/ pbase+dst_offset+h+hs <= j) ==>
      (j IN tz.t_mem <=> j IN tu.t_mem)) /\
    tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac abi_tuple_buffer_resources_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `?first last. expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by metis_tac[] >>
  `type_memory_size tv = static_length at` by metis_tac[abi_caller_static_memory] >>
  `LENGTH (enc at av) = hs` by fs[abi_encoder_layout_valid_def, abi_member_head_size_def] >>
  `val_footprint tv v = hs` by
    (drule_all abi_encode_values_static_footprint >> fs[abi_member_head_size_def]) >>
  `pbase + capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `pbase+dst_offset+h+hs <= pbase+capacity /\
   pbase+dst_offset+h+hs <= u.vs_alloca_next` by decide_tac >>
  qpat_assum `owner.inst_id = shared` (fn th =>
    qpat_assum `FLOOKUP u.vs_allocas shared = SOME (pbase,capacity)`
      (assume_tac o PURE_REWRITE_RULE [GSYM th]) >>
    qpat_assum `shared < first.cs_next_id \/ last.cs_next_id <= shared`
      (assume_tac o PURE_REWRITE_RULE [GSYM th])) >>
  `?w. eval_operand src u = SOME w /\ op_taint tu src = {} /\
       (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory tv v (w2n w) mem) /\
       (0 < val_footprint tv v ==>
        w2n w + val_footprint tv v <= u.vs_alloca_next /\
        venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (pbase+dst_offset+h,hs) /\
        ?p. src = Var p /\ ptr_covers Gu tu p u (val_footprint tv v))` by
    (irule (horizonTypeLib.at_horizon_named "H" abi_encode_values_memory_source) >>
     qhdtm_assum `expr_val_at` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas owner.inst_id = _` (irule_at Any) >>
     qexistsl [`root`,`func`,`ctx`,`hz`] >> asm_rewrite_tac[] >> decide_tac) >>
  qpat_assum `val_footprint tv v = hs`
    (fn th => qpat_assum `0 < val_footprint tv v ==> _`
      (assume_tac o PURE_REWRITE_RULE[th])) >>
  `eval_operand src u = SOME (n2w (w2n w))` by simp[] >>
  `op_taint tu (Var hp) = {}` by fs[ptr_covers_def] >>
  `!x. src = Var x \/ Var hp = Var x ==> not_fresh_at b x` by
    (gen_tac >> disch_then DISJ_CASES_TAC >> fs[]) >>
  `0 < hs ==> w2n w + hs <= u.vs_alloca_next /\
     venomMemDefs$regions_disjoint (w2n w,hs) (pbase+dst_offset+h,hs) /\
     (?p. src = Var p /\ ptr_covers Gu tu p u hs) /\
     (?p. Var hp = Var p /\ ptr_covers Gu tu p u hs)` by
    (strip_tac >> qpat_assum `0 < hs ==> _` (drule_then strip_assume_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     (qexists `p` >> asm_rewrite_tac[] >> NO_TAC ORELSE
      qexists `hp` >> asm_rewrite_tac[])) >>
  qpat_assum `LENGTH (enc at av) = hs`
    (fn th => irule (PURE_REWRITE_RULE [th]
      (Q.INST [`bs` |-> `enc at av`, `env` |-> `get_tenv cx`] abi_encode_values_static_store))) >>
  qpat_x_assum `hs = abi_member_head_size at` kall_tac >>
  qpat_x_assum `at = vyper_to_abi_type _ _` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >>
  qpat_assum `compile_store_memory _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`v`,`tv`,`w2n w`,`cx`] >> asm_rewrite_tac[]
QED

Theorem abi_tuple_static_row_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\ MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  ty = lowered_value_type ce e /\ ~is_word_type ty /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s) /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c) /\
  fn_has_code a c func /\
  (!b r src hp u1 G1 t1.
    unwrap_value ce saved b = (src,r) /\ fn_has_code b r func /\ ci_mono b r /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix b u1 G1 t1 /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i b u1 G1 t1 /\
    not_fresh_at b hp /\ eval_operand (Var hp) u1 = SOME (n2w (pbase+dst_offset+h)) /\
    ptr_covers G1 t1 hp u1 (abi_member_head_size at) ==>
    ?u2 G2 t2.
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix r u2 G2 t2 /\
      abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc
        b u1 G1 t1 r u2 G2 t2 /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i r u2 G2 t2 /\
      eval_operand (Var hp) u2 = SOME (n2w (pbase+dst_offset+h)) /\
      ptr_covers G2 t2 hp u2 (abi_member_head_size at) /\
      (!x. src = Var x ==> not_fresh_at r x) /\
      expr_val_rel cx ty v src u2 /\ ptr_val_ok cx ty v src G2 t2 u2 /\
      expr_store_bound cx ty v src u2 /\
      (?first last. expr_val_at ce cx ty first last ee v src u2 /\
        (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u1,G1,t1) [] (OK u2,G2,t2)) ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc
      a u Gu tu c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `hs = abi_member_head_size at` >>
  `hs = abi_member_head_size at` by simp[NoAsms, Abbr `hs`] >>
  `hl <= off /\ h+hs <= capacity-dst_offset` by decide_tac >>
  drule_all abi_encode_values_static_cuts >>
  disch_then (qx_choosel_then [`head`,`b`,`src`,`r`] strip_assume_tac) >>
  drule_all static_head_address >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`hp`,`u1`,`G1`,`t1`] strip_assume_tac)) >>
  qpat_x_assum `head = Var hp` SUBST_ALL_TAC >>
  (* Start with the exact arith-only phase, before opening the saved value. *)
  `abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
     shared pbase capacity root dst dst_offset prefix b u1 G1 t1 /\
   abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc a u Gu tu b u1 G1 t1` by
    (irule abi_tuple_buffer_phase_mods >>
     qpat_assum `window_phase ctx func a b {} [] u u1` (irule_at Any) >>
     qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
     asm_rewrite_tac[] >> qexistsl [`explicit`,`PG`,`hz`] >> simp[] >>
     qexistsl [`owner`,`root`] >> asm_rewrite_tac[]) >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i b u1 G1 t1` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func a b {} [] u u1` (irule_at Any) >>
     qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ a _ _ _` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `!b r src hp u1 G1 t1. unwrap_value _ _ b = _ /\ _ ==> _` drule_all >>
  disch_then (qx_choosel_then [`u2`,`G2`,`t2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `not_fresh_at r hp` by (irule compiler_ci_mono_not_fresh >> metis_tac[]) >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r u2 _ _`
    (mp_then (Pos hd) drule_all static_row_store) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac)) >>
  suspend "close_store"
QED

Resume abi_tuple_static_row_mods[close_store]:
  `pbase+dst_offset+h+hs <= pbase+capacity` by
    (qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r u2 _ _`
      (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >> decide_tac) >>
  `!j. (j < pbase+dst_offset+h \/ pbase+dst_offset+h+hs <= j) ==>
     j IN tz.t_mem ==> j IN t2.t_mem` by
    (gen_tac >> disch_tac >>
     qpat_assum `!j. _ ==> (j IN tz.t_mem <=> j IN t2.t_mem)` (drule_then SUBST1_TAC) >> simp[]) >>
  `abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
     shared pbase capacity root dst dst_offset prefix c z Gz tz /\
   abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc r u2 G2 t2 c z Gz tz` by
    (irule abi_tuple_buffer_phase_mods >>
     qpat_assum `window_phase ctx func r c {} _ u2 z` (irule_at Any) >>
     qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl [`explicit`,`PG`,`hz`] >>
     simp_tac (srw_ss()) [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rewrite_tac[GSYM AND_IMP_INTRO] >> first_assum ACCEPT_TAC) >>
     qexistsl [`owner`,`root`] >> asm_rewrite_tac[]) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule abi_tuple_row_effects_trans_mods >>
      qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ r u2 _ _ c z _ _` (irule_at Any) >>
      irule abi_tuple_row_effects_trans_mods >>
      qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ b u1 _ _ r u2 _ _` (irule_at Any) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r u2 _ _`
        (mp_then (Pos hd) (drule_then strip_assume_tac) abi_tuple_buffer_resources_mods) >>
      qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r u2 _ _`
        (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
      `pbase+dst_offset+off <= pbase+capacity` by decide_tac >>
      irule abi_encode_values_static_prefix >>
      qpat_assum `window_phase ctx func r c {} _ u2 z` (irule_at Any) >>
      qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ r u2 _ _` (irule_at Any) >>
      qpat_assum `FLOOKUP u2.vs_allocas shared = _` (irule_at Any) >>
      qpat_assum `abi_encoder_layout_valid at av` (irule_at Any) >>
      `pbase <= pbase + dst_offset` by decide_tac >>
      qpat_x_assum `at = vyper_to_abi_type _ _` (assume_tac o SYM) >>
      qexists `off` >> asm_rewrite_tac[]) >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl [`G1`,`u1`,`t1`] >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> qexistsl [`G2`,`u2`,`t2`] >> asm_rewrite_tac[]
QED

Finalise abi_tuple_static_row_mods
