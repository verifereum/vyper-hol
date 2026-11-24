Theory createCtorEncoderStaticRowMods
Ancestors
  createExprSizeExitDefsMods bodyFullExtCallDirectUnwrap bodyFullExtCallDirectPhase
  abiEncodeValuesPhases abiEncodeValuesMetadata abiEncodeValuesPrefixFrame
  abiEncodeValuesStaticPrefix abiEncodeValuesStatic abiEncodeValuesSource
  abiDecodeRanges allocaSiteResource exprLoweringProps exprSimAbiEncodeExecFrame
  bodyFullShadowBodyInv exprSimAbiEncodePlanMetadata abiCallerTupleLayout abiEncoderOpenInput
  stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragGasOriginPtrLoop fragExec
  compileEnv exprLowering context contractABI valueEncodingDefs vyperValue vyperTyping
  vyperABI venomState venomInst venomMemDefs finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs horizonTypeLib

Theorem ctor_encoder_static_resources[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  valid_horizon cx st0 H ee.storage_trace ==>
  stmt_state_rel H ctx func ce cx ee u /\
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)
Proof
  simp_tac bool_ss [abi_encode_saved_state_mods_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  drule_then (assume_tac o cj 2) stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  asm_rewrite_tac[] >> strip_tac >> fs[fmp_room_def] >> decide_tac
QED

(* The source-row data is fixed by the caller of restore. The callback
   quantifies just over the changing cut and its unwrap result. *)
Theorem ctor_encoder_static_row_mods:
  ~is_word_type ty /\ ~is_dynamic at /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size rt /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  (!a c ids outs v Gv tv z Gz tz.
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a v Gv tv /\
    ci_mono a c /\ window_phase ctx func a c ids outs v z /\ abi_encode_exec_frame func v z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP Gz x = FLOOKUP Gv x /\ op_taint tz (Var x) = op_taint tv (Var x)) /\
    tz.t_stor = tv.t_stor /\ tz.t_trans = tv.t_trans /\ tz.t_imm = tv.t_imm /\
    shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
    EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
    (!aid. aid IN shared INSERT ids ==>
      ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
    (!j. EVERY (\(p,n). j < p \/ p+n <= j) outs /\
      (!aid p n. aid IN ids /\ FLOOKUP z.vs_allocas aid = SOME (p,n) ==>
        j < p \/ p+n <= j) /\ j IN tz.t_mem ==> j IN tv.t_mem) ==>
    (pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz) /\
  (!a b src u1 G1 t1.
    unwrap_value ce saved a = (src,b) /\ fn_has_code a b func /\ ci_mono a b /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a u1 G1 t1 /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u1 G1 t1 ==>
    ?u2 G2 t2.
      (pure_frame ce func ee a u1 u2 /\ wb_frame ce ee ee a u1 u2) /\
      abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix b u2 G2 t2 /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i b u2 G2 t2 /\
      expr_val_rel cx ty v src u2 /\ ptr_val_ok cx ty v src G2 t2 u2 /\
      expr_store_bound cx ty v src u2 /\ (!x. src = Var x ==> not_fresh_at b x) /\
      (!x. not_fresh_at a x ==>
        lookup_var x u2 = lookup_var x u1 /\ FLOOKUP G2 x = FLOOKUP G1 x /\
        op_taint t2 (Var x) = op_taint t1 (Var x)) /\
      (?first last. expr_val_at ce cx ty first last ee v src u2 /\
        (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u1,G1,t1) [] (OK u2,G2,t2)) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
  drule_all_then strip_assume_tac ctor_encoder_static_resources >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by metis_tac[abi_encode_translated_dynamic] >>
  drule_all abi_encode_values_static_cuts >>
  disch_then (qx_choosel_then [`head_op`,`su1`,`src`,`su2`] strip_assume_tac) >>
  qabbrev_tac `hs = abi_member_head_size at` >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su u Gu tu`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  `hl <= off /\ h+hs <= capacity-dst_offset` by decide_tac >>
  `pbase+capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ _` mp_tac >> simp[]) >>
  mp_tac (Q.INST [`b` |-> `pbase+dst_offset`,`off` |-> `h`,`n` |-> `hs`,
    `cap` |-> `capacity-dst_offset`,`st` |-> `su`,`en` |-> `su1`,`head` |-> `head_op`,
    `s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`] abi_encode_values_head_address) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`hp`,`u1`,`G1`,`t1`] strip_assume_tac) >>
  `!aid. aid IN {shared} ==> ?site x. MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
    site.inst_id = aid /\ site.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp[] >> qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
  qpat_assum `!a c ids outs v Gv tv z Gz tz. _`
    (qspecl_then [`su`,`su1`,`{}`,`[]`,`u`,`Gu`,`tu`,`u1`,`G1`,`t1`] mp_tac) >>
  impl_tac >- simp[EVERY_DEF] >>
  strip_tac >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su1 u1 G1 t1` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func su su1 {} [] u u1` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!a b src u1 G1 t1. _`
    (qspecl_then [`su1`,`su2`,`src`,`u1`,`G1`,`t1`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u2`,`G2`,`t2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `head_op = Var hp` SUBST_ALL_TAC >>
  `eval_operand (Var hp) u2 = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers G2 t2 hp u2 hs` by
    (irule extcall_direct_unwrap_pointer >> qexistsl_tac [`G1`,`u1`,`su1`,`t1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at su2 hp` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `su1` >>
     fs[ci_mono_def]) >>
  drule_all_then strip_assume_tac ctor_encoder_static_resources >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su2 u2 G2 t2`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  `hs = abi_member_head_size at` by simp[NoAsms, Abbr `hs`] >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by
    (qpat_assum `at = vyper_to_abi_type _ _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `type_memory_size rt = static_length at` by
    (qpat_assum `at = vyper_to_abi_type _ _` (fn th => PURE_REWRITE_TAC [th]) >>
     metis_tac[abi_caller_static_memory]) >>
  `hs = static_length at` by
    (qpat_assum `hs = abi_member_head_size at` SUBST1_TAC >>
     simp_tac bool_ss [abi_member_head_size_def] >>
     qpat_assum `~is_dynamic at` (fn th => simp_tac bool_ss [th])) >>
  `LENGTH (enc at av) = hs` by
    (qpat_assum `hs = static_length at` SUBST1_TAC >>
     qpat_assum `abi_encoder_layout_valid at av` (mp_tac o REWRITE_RULE [abi_encoder_layout_valid_def]) >>
     qpat_assum `~is_dynamic at` (fn th => simp_tac bool_ss [th])) >>
  `val_footprint rt v = hs` by
    (drule_all abi_encode_values_static_footprint >> asm_rewrite_tac[]) >>
  `pbase+capacity <= u2.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `pbase+dst_offset+h+hs <= pbase+capacity /\ pbase+dst_offset+h+hs <= u2.vs_alloca_next` by decide_tac >>
  qpat_x_assum `?first last. expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_assum `inst.inst_id = shared` (fn th =>
    qpat_assum `FLOOKUP u2.vs_allocas shared = SOME (pbase,capacity)`
      (assume_tac o REWRITE_RULE [GSYM th]) >>
    qpat_assum `shared < first.cs_next_id \/ last.cs_next_id <= shared`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  mp_tac (Q.INST [`H` |-> `hz`,`s` |-> `u2`,`G` |-> `G2`,`tn` |-> `t2`,
    `sa` |-> `first`,`sb` |-> `last`,`x` |-> `root`,`b` |-> `pbase`,`tv` |-> `rt`,
    `n` |-> `capacity`,`d` |-> `pbase+dst_offset+h`,`len` |-> `hs`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_memory_source)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choose_then `w` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `eval_operand src u2 = SOME (n2w (w2n w))` by simp[] >>
  qpat_assum `ptr_covers G2 t2 hp u2 hs`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  `!x. src = Var x \/ Var hp = Var x ==> not_fresh_at su2 x` by
    (gen_tac >> disch_then DISJ_CASES_TAC
     >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `Var hp = Var x` (SUBST1_TAC o SYM o REWRITE_RULE [operand_11]) >>
     first_assum ACCEPT_TAC) >>
  `0 < hs ==> w2n w + hs <= u2.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n w,hs) (pbase+dst_offset+h,hs) /\
    (?p. src = Var p /\ ptr_covers G2 t2 p u2 hs) /\
    (?p. Var hp = Var p /\ ptr_covers G2 t2 p u2 hs)` by
    (qpat_assum `val_footprint rt v = hs` (fn th =>
       qpat_assum `0 < val_footprint rt v ==> _` (assume_tac o PURE_REWRITE_RULE [th])) >>
     disch_tac >> qpat_assum `0 < hs ==> _` (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac `hp` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`env` |-> `get_tenv cx`,`s` |-> `u2`,`G` |-> `G2`,`tn` |-> `t2`,
    `st` |-> `su2`,`en` |-> `en`,`dst` |-> `Var hp`,`tv` |-> `rt`,
    `d` |-> `pbase+dst_offset+h`,`sb` |-> `w2n (w:bytes32)`,`bs` |-> `enc at av`]
    abi_encode_values_static_store) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `at = vyper_to_abi_type _ _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
    qpat_assum `LENGTH (enc at av) = hs` (fn th => PURE_REWRITE_TAC [th]) >>
    asm_rewrite_tac[]) >>
  qpat_assum `LENGTH (enc at av) = hs` (fn th =>
    disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (strip_assume_tac o PURE_REWRITE_RULE [th]))) >>
  `!j. (j < pbase+dst_offset+h \/ pbase+dst_offset+h+hs <= j) ==>
      j IN tz.t_mem ==> j IN t2.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!j. _ ==> (j IN tz.t_mem <=> j IN t2.t_mem)` (drule_then (fn th => simp[th]))) >>
  `!j. (j < pbase+dst_offset+h \/ pbase+dst_offset+h+hs <= j) /\
      j IN tz.t_mem ==> j IN t2.t_mem` by
    (gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_assum `!j. _ ==> j IN tz.t_mem ==> j IN t2.t_mem` (drule_then irule) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!a c ids outs v Gv tv z Gz tz. _`
    (qspecl_then [`su2`,`en`,`{}`,`[(pbase+dst_offset+h,hs)]`,`u2`,`G2`,`t2`,`z`,`Gz`,`tz`] mp_tac) >>
  impl_tac >- (simp_tac (srw_ss()) [EVERY_DEF, NoAsms] >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[] >> NO_TAC) >> decide_tac) >>
  strip_tac >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz` by
    (irule abi_encode_values_static_prefix >>
     qpat_assum `window_phase ctx func su2 en {} _ u2 z` (irule_at Any) >>
     qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ i su2 u2 G2 t2` (irule_at Any) >>
     qpat_assum `FLOOKUP u2.vs_allocas shared = SOME (pbase,capacity)` (irule_at Any) >>
     qexistsl_tac [`off`,`av`,`at`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `se.cs_next_var <= su1.cs_next_var /\ se.cs_next_id <= su1.cs_next_id` by
    (qpat_assum `ci_mono su su1` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  `pure_frame ce func ee se u u2 /\ wb_frame ce ee ee se u u2` by
    (irule abi_encode_saved_frames_trans >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`su1`,`u1`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`hz`,`ctx`,`cx`] >> first_assum ACCEPT_TAC) >>
  `pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z` by
    (irule abi_encode_saved_frames_trans >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`se`,`u2`] >> asm_rewrite_tac[LESS_EQ_REFL]) >>
     qexistsl_tac [`hz`,`ctx`,`cx`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G1`,`u1`,`t1`] >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G2`,`u2`,`t2`] >> asm_rewrite_tac[]
QED
