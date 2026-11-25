Theory createCtorEncoderDynamicRowMods
Ancestors
  createExprSizeExitDefsMods bodyFullExtCallDirectUnwrap bodyFullExtCallDirectPhase
  reasonCopySourcePtr exprSimHyps
  abiEncodeValuesPhases abiEncodeValuesMetadata abiEncodeValuesPrefixFrame abiEncodeValuesRun
  abiEncodeValuesDynamicPrefix abiEncodeValuesDynamic abiEncodeValuesSource
  abiEncoderWindowJointPhases abiEncoderWindowContract abiEncoderProps
  abiDecodeRanges allocaSiteResource exprLoweringProps exprSimAbiEncodeExecFrame
  bodyFullShadowBodyInv exprSimAbiEncodePlanMetadata abiCallerTupleLayout abiEncoderOpenInput
  stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragGasOriginPtrLoop fragExec
  compileEnv exprLowering context contractABI valueEncodingDefs vyperValue vyperTyping
  vyperABI venomState venomInst venomMemDefs finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs horizonTypeLib

Theorem ctor_encoder_dynamic_resources[local]:
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

Theorem ctor_encoder_dynamic_row_mods:
  ~is_word_type ty /\ is_dynamic at /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size rt /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off + LENGTH (enc at av) <= capacity-dst_offset /\
  (!t tv. evaluate_type (get_tenv cx) t = SOME tv ==> type_memory_bytes ce t = type_memory_size tv) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ shared <> loc /\
  se.cs_next_id <= loc /\
  (?ci r. MEM ci (fn_insts func) /\ ci.inst_opcode = ALLOCA /\ ci.inst_id = loc /\
    ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r) /\
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
        last.cs_next_id <= b.cs_next_id /\
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
  drule_all_then strip_assume_tac ctor_encoder_dynamic_resources >>
  `is_abi_dynamic ce.ce_struct_fields ty` by metis_tac[abi_encode_translated_dynamic] >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su u Gu tu`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  drule_all abi_encode_values_dynamic_cuts >>
  disch_then (qx_choosel_then [`head_op`,`off0`,`tail_op`,`su1`,`src`,`su2`,`len`,`mid`]
    strip_assume_tac) >>
  `abi_member_head_size at = 32` by simp[abi_member_head_size_def] >>
  `h + 32 <= hl` by
    (qpat_assum `h + abi_member_head_size at <= hl` (fn hle =>
       qpat_assum `abi_member_head_size at = 32` (fn hsz =>
         ACCEPT_TAC (REWRITE_RULE [hsz] hle))) ) >>
  `h + 32 <= off` by
    (qpat_assum `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))`
      (SUBST1_TAC o SYM) >> irule LESS_EQ_TRANS >> qexists_tac `hl` >>
     conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  `h + 32 <= capacity-dst_offset` by
    (qpat_assum `off + LENGTH (enc at av) <= capacity-dst_offset` (fn offle =>
       irule LESS_EQ_TRANS >> qexists_tac `off` >>
       conj_tac >- first_assum ACCEPT_TAC >> decide_tac)) >>
  `pbase + capacity <= u.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac
     >- qpat_assum `alloca_inv u` ACCEPT_TAC
     >- (qexists_tac `shared` >>
         qpat_assum `FLOOKUP u.vs_allocas shared = SOME (pbase,capacity)` ACCEPT_TAC)) >>
  `pbase+dst_offset+(capacity-dst_offset) <= pbase+capacity` by decide_tac >>
  `pbase+dst_offset+(capacity-dst_offset) <= u.vs_alloca_next` by
    (irule LESS_EQ_TRANS >> qexists_tac `pbase+capacity` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs)))`
    (SUBST1_TAC o SYM) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
       u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp`
       (drule_then (assume_tac o cj 1)) >>
     first_assum ACCEPT_TAC) >>
  `off <= capacity-dst_offset` by decide_tac >>
  mp_tac (Q.INST [`d` |-> `pbase+dst_offset`,`ho` |-> `h`,`dp` |-> `p`,
    `bound` |-> `capacity-dst_offset`,`st` |-> `su`,`en` |-> `su1`,
    `ops` |-> `(head_op,off0,tail_op)`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`]
    window_child_prefix_joint) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u1`,`G1`,`t1`,`hp`,`tp`]
    (strip_assume_tac o SIMP_RULE bool_ss [FST,SND])) >>
  qpat_x_assum `head_op = Var _` SUBST_ALL_TAC >>
  qpat_x_assum `tail_op = Var _` SUBST_ALL_TAC >>
  qpat_assum `!a c ids outs v Gv tv z Gz tz. _`
    (qspecl_then [`su`,`su1`,`{}`,`[]`,`u`,`Gu`,`tu`,`u1`,`G1`,`t1`] mp_tac) >>
  impl_tac >- (simp[EVERY_DEF] >>
    qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
  strip_tac >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var p) loc slot i su1 u1 G1 t1` by
    (irule abiEncodeValuesPrefixFrameTheory.abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func su su1 {} [] u u1` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  `!aid. aid IN {shared} ==> ?site x. MEM site (fn_insts func) /\
      site.inst_opcode = ALLOCA /\ site.inst_id = aid /\
      site.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp[] >> qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
  qpat_assum `!a b src u1 G1 t1. _`
    (qspecl_then [`su1`,`su2`,`src`,`u1`,`G1`,`t1`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u2`,`G2`,`t2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!x w n. not_fresh_at su1 x /\ eval_operand (Var x) u1 = SOME w /\
      ptr_covers G1 t1 x u1 n ==>
    eval_operand (Var x) u2 = SOME w /\ ptr_covers G2 t2 x u2 n` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule extcall_direct_unwrap_pointer >> qexistsl_tac [`G1`,`u1`,`su1`,`t1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var hp) u2 = SOME (n2w (pbase+dst_offset+h)) /\
    ptr_covers G2 t2 hp u2 32` by
    (qpat_assum `!x w n. _ ==> _` (qspecl_then [`hp`,`n2w (pbase+dst_offset+h)`,`32`] mp_tac) >>
     metis_tac[]) >>
  `LENGTH (enc at av) <= capacity-dst_offset-off` by
    (qpat_assum `off + LENGTH (enc at av) <= capacity-dst_offset`
      (fn _ => decide_tac)) >>
  `eval_operand (Var tp) u2 = SOME (n2w (pbase+dst_offset+off)) /\
    ptr_covers G2 t2 tp u2 (LENGTH (enc at av))` by
    (qpat_assum `!x w n. _ ==> _`
      (qspecl_then [`tp`,`n2w (pbase+dst_offset+off)`,`capacity-dst_offset-off`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> metis_tac[]) >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `capacity-dst_offset-off` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_child_prefix (Var dst) h (Var p) su =
      ((Var hp,off0,Var tp),su1)`
    (mp_tac o MATCH_MP abiEncoderWindowChildTheory.window_child_prefix_variables) >>
  simp[] >> disch_then (qx_choose_then `opvar` SUBST_ALL_TAC) >>
  `not_fresh_at su1 opvar` by
    (qpat_assum `!x. Var hp = Var x \/ Var opvar = Var x \/ Var tp = Var x ==> _`
      (qspec_then `opvar` mp_tac) >> simp[]) >>
  `eval_operand (Var opvar) u2 = SOME (n2w off) /\ op_taint t2 (Var opvar) = {}` by
    (qpat_assum `!x. not_fresh_at su1 x ==> _` (qspec_then `opvar` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_assum `eval_operand (Var opvar) u1 = _`
       (assume_tac o REWRITE_RULE [venomStateTheory.eval_operand_def]) >>
     simp[venomStateTheory.eval_operand_def]) >>
  `ci_mono su2 en` by metis_tac[ci_mono_trans] >>
  `!x. src = Var x \/ Var hp = Var x \/ Var tp = Var x \/ Var opvar = Var x ==>
     not_fresh_at su2 x` by
    (qpat_assum `ci_mono su1 su2` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su2 u2 G2 t2`
    (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      (Q.INST [`H` |-> `hz`] ctor_encoder_dynamic_resources)) th)) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su2 u2 G2 t2`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  qpat_x_assum `?first last. expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved ce su2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `se` >> asm_rewrite_tac[]) >>
  `pbase <= pbase+dst_offset+off /\ pbase+dst_offset+off+LENGTH (enc at av) <= pbase+capacity` by
    decide_tac >>
  qpat_assum `inst.inst_id = shared` (fn th =>
    qpat_assum `FLOOKUP u2.vs_allocas shared = SOME (pbase,capacity)`
      (assume_tac o REWRITE_RULE [GSYM th]) >>
    qpat_assum `shared < first.cs_next_id \/ last.cs_next_id <= shared`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  qpat_assum `stmt_state_rel hz ctx func ce cx ee u2` (fn th =>
    mp_tac (Q.INST [`G` |-> `G2`,`tn` |-> `t2`,`tv` |-> `rt`,
      `sa` |-> `first`,`sb` |-> `last`,`x` |-> `root`,`b` |-> `pbase`,
      `n` |-> `capacity`,`d` |-> `pbase+dst_offset+off`,`len` |-> `LENGTH (enc at av)`]
      (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] abi_encode_values_memory_source) th))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  qabbrev_tac `info = type_to_abi_enc_info ce.ce_struct_fields ce ty` >>
  `abi_encoder_admissible info` by
    simp[Abbr `info`, abiEncoderAdmissibleTheory.abi_encoder_translation_admissible] >>
  `?ct rv. enc ct rv = enc at av /\
      !mem. mem_agree_outside t2.t_mem u2.vs_memory mem ==>
        abi_encoder_window_input info ct rv (w2n w) (val_footprint rt v) mem` by
    (qpat_assum `at = vyper_to_abi_type (get_tenv cx) ty` (fn th =>
      PURE_REWRITE_TAC [th]) >>
     simp_tac bool_ss [Abbr `info`] >>
     irule bodyFullAbiEncodeNonwordWindowTheory.abi_encode_uniform_translated_footprint_window >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `get_tenv cx` >> simp[]) >>
  `eval_operand src u2 = SOME (n2w (w2n (w:bytes32)))` by simp[] >>
  `0 < val_footprint rt v ==> w2n w + val_footprint rt v <= u2.vs_alloca_next` by
    (strip_tac >> qpat_assum `0 < val_footprint rt v ==> _` (drule_then (ACCEPT_TAC o cj 1))) >>
  `!j r n. MEM j (fn_insts func) /\ j.inst_opcode = ALLOCA /\
      j.inst_id IN frag_ids su2 mid /\ FLOOKUP u2.vs_allocas j.inst_id = SOME (r,n) ==>
      n = 32 /\ (0 < val_footprint rt v ==>
        venomMemDefs$regions_disjoint (w2n w,val_footprint rt v) (r,n)) /\
      venomMemDefs$regions_disjoint (pbase+dst_offset+off,LENGTH (enc at av)) (r,n)` by
    (mp_tac (Q.INST [`H` |-> `hz`,`s` |-> `u2`,`st` |-> `su2`,`en` |-> `mid`,
      `dst` |-> `Var tp`,`out` |-> `len`,`sa` |-> `first`,`sb` |-> `last`,
      `ei` |-> `info`,`tv` |-> `rt`,`parent` |-> `shared`,`b` |-> `pbase`,
      `sz` |-> `capacity`,`d` |-> `pbase+dst_offset+off`,
      `n` |-> `LENGTH (enc at av)`,`q` |-> `w2n (w:bytes32)`]
      (horizonTypeLib.at_horizon_named "H" abi_encode_values_scratch_separation)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `op_taint t2 (Var tp) = {}` by
    (qpat_assum `ptr_covers G2 t2 tp u2 (LENGTH (enc at av))` mp_tac >> simp[ptr_covers_def]) >>
  `!x. src = Var x \/ Var tp = Var x \/ Var hp = Var x \/ Var opvar = Var x ==>
     not_fresh_at su2 x` by
    (gen_tac >> qpat_assum `!x. src = Var x \/ Var hp = Var x \/ _ ==> _`
      (qspec_then `x` mp_tac) >> tautLib.TAUT_TAC) >>
  mp_tac (Q.INST [`s` |-> `u2`,`G` |-> `G2`,`tn` |-> `t2`,
    `st` |-> `su2`,`dest` |-> `tp`,`head` |-> `hp`,`offset` |-> `Var opvar`,
    `owner` |-> `shared`,`cursor_var` |-> `p`,`ei` |-> `info`,
    `b` |-> `pbase`,`d` |-> `pbase+dst_offset`,`sb` |-> `w2n (w:bytes32)`,
    `cap` |-> `val_footprint rt v`,`bs` |-> `enc at av`]
    abi_encode_values_dynamic_prefix_input) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (qexistsl_tac [`ct`,`rv`] >> asm_rewrite_tac[]) >>
    simp[NoAsms, LESS_EQ_ADD]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!aid. aid IN window_alloca_sites func (frag_ids su2 mid) ==> su2.cs_next_id <= aid` by
    simp[NoAsms, window_alloca_sites_def, frag_ids_def] >>
  `shared NOTIN loc INSERT window_alloca_sites func (frag_ids su2 mid)` by
    (simp_tac (srw_ss()) [IN_INSERT] >> conj_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> qpat_assum `!aid. aid IN window_alloca_sites _ _ ==> _`
       (drule_then assume_tac) >> decide_tac) >>
  `!aid. aid IN loc INSERT window_alloca_sites func (frag_ids su2 mid) ==>
      se.cs_next_id <= aid` by
    (pure_rewrite_tac [IN_INSERT] >> gen_tac >>
     disch_then (DISJ_CASES_THEN2 SUBST1_TAC assume_tac)
     >- first_assum ACCEPT_TAC >>
     qpat_assum `!aid. aid IN window_alloca_sites _ _ ==> _`
       (drule_then assume_tac) >> decide_tac) >>
  `!aid. aid IN shared INSERT loc INSERT window_alloca_sites func (frag_ids su2 mid) ==>
    ?site x. MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
      site.inst_id = aid /\ site.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp_tac (srw_ss()) [IN_INSERT, window_alloca_sites_def] >> gen_tac >> strip_tac
     >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[])
     >- (qpat_x_assum `aid = loc` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     rename1 `scratch.inst_id = aid` >>
     mp_tac (Q.INST [`ready` |-> `su2`,`body_end` |-> `mid`,`earlier` |-> `su2`,
       `obs` |-> `func`,`i` |-> `scratch`,`scopes` |-> `ee.scopes`,
       `dst` |-> `Var tp`,`out` |-> `len`,`ei` |-> `info`]
       (SPEC_ALL exprSimAbiEncodeSiteResourcesTheory.abi_encode_compiled_scratch_site)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       TRY (qpat_assum `scratch.inst_id = aid` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
       simp[NoAsms]) >> strip_tac >> qexistsl_tac [`scratch`,`q`] >> asm_rewrite_tac[]) >>
  qpat_assum `!a c ids outs v Gv tv z Gz tz. _`
    (qspecl_then [`su2`,`en`,`loc INSERT window_alloca_sites func (frag_ids su2 mid)`,
      `[(pbase+dst_offset+h,32);(pbase+dst_offset+off,LENGTH (enc at av))]`,
      `u2`,`G2`,`t2`,`z`,`Gz`,`tz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp_tac (srw_ss()) [EVERY_DEF] >> conj_tac >> decide_tac) >>
    simp_tac (srw_ss()) [EVERY_DEF] >>
    qx_gen_tac `j` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
    qpat_assum `!i. _ /\ _ /\ _ ==> (i IN tz.t_mem <=> i IN t2.t_mem)` (qspec_then `j` mp_tac) >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      PURE_REWRITE_TAC [IN_INSERT] >> first_assum ACCEPT_TAC) >>
    disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `pure_frame ce func ee se u u2 /\ wb_frame ce ee ee se u u2` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `su1`,`v` |-> `u1`,`z` |-> `u2`]
      abi_encode_saved_frames_trans) >>
     impl_tac >- (
       qpat_assum `ci_mono su su1` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
       `se.cs_next_var <= su1.cs_next_var` by decide_tac >>
       `se.cs_next_id <= su1.cs_next_id` by decide_tac >>
       asm_rewrite_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `se`,`v` |-> `u2`] abi_encode_saved_frames_trans) >>
     asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  conj_tac >- (qpat_assum `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) _ _ _ (SUC i) en z Gz tz`
    (ACCEPT_TAC o ONCE_REWRITE_RULE [ADD_COMM])) >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G1`,`u1`,`t1`] >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G2`,`u2`,`t2`] >> asm_rewrite_tac[]
QED
