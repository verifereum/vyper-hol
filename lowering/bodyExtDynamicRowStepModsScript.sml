Theory bodyExtDynamicRowStepMods
Ancestors
  bodyExtDynamicRestoredSuffixMods bodyExtDynamicPhaseFrameMods
  bodyExtRestorePackingRowMods bodyExtPackingEndpointMods
  bodyExtPackingCursorFrameMods bodyAbiEncodeRegisteredFrameMods bodyFullExtCallDirectWindows
  abiDecodeRanges reasonCopySourcePtr venomMemDefs memoryReadProps
  abiEncoderWindowJointPhases abiEncodeValuesMetadata abiEncodeValuesPrefixFrame
  abiEncodeValuesRun abiEncodeValuesPhases abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderWindowContract abiCanonicalHeadSize
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSiteResources exprSimAbiEncodePlanMetadata
  entryDecodeStaticProps allocaSiteResource bodyFullHashKeccakFixed
  exprLoweringProps wordArgsPtr exprSimWordArgs exprSimProps freshWrites stateRelProj
  bodyFullShadowBodyInv bodyExtPosSavedRowMods loweringPosts bodyPtrDefs
  fragGasOriginPtrLoop fragExec ptrDiscipline compileEnv venomState venomInst
  vyperABI vyperValue vyperStorageFootprint contractABI finite_map pred_set arithmetic words pair list
Libs horizonTypeLib

val endpoint = ``ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
  owner b capacity root dst selector``;
val horizons = ``\u Gu tu. !H. valid_horizon cx st0 H ee.storage_trace ==>
  stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo ret ce cx ee Gu tu u /\ immutable_frame_mods func ce cx ee u``;
val whole_windows = ``!p k. ((p = 0 /\ k = lo) \/ (?name. local_region ce ee.scopes u name p k) \/
  (?aid. FLOOKUP u.vs_allocas aid = SOME (p,k) /\ aid < front.cs_next_id)) ==>
  mem_bytes_at p k t.vs_memory = mem_bytes_at p k u.vs_memory /\
  (!j. p <= j /\ j < p+k /\ j IN tt.t_mem ==> j IN tu.t_mem)``;

Theorem dynamic_subwindow[local]:
  p <= q /\ q+n <= p+k /\ mem_bytes_at p k m' = mem_bytes_at p k m ==>
  mem_bytes_at q n m' = mem_bytes_at q n m
Proof
  strip_tac >>
  `q-p+n <= k /\ p+(q-p) = q` by decide_tac >>
  qpat_x_assum `mem_bytes_at p k m' = _`
    (mp_tac o Q.AP_TERM `\bs. TAKE n (DROP (q-p) bs)`) >>
  simp[mem_bytes_at_window]
QED

(* Reassemble the same fold invariant after an observed physical phase. *)
Theorem dynamic_endpoint_advance[local]:
  ^endpoint a u Gu tu /\ ^horizons t gfin tt /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  local_ptrs_reserved ce front /\ ci_mono a c /\
  window_phase ctx func a c ids outs u t /\ abi_encode_exec_frame func u t /\
  pure_frame ce func ee front u t /\ wb_frame ce ee ee front u t /\
  ghost_kept_at lo ce ee front Gu tu u gfin tt /\ alloca_history func t /\
  (!x. not_fresh_at a x ==> FLOOKUP gfin x = FLOOKUP Gu x /\
    op_taint tt (Var x) = op_taint tu (Var x)) /\
  tt.t_stor = tu.t_stor /\ tt.t_trans = tu.t_trans /\ tt.t_imm = tu.t_imm /\
  read_memory (b+28) 4 t = read_memory (b+28) 4 u /\
  (!j. b+28 <= j /\ j < b+32 /\ j IN tt.t_mem ==> j IN tu.t_mem) /\
  ^whole_windows ==>
  ^endpoint c t gfin tt
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule_then assume_tac window_phase_labels >>
  drule window_phase_effect >> strip_tac >>
  `!i r. FLOOKUP u.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC abi_encoder_registered_effect_allocated) >>
  `window_alloca_growth s t` by
    (irule window_alloca_growth_trans >> qexists `u` >> simp[]) >>
  `pure_frame ce func ee front s t` by
    (irule pure_frame_trans >>
     qpat_assum `pure_frame ce func ee front s u` (irule_at Any) >>
     qpat_assum `pure_frame ce func ee front u t` (irule_at Any) >>
     fs[wb_frame_def]) >>
  `wb_frame ce ee ee front s t` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front u t` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee front G tn s gfin tt` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front Gu tu u gfin tt` (irule_at Any) >> simp[]) >>
  suspend "physical"
QED

Resume dynamic_endpoint_advance[physical]:
  `!x w n. not_fresh_at a x /\ lookup_var x u = SOME w /\ ptr_covers Gu tu x u n ==>
     lookup_var x t = SOME w /\ ptr_covers gfin tt x t n` by
    (pure_rewrite_tac[GSYM (cj 2 eval_operand_def)] >> rpt strip_tac >>
     drule_all abi_encode_values_pointer_frame >> simp[]) >>
  `lookup_var root t = SOME (n2w b) /\ ptr_covers gfin tt root t capacity` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `lookup_var dst t = SOME (n2w (b+32)) /\ ptr_covers gfin tt dst t (capacity-32)` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `FLOOKUP gfin root = SOME (b,capacity)` by
    (qpat_assum `!x. not_fresh_at a x ==> FLOOKUP gfin x = _ /\ _`
       (qspec_then `root` mp_tac) >> simp[]) >>
  `FLOOKUP t.vs_allocas owner = SOME (b,capacity)` by
    (drule_all_then ACCEPT_TAC abi_encoder_registered_effect_allocated) >>
  `t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\ t.vs_immutables = u.vs_immutables` by
    fs[abi_encoder_registered_effect_def] >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_data_section = u.vs_data_section /\
   LENGTH u.vs_memory <= LENGTH t.vs_memory` by fs[abi_encode_exec_frame_def] >>
  qpat_assum `ci_mono a c` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    (conj_tac >> irule not_fresh_at_mono >> qexists `a` >> simp[]) >>
  `front.cs_next_var <= c.cs_next_var /\ owner < c.cs_next_id /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by decide_tac >>
  `!j. b+28 <= j /\ j < b+32 ==> j NOTIN tt.t_mem` by
    (rpt strip_tac >> `j IN tu.t_mem` by (first_x_assum irule >> simp[]) >>
     qpat_assum `!i. _ ==> i NOTIN tu.t_mem` (qspec_then `j` mp_tac) >> simp[]) >>
  PURE_REWRITE_TAC [ext_packing_endpoint_mods_def] >> asm_rewrite_tac[] >>
  suspend "windows"
QED

Resume dynamic_endpoint_advance[windows]:
  `!name p k. local_region ce ee.scopes s name p k <=> local_region ce ee.scopes u name p k` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >> simp[]) >>
  qpat_assum `wb_frame ce ee ee front s u` (assume_tac o cj 2 o REWRITE_RULE[wb_frame_def]) >>
  map_every qx_gen_tac [`q`,`n`] >> disch_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n u.vs_memory = _ /\ _`
    (qspecl_then [`q`,`n`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `?p k. p <= q /\ q+n <= p+k /\
    ((p = 0 /\ k = lo) \/ (?name. local_region ce ee.scopes u name p k) \/
     (?aid. FLOOKUP u.vs_allocas aid = SOME (p,k) /\ aid < front.cs_next_id))`
    suffices_by
    (disch_then (qx_choosel_then [`p`,`k`] (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `^whole_windows` (qspecl_then [`p`,`k`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `mem_bytes_at q n t.vs_memory = mem_bytes_at q n u.vs_memory` by
       (irule dynamic_subwindow >> qexistsl [`k`,`p`] >> simp[]) >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `p <= i /\ i < p+k` by decide_tac >>
     `i IN tu.t_mem` by (first_x_assum irule >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  qpat_x_assum `q+n <= lo \/ _` strip_assume_tac
  >- (qexistsl [`0`,`lo`] >> simp[])
  >- (rename1 `q+n <= p+k` >> qexistsl [`p`,`k`] >> simp[] >>
      disj2_tac >> disj1_tac >> rename1 `local_region ce ee.scopes s nm p k` >>
      qexists `nm` >>
      qpat_assum `!nm p k. local_region ce ee.scopes s nm p k <=>
                           local_region ce ee.scopes u nm p k`
        (qspecl_then [`nm`,`p`,`k`] mp_tac) >> simp[]) >>
  rename1 `q+n <= p+k` >> qexistsl [`p`,`k`] >> simp[] >>
  disj2_tac >> disj2_tac >> rename1 `FLOOKUP s.vs_allocas aid = SOME (p,k)` >>
  qexists `aid` >> simp[] >> first_assum irule >> simp[]
QED

Finalise dynamic_endpoint_advance

Theorem dynamic_horizon_resources[local]:
  stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at_mods D lo ret ce cx ee Gu tu u ==>
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)
Proof
  strip_tac >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  qhdtm_assum `ghost_inv_at_mods` (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  asm_rewrite_tac[] >> strip_tac >>
  qhdtm_x_assum `fmp_room` mp_tac >> simp[fmp_room_def] >> strip_tac >>
  `u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by decide_tac >>
  asm_rewrite_tac[allocas_below_fmp_def] >> rpt strip_tac >>
  qhdtm_assum `alloca_inv` (assume_tac o cj 2 o REWRITE_RULE[alloca_inv_def,alloca_next_valid_def]) >>
  qpat_assum `!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==> _`
    (drule_then assume_tac) >> decide_tac
QED

Theorem ext_dynamic_row_step_mods:
  ^endpoint a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (b+32) (Var cursor) loc slot i a u Gu tu /\
  compile_abi_encode_value_rows ce (Var dst) (Var cursor) h [(saved,ty)] a = ((),en) /\
  fn_has_code a en func /\ fn_inst_ids_distinct func /\ is_abi_dynamic ce.ce_struct_fields ty /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h+32 <= hl /\ off+LENGTH bytes <= capacity-32 /\ bytes = enc at av /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ ty = lowered_value_type ce e /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ abi_encoder_layout_valid at av /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!typ rt. evaluate_type (get_tenv cx) typ = SOME rt ==>
    type_memory_bytes ce typ = type_memory_size rt) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es sa front H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s) /\
  local_ptrs_reserved ce front /\ return_buf_frame ret ce front s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = owner /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cu (fn_insts func) /\ cu.inst_opcode = ALLOCA /\
  cu.inst_id = loc /\ cu.inst_outputs = [croot] /\ not_local_ptr ce ee.scopes croot /\
  owner < loc /\ 32 <= capacity ==>
  ?t gf tt. ^endpoint en t gf tt /\
    abi_encode_values_prefix_at ats avs hl (b+32) (Var cursor) loc slot (SUC i) en t gf tt /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,gf,tt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_dynamic_cuts >>
  disch_then (qx_choosel_then [`hop`,`offset`,`top`,`prepared`,`src`,`ready`,`len`,`encoded`]
    (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dynamic_horizon_resources >>
  qhdtm_assum `abi_encode_values_prefix_at`
    (strip_assume_tac o REWRITE_RULE[abi_encode_values_prefix_at_def]) >>
  suspend "prefix"
QED

Resume ext_dynamic_row_step_mods[prefix]:
  `p = cursor` by fs[] >> pop_assum SUBST_ALL_TAC >>
  `eval_operand (Var dst) u = SOME (n2w (b+32))` by simp[eval_operand_def] >>
  `b+capacity <= u.vs_alloca_next` by
    (qhdtm_assum `alloca_inv` (assume_tac o cj 2 o REWRITE_RULE[alloca_inv_def,alloca_next_valid_def]) >>
     first_assum irule >> qexists `owner` >> first_assum ACCEPT_TAC) >>
  `b+32+(capacity-32) <= u.vs_alloca_next /\ h+32 <= capacity-32 /\ off <= capacity-32` by decide_tac >>
  `mem_word_at slot u.vs_memory = n2w off` by asm_rewrite_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by simp[] >>
  drule_all window_child_prefix_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`pre`,`gp`,`tp`,`head`,`tail`]
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[FST,SND]))) >>
  qpat_x_assum `hop = Var head` SUBST_ALL_TAC >>
  qpat_x_assum `top = Var tail` SUBST_ALL_TAC >>
  `abi_encode_values_prefix_at ats avs hl (b+32) (Var cursor) loc slot i prepared pre gp tp` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ a u Gu tu` (irule_at Any) >>
     qpat_assum `window_phase ctx func a prepared {} [] u pre` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid:num. aid IN {} ==> front.cs_next_id <= aid` by simp[] >>
  `EVERY (\(p,n). b <= p /\ p+n <= b+capacity) []` by simp[] >>
  `!aid. aid IN owner INSERT {} ==>
    ?op x. MEM op (fn_insts func) /\ op.inst_opcode = ALLOCA /\
      op.inst_id = aid /\ op.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp[] >> qexistsl [`inst`,`root`] >> simp[]) >>
  `!j. EVERY (\(p,n). j < p \/ p+n <= j) ([]:(num # num) list) /\
    (!aid p n. aid IN {} /\ FLOOKUP pre.vs_allocas aid = SOME (p,n) ==> j < p \/ p+n <= j) /\
    j IN tp.t_mem ==> j IN tu.t_mem` by simp[] >>
  drule_all abi_encode_registered_phase_frame_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel hz ctx func ce cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> ext_pos_saved_row_mods _ _ _ _ _ _ H _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o cj 1 o cj 2))) >>
  `ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
     owner b capacity root dst selector prepared pre gp tp` by
    (irule dynamic_endpoint_advance >>
     qpat_assum `^endpoint a u Gu tu` (irule_at Any) >>
     qpat_assum `window_phase ctx func a prepared {} [] u pre` (irule_at Any) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     BETA_TAC >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (pure_rewrite_tac[read_memory_eq_mem_bytes_at] >> simp[]))) >>
  `h+32 <= off /\ b+32+h <= b+capacity /\ b+32+off <= b+capacity /\
    b+32+off+LENGTH bytes <= b+capacity /\ LENGTH bytes <= capacity-32-off` by decide_tac >>
  `b+32 + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= b+capacity /\
    b+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= b+capacity` by
    (REV_FULL_SIMP_TAC (srw_ss()) [] >> decide_tac) >>
  `abi_encoder_layout_valid (vyper_to_abi_type (get_tenv cx) ty) av` by
    (qpat_assum `at = vyper_to_abi_type _ _` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`cursor` |-> `cursor_op`] ext_restore_packing_row_mods
    |> Q.INST [`p` |-> `pre`, `Gp` |-> `gp`, `ci` |-> `cu`,
               `cursor_op` |-> `Var cursor`]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`z`,`gz`,`tz`,`first`,`last`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "suffix"
QED

Resume ext_dynamic_row_step_mods[suffix]:
  qpat_assum `^endpoint ready z gz tz`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dynamic_horizon_resources >>
  `eval_operand (Var head) z = SOME (n2w (b+32+h)) /\ ptr_covers gz tz head z 32` by
    (qpat_assum `!x w n. not_fresh_at prepared x /\ _ ==> eval_operand (Var x) z = SOME w /\ _`
       irule >> simp[]) >>
  `eval_operand (Var tail) z = SOME (n2w (b+32+off)) /\ ptr_covers gz tz tail z (capacity-32-off)` by
    (qpat_assum `!x w n. not_fresh_at prepared x /\ _ ==> eval_operand (Var x) z = SOME w /\ _`
       irule >> simp[]) >>
  `eval_operand offset z = SOME (n2w off) /\ op_taint tz offset = op_taint tp offset` by
    (qpat_assum `!op w. _ ==> eval_operand op z = SOME w /\ _` irule >> simp[]) >>
  `op_taint tz offset = {}` by simp[] >>
  `ptr_covers gz tz tail z (LENGTH bytes)` by (irule ptr_covers_mono >> qexists `capacity-32-off` >> simp[]) >>
  `!x. src = Var x \/ Var tail = Var x \/ Var head = Var x \/ offset = Var x ==>
       not_fresh_at ready x` by
    (gen_tac >> disch_then (DISJ_CASES_THEN assume_tac)
     >- (qpat_assum `!x. src = Var x ==> not_fresh_at ready x` (drule_then ACCEPT_TAC)) >>
     irule not_fresh_at_mono >> qexists `prepared` >>
     qpat_assum `ci_mono prepared ready` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     asm_rewrite_tac[] >>
     qpat_assum `!x. Var head = Var x \/ offset = Var x \/ Var tail = Var x ==> _` irule >>
     metis_tac[]) >>
  `ci_mono ready en` by (irule ci_mono_trans >> qexists `encoded` >> simp[]) >>
  `~is_word_type ty` by metis_tac[word_type_dec_sizes] >>
  `h + abi_member_head_size at <= hl` by
    (qpat_assum `is_dynamic at` (fn th => simp_tac bool_ss [abi_member_head_size_def,th]) >>
     first_assum ACCEPT_TAC) >>
  `owner <> loc /\ b <= b+32` by
    (simp[] >> qpat_assum `owner < loc` mp_tac >> decide_tac) >>
  `?t gf tf.
    abi_encode_values_prefix_at ats avs hl (b+32) (Var cursor) loc slot (SUC i) en t gf tf /\
    window_phase ctx func ready en (loc INSERT window_alloca_sites func (frag_ids ready encoded))
      [(b+32+h,32);(b+32+off,LENGTH bytes)] z t /\
    abi_encode_exec_frame func z t /\
    (!x. not_fresh_at ready x ==>
      FLOOKUP gf x = FLOOKUP gz x /\ op_taint tf (Var x) = op_taint tz (Var x)) /\
    (!j. (j < b+32+h \/ b+32+h+32 <= j) /\
      (j < b+32+off \/ b+32+off+LENGTH bytes <= j) /\
      (!aid p k. aid IN loc INSERT window_alloca_sites func (frag_ids ready encoded) /\
        FLOOKUP t.vs_allocas aid = SOME (p,k) ==> j < p \/ p+k <= j) ==>
      (j IN tf.t_mem <=> j IN tz.t_mem)) /\
    tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,gz,tz) [] (OK t,gf,tf)` suffices_by
    (disch_then (qx_choosel_then [`t`,`gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
     suspend "phase_frame") >>
  irule (horizonTypeLib.at_horizon_named "H" ext_dynamic_restored_suffix_mods) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ ready = _` (irule_at Any) >>
     qpat_assum `expr_val_at ce cx ty first last ee v src z` (irule_at Any) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee z` (irule_at Any) >>
     qpat_assum `unwrap_value ce saved prepared = (src,ready)` (irule_at Any) >>
     qpat_assum `FLOOKUP z.vs_allocas owner = SOME (b,capacity)` (irule_at Any) >>
     qpat_assum `inst.inst_id = owner` (irule_at Any) >>
     qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (irule_at Any) >>
     qpat_assum `vyper_to_abi (get_tenv cx) ty v = SOME av` (irule_at Any) >>
     qpat_assum `at = EL i ats` (irule_at Any) >>
  qexistsl [`root`,`offset`,`head`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ext_dynamic_row_step_mods[phase_frame]:
  `a.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= ready.cs_next_var /\
    a.cs_next_id <= prepared.cs_next_id /\ prepared.cs_next_id <= ready.cs_next_id` by
    (qpat_assum `ci_mono a prepared` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     qpat_assum `ci_mono prepared ready` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     asm_rewrite_tac[]) >>
  `front.cs_next_var <= ready.cs_next_var /\ loc < ready.cs_next_id` by
    (qpat_assum `front.cs_next_var <= a.cs_next_var` mp_tac >>
     qpat_assum `loc < a.cs_next_id` mp_tac >>
     qpat_assum `a.cs_next_var <= prepared.cs_next_var` mp_tac >>
     qpat_assum `prepared.cs_next_var <= ready.cs_next_var` mp_tac >>
     qpat_assum `a.cs_next_id <= prepared.cs_next_id` mp_tac >>
     qpat_assum `prepared.cs_next_id <= ready.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  mp_tac (Q.INST [`owner` |-> `inst`, `cursor` |-> `cu`,
    `cursor_var` |-> `croot`, `dst` |-> `Var tail`,
    `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce ty`,
    `Gz` |-> `gz`, `Gf` |-> `gf`, `tt` |-> `tf`, `d` |-> `ret`]
    (INST_TYPE [Type.alpha |-> ``:word8``] ext_dynamic_phase_frame_mods)
    |> Q.INST [`shared` |-> `owner:num`, `cap` |-> `capacity`]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "protected_windows"
QED

Resume ext_dynamic_row_step_mods[protected_windows]:
  qabbrev_tac `ids = loc INSERT window_alloca_sites func (frag_ids ready encoded)` >>
  qabbrev_tac `outs = [(b+32+h,32);(b+32+off,LENGTH bytes)]` >>
  `!aid. aid IN ids ==> front.cs_next_id <= aid` by
    (simp_tac (srw_ss()) [Abbr `ids`,window_alloca_sites_def,abiEncoderPropsTheory.frag_ids_def] >>
     rpt strip_tac >>
     qpat_assum `front.cs_next_id <= owner` mp_tac >>
     qpat_assum `owner < loc` mp_tac >>
     qpat_assum `loc < ready.cs_next_id` mp_tac >>
     (qpat_assum `aid = loc` mp_tac ORELSE
      qpat_assum `ready.cs_next_id <= aid` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `EVERY (\(p,n). b <= p /\ p+n <= b+capacity) outs` by
    (simp_tac (srw_ss()) [Abbr `outs`] >>
     qpat_assum `h+32 <= off` mp_tac >>
     qpat_assum `b+32+off+LENGTH bytes <= b+capacity` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!aid. aid IN owner INSERT ids ==>
     ?op x. MEM op (fn_insts func) /\ op.inst_opcode = ALLOCA /\
       op.inst_id = aid /\ op.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp_tac bool_ss [Abbr `ids`, IN_INSERT] >> gen_tac >>
     disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
     >- (qexistsl [`inst`,`root`] >> asm_rewrite_tac[]) >>
     disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
     >- (qexistsl [`cu`,`croot`] >> asm_rewrite_tac[]) >>
     simp_tac (srw_ss()) [window_alloca_sites_def] >> strip_tac >>
     rename1 `site.inst_id = aid` >>
     `site.inst_id IN frag_ids ready encoded` by simp[] >>
     `!op. MEM op (fn_insts func) /\ op.inst_opcode <> STOP /\ op.inst_opcode <> NOP ==>
        MEM op (fn_insts func)` by simp[] >>
     drule_all (Q.INST [`obs` |-> `func`, `earlier` |-> `front`, `scopes` |-> `ee.scopes`]
       abi_encode_compiled_scratch_site) >>
     disch_then (qspec_then `ee` strip_assume_tac) >>
     rename1 `site.inst_outputs = [scratch]` >> qexistsl [`site`,`scratch`] >> asm_rewrite_tac[]) >>
  `!j. EVERY (\(p,n). j < p \/ p+n <= j) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==> j < p \/ p+n <= j) /\
    j IN tf.t_mem ==> j IN tz.t_mem` by
    (simp_tac (srw_ss()) [Abbr `outs`] >> gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j. _ ==> (j IN tf.t_mem <=> j IN tz.t_mem)` (qspec_then `j` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  drule_all_then (assume_tac o CONJUNCT1)
    (Q.INST [`cut` |-> `front.cs_next_id`, `s` |-> `z`, `tn` |-> `tz`, `tn'` |-> `tf`]
      extcall_direct_encode_windows) >>
  qexistsl [`t`,`gf`,`tf`] >>
  conj_tac
  >- (irule dynamic_endpoint_advance >>
      qpat_assum `^endpoint ready z gz tz` (irule_at Any) >>
      qpat_assum `window_phase ctx func ready en ids outs z t` (irule_at Any) >>
      qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
      qpat_assum `read_memory (b+28) 4 t = read_memory (b+28) 4 z` (irule_at Any) >>
      BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >> gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl [`gp`,`pre`,`tp`] >>
  conj_tac >- first_assum irule >>
  irule gas_origin_ptr_path_trans >> qexistsl [`gz`,`z`,`tz`] >>
  conj_tac >> first_assum irule
QED

Finalise ext_dynamic_row_step_mods
