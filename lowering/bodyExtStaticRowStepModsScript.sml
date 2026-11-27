(* The static callback: prepare the head, restore the saved row, then write
   only that head. Every observation is taken at the reached endpoint. *)
Theory bodyExtStaticRowStepMods
Ancestors
  bodyExtStaticHeadAddressMods bodyExtStaticRestoredStoreMods
  bodyExtRestorePackingRowMods bodyExtPackingEndpointMods
  bodyAbiEncodeRegisteredFrameMods bodyFullExtCallDirectWindows
  allocaSiteResource
  abiEncodeValuesRun abiEncodeValuesMetadata abiEncodeValuesPhases abiCanonicalHeadSize
  abiEncoderWindowPhase abiEncoderRegisteredEffect abiEncoderWindowContract
  exprSimAbiEncodeExecFrame exprSimAbiEncodePlanMetadata
  exprSimWordArgs exprSimProps wordArgsPtr memoryReadProps
  fragGasOriginPtrLoop stateRelProj freshWrites loweringPosts
  exprLoweringProps bodyPtrDefs ptrDiscipline bodyFullShadowBodyInv
  venomState venomMemDefs finite_map pred_set arithmetic list pair
Libs horizonTypeLib

val entry = ``ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner b capacity root dst selector a u Gu tu``;
val exit = ``ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner b capacity root dst selector c w Gw tw``;
val row_sites = ``MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = owner /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root``;
val phase_context = ``fn_inst_ids_distinct func /\ local_ptrs_reserved ce front /\
    (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
    (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
    stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s``;
val phase_path = ``!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK w,Gw,tw)``;

Triviality phase_subrange:
  p <= q /\ q+n <= p+k /\ mem_bytes_at p k m' = mem_bytes_at p k m ==>
  mem_bytes_at q n m' = mem_bytes_at q n m
Proof
  strip_tac >> `q-p+n <= k /\ p+(q-p) = q` by decide_tac >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `mem_bytes_at p k m' = _`
    (mp_tac o Q.AP_TERM `\bs. TAKE n (DROP (q-p) bs)`) >>
  simp[mem_bytes_at_window]
QED

(* Both static phases use no allocation sites. The output list distinguishes
   the address calculation from the head-only store. *)
Triviality static_phase_endpoint:
  ^entry /\ ^phase_context /\ ^row_sites /\ 32 <= capacity /\
  ci_mono a c /\ window_phase ctx func a c {} outs u w /\
  abi_encode_exec_frame func u w /\ ^phase_path /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gw x = FLOOKUP Gu x /\ op_taint tw (Var x) = op_taint tu (Var x)) /\
  tw.t_stor = tu.t_stor /\ tw.t_trans = tu.t_trans /\ tw.t_imm = tu.t_imm /\
  EVERY (\(p,n). b+32 <= p /\ p+n <= b+capacity) outs /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\ i IN tw.t_mem ==> i IN tu.t_mem) ==>
  ^exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  `!aid. aid IN owner INSERT ({}:num set) ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp[] >> qexistsl [`inst`,`root`] >> asm_rewrite_tac[]) >>
  `EVERY (\(p,n). b <= p /\ p+n <= b+capacity) outs /\
   EVERY (\r. venomMemDefs$regions_disjoint (b+28,4) r) outs` by
    (fs[EVERY_MEM,FORALL_PROD,venomMemDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ({}:num set) /\ FLOOKUP w.vs_allocas aid = SOME (p,n) ==>
       i < p \/ p+n <= i) /\ i IN tw.t_mem ==> i IN tu.t_mem` by simp[] >>
  `!aid:num. aid IN {} ==> front.cs_next_id <= aid` by simp[] >>
  `owner NOTIN ({}:num set)` by simp[] >>
  drule_all abi_encode_registered_phase_frame_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "observations"
QED

Resume static_phase_endpoint[observations]:
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `b <= b+28 /\ b+28+4 <= b+capacity` by decide_tac >>
  drule_all abi_encode_values_registered_window >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `read_memory (b+28) 4 w = selector` by fs[read_memory_eq_mem_bytes_at] >>
  `!i. b+28 <= i /\ i < b+32 ==> i NOTIN tw.t_mem` by
    (rpt strip_tac >> `i < b+28+4` by decide_tac >>
     qpat_assum `!i. b+28 <= i /\ _ /\ i IN tw.t_mem ==> _`
       (qspecl_then [`i`] (drule_all_then assume_tac)) >>
     qpat_assum `!i. b+28 <= i /\ i < b+32 ==> i NOTIN tu.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `!x value n. not_fresh_at a x /\ lookup_var x u = SOME value /\ ptr_covers Gu tu x u n ==>
     lookup_var x w = SOME value /\ ptr_covers Gw tw x w n` by
    (pure_rewrite_tac[GSYM (cj 2 eval_operand_def)] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all_then ACCEPT_TAC abi_encode_values_pointer_frame) >>
  `lookup_var root w = SOME (n2w b) /\ ptr_covers Gw tw root w capacity` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `lookup_var dst w = SOME (n2w (b+32)) /\ ptr_covers Gw tw dst w (capacity-32)` by
    (qpat_assum `!x value n. _ ==> lookup_var x w = SOME value /\ _` irule >> asm_rewrite_tac[]) >>
  `FLOOKUP Gw root = SOME (b,capacity)` by
    (qpat_assum `!x. not_fresh_at a x ==> FLOOKUP Gw x = _ /\ _` (drule_then strip_assume_tac) >> fs[]) >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_phase_labels >>
  drule_then assume_tac window_phase_effect >>
  suspend "compose"
QED

Resume static_phase_endpoint[compose]:
  `window_alloca_growth s w` by
    (irule window_alloca_growth_trans >> qexists `u` >> asm_rewrite_tac[]) >>
  `pure_frame ce func ee front s w` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ee`,`front`,`u`] >> fs[wb_frame_def]) >>
  `wb_frame ce ee ee front s w` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front u w` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee front G tn s Gw tw` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front Gu tu u Gw tw` (irule_at Any) >> simp[]) >>
  `w.vs_accounts = u.vs_accounts /\ w.vs_transient = u.vs_transient /\
   w.vs_immutables = u.vs_immutables` by
    (qhdtm_assum `abi_encoder_registered_effect` mp_tac >>
     pure_rewrite_tac[abi_encoder_registered_effect_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `w.vs_call_ctx = u.vs_call_ctx /\ w.vs_data_section = u.vs_data_section /\
   LENGTH u.vs_memory <= LENGTH w.vs_memory` by
    (qhdtm_assum `abi_encode_exec_frame` mp_tac >>
     pure_rewrite_tac[abi_encode_exec_frame_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `ci_mono` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    (conj_tac >> irule not_fresh_at_mono >> qexists `a` >> asm_rewrite_tac[]) >>
  `front.cs_next_var <= c.cs_next_var /\ owner < c.cs_next_id /\
   LENGTH s.vs_memory <= LENGTH w.vs_memory` by decide_tac >>
  suspend "protected"
QED

Resume static_phase_endpoint[protected]:
  drule_all_then (assume_tac o CONJUNCT1) extcall_direct_encode_windows >>
  `!nm p k. local_region ce ee.scopes s nm p k <=> local_region ce ee.scopes u nm p k` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >> simp[]) >>
  qpat_assum `wb_frame ce ee ee front s u`
    (assume_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
  pure_rewrite_tac[ext_packing_endpoint_mods_def] >> asm_rewrite_tac[] >>
  rpt gen_tac >> rename1 `mem_bytes_at q n w.vs_memory = _ /\ _` >> disch_tac >>
  qpat_assum `!q n. q+n <= lo \/ _ ==> mem_bytes_at q n u.vs_memory = _ /\ _`
    (qspecl_then [`q`,`n`] mp_tac) >>
  (impl_tac >- (qpat_assum `!nm p k. local_region _ _ s nm p k <=> _`
     (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?p k. p <= q /\ q+n <= p+k /\
    ((p = 0 /\ k = lo) \/ (?name. local_region ce ee.scopes u name p k) \/
      (?aid. FLOOKUP u.vs_allocas aid = SOME (p,k) /\ aid < front.cs_next_id))` suffices_by
   (disch_then (qx_choosel_then [`p`,`k`] (map_every assume_tac o CONJUNCTS)) >>
    qpat_assum `!b n. _ ==> mem_bytes_at b n w.vs_memory = _ /\ _`
      (qspecl_then [`p`,`k`] mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    `mem_bytes_at q n w.vs_memory = mem_bytes_at q n u.vs_memory` by
      (irule phase_subrange >> qexistsl [`k`,`p`] >> asm_rewrite_tac[]) >>
    asm_rewrite_tac[] >> rpt strip_tac >>
    `p <= i /\ i < p+k` by decide_tac >>
    `i IN tu.t_mem` by
      (qpat_assum `!i. p <= i /\ _ /\ i IN tw.t_mem ==> _`
        (qspec_then `i` (drule_all_then ACCEPT_TAC))) >>
    qpat_assum `!i. q <= i /\ _ /\ i IN tu.t_mem ==> _`
      (qspec_then `i` (drule_all_then ACCEPT_TAC))) >>
  qpat_x_assum `q+n <= lo \/ _` strip_assume_tac
  >- (qexistsl [`0`,`lo`] >> simp[])
  >- (qexistsl [`p`,`k`] >> asm_rewrite_tac[] >> disj2_tac >> disj1_tac >>
      qexists `name` >> fs[]) >>
  qexistsl [`p`,`k`] >> asm_rewrite_tac[] >> disj2_tac >> disj2_tac >>
  qexists `id` >> simp[]
QED

Finalise static_phase_endpoint[local]

Triviality static_row_fmp:
  stmt_state_rel H ctx func ce cx ee u ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp
Proof
  strip_tac >> strip_tac >>
  drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  simp[allocas_below_fmp_def] >> rpt gen_tac >> strip_tac >>
  drule_all alloca_site_registered_below >> decide_tac
QED

val packing_start = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es sa front H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s``;
val typed_saved = ``ty = lowered_value_type ce e /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
    abi_encoder_layout_valid (vyper_to_abi_type (get_tenv cx) ty) av``;
val row_prefix = ``abi_encode_values_prefix_at ats avs hl (b+32) cursor loc slot i``;

Theorem ext_static_row_step_mods:
  ^entry /\ ^phase_context /\ ^row_sites /\ ^packing_start /\ ^typed_saved /\
  storage_trace_domain cx st0 ee.storage_trace /\ return_buf_frame ret ce front s /\
  MEM ci (fn_insts func) /\ ci.inst_id = loc /\ ci.inst_outputs = [croot] /\
  not_local_ptr ce ee.scopes croot /\ owner < loc /\ 32 <= capacity /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  ~is_dynamic at /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h+hs <= hl /\
  b+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= b+capacity /\
  ^row_prefix a u Gu tu /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c) /\
  fn_has_code a c func ==>
  ?w Gw tw. ^exit /\
    abi_encode_values_prefix_at ats avs hl (b+32) cursor loc slot (SUC i) c w Gw tw /\
    ^phase_path
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by
    (drule_all abi_encode_translated_dynamic >>
     qpat_assum `at = vyper_to_abi_type _ _`
       (fn th => disch_then (fn eq => pure_rewrite_tac [REWRITE_RULE [GSYM th] eq])) >>
     first_assum ACCEPT_TAC) >>
  `abi_encoder_layout_valid at av` by
    (qpat_assum `at = vyper_to_abi_type _ _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all abi_encode_values_static_cuts >>
  disch_then (qx_choosel_then [`head`,`prepared`,`src`,`ready`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `^entry`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_room ctx func u` by drule_then ACCEPT_TAC stmt_state_rel_alloca_room >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx ee u` (mp_then Any mp_tac static_row_fmp) >> simp[]) >>
  suspend "address"
QED

Resume ext_static_row_step_mods[address]:
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `b+capacity <= u.vs_alloca_next` by drule_all_then ACCEPT_TAC alloca_site_registered_below >>
  `h+hs <= capacity-32 /\ b+32+(capacity-32) <= u.vs_alloca_next` by decide_tac >>
  `eval_operand (Var dst) u = SOME (n2w (b+32))` by simp[eval_operand_def] >>
  drule_all ext_static_head_address_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`hp`,`p`,`Gp`,`tp`] (map_every assume_tac o CONJUNCTS))) >>
  `EVERY (\(p,n). b+32 <= p /\ p+n <= b+capacity) [] /\
   (!j. EVERY (\(p,n). j < p \/ p+n <= j) [] /\ j IN tp.t_mem ==> j IN tu.t_mem)` by simp[] >>
  drule_all_then assume_tac static_phase_endpoint >>
  suspend "restore"
QED

Resume ext_static_row_step_mods[restore]:
  `b+32+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= b+capacity` by decide_tac >>
  qpat_assum `ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
      owner b capacity root dst selector prepared p Gp tp`
    (mp_then (Pat `ext_packing_endpoint_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (mp_tac o SPEC_ALL) ext_restore_packing_row_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`first`,`last`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `head = Var hp` SUBST_ALL_TAC >>
  `eval_operand (Var hp) z = SOME (n2w (b+32+h)) /\ ptr_covers Gz tz hp z hs` by
    (qpat_assum `!x w n. not_fresh_at prepared x /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `not_fresh_at ready hp` by
    (irule not_fresh_at_mono >> qexists `prepared` >> fs[ci_mono_def]) >>
  suspend "store"
QED

Resume ext_static_row_step_mods[store]:
  qpat_assum `ext_packing_endpoint_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready z Gz tz`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `alloca_inv z` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_room ctx func z` by drule_then ACCEPT_TAC stmt_state_rel_alloca_room >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `~is_word_type ty ==> ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    stmt_state_rel hz ctx func ce cx ee z /\ expr_val_at ce cx ty first last ee v src z /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    (inst.inst_id < first.cs_next_id \/ last.cs_next_id <= inst.inst_id)` by simp[] >>
  `is_word_type ty ==> op_taint tz src = {}` by simp[] >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (b,capacity) /\ inst.inst_id <> loc` by (simp[] >> decide_tac) >>
  `b <= b+32` by simp[] >>
  suspend "credit"
QED

Resume ext_static_row_step_mods[credit]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gp`,`p`,`tp`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z /\
      z.vs_alloca_next + pending_alloca_size func z <= w2n z.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx ee z`
      (mp_then Any ACCEPT_TAC static_row_fmp)) >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `b+32+off <= b+capacity` by (simp[Abbr `off`] >> decide_tac) >>
  `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` by simp[Abbr `off`] >>
  qpat_assum `^row_prefix ready z Gz tz`
    (mp_then (Pos hd) (fn th =>
       qpat_assum `compile_store_memory ce src (Var hp) ty ty ready = ((),c)`
         (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) (mp_tac o SPEC_ALL) th))
      (Q.INST [`d` |-> `b+32`, `H` |-> `hz:(bool # bytes32 # type_value) list # num list`]
        (horizonTypeLib.at_horizon_named "H" ext_static_restored_store_mods))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`w`,`Gw`,`tw`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "advance"
QED

Resume ext_static_row_step_mods[advance]:
  `EVERY (\(q,n). b+32 <= q /\ q+n <= b+capacity) [(b+32+h,hs)]` by
    (simp_tac bool_ss [EVERY_DEF, pairTheory.UNCURRY, FST, SND] >>
     qpat_assum `h+hs <= hl` mp_tac >>
     qpat_assum `b+32+hl+LENGTH _ <= b+capacity` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!j. EVERY (\(q,n). j < q \/ q+n <= j) [(b+32+h,hs)] /\ j IN tw.t_mem ==> j IN tz.t_mem` by
    (simp_tac bool_ss [EVERY_DEF,pairTheory.UNCURRY,FST,SND] >> gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j. j < b+32+h \/ b+32+h+hs <= j ==> _`
       (qspec_then `j` (drule_then assume_tac)) >> fs[]) >>
  drule_all_then assume_tac static_phase_endpoint >>
  qexistsl [`w`,`Gw`,`tw`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gz`,`z`,`tz`] >> simp[]
QED

Finalise ext_static_row_step_mods
