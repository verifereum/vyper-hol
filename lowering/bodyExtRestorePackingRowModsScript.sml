(* Restore one selected row at the reached prepare cut, without writing the tuple. *)
Theory bodyExtRestorePackingRowMods
Ancestors
  bodyExtPackingEndpointMods bodyExtPreparedSavedRowMods bodyExtUnwrapProtectedMods
  bodyExtSavedRowInputMods bodyExtPosSavedRowMods
  bodyAbiEncodeSavedSlotMods bodyAbiEncodeSavedCodeMods bodyMemoryDefs
  bodyAbiEncodePackedPostMods exprLowering context valueEncodingTyping words
  abiEncoderWindowContract exprSimSubscriptArrayFrame exprSimWordArgs
  exprSimProps wordArgsPtr gasOriginPtrLabels fragGasOriginPtr
  stateRelProj exprLoweringProps freshWrites loweringPosts bodyPtrDefs
  loweringStateRelDefs ptrDiscipline exprSimStorageCopy venomState venomInst
  valueEncodingDefs memoryReadProps finite_map pred_set arithmetic pair list
  bodyPtrIfExpAllocSource

(* Only the nonempty portions of a saved read need a protected window. *)
Theorem saved_read_window[local]:
  abi_encode_saved_row_mods lo ce cx sa front e saved v si sm ss vv copy H ee G tn s /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  eval_operand (vv_operand saved) s = SOME w /\ val_wf tv v /\
  ((~is_word_type (lowered_value_type ce e) /\
    (vv_location saved = NONE \/ vv_location saved = SOME LocMemory)) \/
   (ce.ce_is_ctor /\ vv_location saved = SOME LocCode)) ==>
  val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= lo \/
  (?name b n. local_region ce ee.scopes s name b n /\ b <= w2n w /\
      w2n w + val_footprint tv v <= b+n) \/
  (?aid b n. aid < front.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) /\
      b <= w2n w /\ w2n w + val_footprint tv v <= b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `_ \/ (ce.ce_is_ctor /\ _)`
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 assume_tac assume_tac)
      (CONJUNCTS_THEN2 assume_tac assume_tac))
  >- (qpat_x_assum `?raw. read_result _ raw _ = _ /\ _`
        (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
      Cases_on `saved` >>
      gvs[vv_location_def,vv_operand_def,vv_at_def,expr_val_at_def] >>
      metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_assum `ce.ce_is_ctor /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
  disj2_tac >> disj1_tac >> decide_tac
QED

val packing_start = ``
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es sa front H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s)``;

val at_prepared = ``
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa prepared e saved v si sm ss vv copy H ee Gp tp p /\
    stmt_state_rel H ctx func ce cx ee p /\ immutable_frame_mods func ce cx ee p /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee Gp tp p``;

val typed_saved = ``
  ty = lowered_value_type ce e /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid (vyper_to_abi_type (get_tenv cx) ty) av``;

val prepared_endpoint = ``ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner b capacity root dst selector prepared p Gp tp``;

Theorem prepare_saved_at_endpoint[local]:
  ^packing_start /\ ^prepared_endpoint /\ ^typed_saved ==>
  ?si sm ss vv copy.
    ^at_prepared /\
    (!x. vv_operand saved = Var x ==> not_fresh_at prepared x) /\
    op_taint tp (vv_operand saved) = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ext_packing_endpoint_mods_def]) >>
  qhdtm_assum `wb_frame` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  qhdtm_assum `ghost_kept_at` (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qhdtm_assum `window_alloca_growth` (assume_tac o cj 1 o REWRITE_RULE [window_alloca_growth_def]) >>
  `front.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee p /\ immutable_frame_mods func ce cx ee p /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee Gp tp p` by simp[] >>
  `!w. eval_operand (vv_operand saved) s = SOME w /\
       ((~is_word_type ty /\ (vv_location saved = NONE \/ vv_location saved = SOME LocMemory)) \/
        (ce.ce_is_ctor /\ vv_location saved = SOME LocCode)) ==>
     mem_bytes_at (w2n w) (val_footprint tv v) p.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
     (!j. w2n w <= j /\ j < w2n w + val_footprint tv v /\ j IN tp.t_mem ==> j IN tn.t_mem)` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >> suspend "saved_read") >>
  drule_all ext_prepared_saved_row_mods >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w`,`at`,`bytes`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`si`,`sm`,`ss`,`vv`,`copy`] >> asm_rewrite_tac[]
QED

Resume prepare_saved_at_endpoint[saved_read]:
  `val_wf tv v` by simp[value_has_type_val_wf] >>
  drule_all ext_saved_row_input_mods >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w0`,`at`,`bytes`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (assume_tac o cj 1))) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  drule_all saved_read_window >>
  disch_then (DISJ_CASES_THEN2 assume_tac assume_tac)
  >- simp[mem_bytes_at_def] >>
  `w0 = w` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_assum `!b n. b+n <= lo \/ _ ==> _`
    (qspecl_then [`w2n w`,`val_footprint tv v`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise prepare_saved_at_endpoint

(* Copy packets provide these effects for the very state that holds src. *)
val copy_tail_pre = ``
  FLOOKUP a0.vs_allocas prepared.cs_next_id = SOME (w2n w,type_memory_size tv) /\
  exec_alloca (mk_inst prepared.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [x])
    p (n2w (type_memory_size tv) : bytes32) = OK a0 /\ copy_static z = copy_static a0 /\
  (!aid q n. aid < prepared.cs_next_id /\ FLOOKUP p.vs_allocas aid = SOME (q,n) ==>
    regions_disjoint (w2n w) (type_memory_size tv) q n) /\
  lo <= w2n w /\
  (!q n. q+n <= w2n w \/ w2n w+type_memory_size tv <= q ==>
    mem_bytes_at q n z.vs_memory = mem_bytes_at q n p.vs_memory) /\
  (!j. j < w2n w \/ w2n w+type_memory_size tv <= j ==> j IN tz.t_mem ==> j IN tp.t_mem)``;

Theorem copy_tail_frame[local]:
  ^copy_tail_pre ==>
  window_alloca_growth p z /\
  (!q n. (q+n <= lo \/
    (?aid a k. aid < prepared.cs_next_id /\ FLOOKUP p.vs_allocas aid = SOME (a,k) /\
       a <= q /\ q+n <= a+k)) ==>
    mem_bytes_at q n z.vs_memory = mem_bytes_at q n p.vs_memory /\
    (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (`window_alloca_growth p a0` by
        (qpat_assum `exec_alloca _ _ _ = OK _`
           (mp_then Any mp_tac window_exec_alloca_growth) >> simp[mk_inst_def]) >>
      fs[window_alloca_growth_def,copy_static_def,venom_state_component_equality] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `q+n <= w2n w \/ w2n w+type_memory_size tv <= q` suffices_by
    (disch_tac >> conj_tac
     >- (qpat_assum `!q n. _ ==> mem_bytes_at q n z.vs_memory = _` irule >>
         first_assum ACCEPT_TAC) >>
     gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j. j < _ \/ _ <= j ==> j IN tz.t_mem ==> _`
       (qspec_then `j` (irule o REWRITE_RULE [AND_IMP_INTRO])) >>
     conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  qpat_x_assum `_ <= lo \/ _` strip_assume_tac >- decide_tac >>
  qpat_assum `!aid q n. aid < prepared.cs_next_id /\ _ ==> _` (drule_all_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

val restored_horizons = ``
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee Gz tz z``;

val copy_tail_post = ``
  ^restored_horizons /\ ~z.vs_halted /\ z.vs_current_bb = ready.cs_current_bb /\
  z.vs_inst_idx = LENGTH ready.cs_current_insts /\ alloca_history func z /\
  pure_frame ce func ee prepared p z /\ wb_frame ce ee ee prepared p z /\
  ghost_kept_at lo ce ee prepared Gp tp p Gz tz /\ window_alloca_growth p z /\
  z.vs_labels = p.vs_labels /\ z.vs_accounts = p.vs_accounts /\ z.vs_transient = p.vs_transient /\
  z.vs_call_ctx = p.vs_call_ctx /\ z.vs_immutables = p.vs_immutables /\
  z.vs_data_section = p.vs_data_section /\ LENGTH p.vs_memory <= LENGTH z.vs_memory /\
  tz.t_stor = tp.t_stor /\ tz.t_trans = tp.t_trans /\ tz.t_imm = tp.t_imm /\
  (!q n. (q+n <= lo \/
    (?aid a k. aid < prepared.cs_next_id /\ FLOOKUP p.vs_allocas aid = SOME (a,k) /\
       a <= q /\ q+n <= a+k)) ==>
    mem_bytes_at q n z.vs_memory = mem_bytes_at q n p.vs_memory /\
    (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem))``;

val ptr_path = ``!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) [] (OK z,Gz,tz)``;

val restored_src = ``expr_val_at ce cx ty first last ee v src z /\ expr_val_rel cx ty v src z /\
    ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    (!x. src = Var x ==> not_fresh_at ready x) /\ op_taint tz src = {}``;

(* Normalize the two checked copy packets to one frame shape. *)
Theorem restore_copy_at_prepared[local]:
  ^at_prepared /\ ^typed_saved /\ saved = LocatedValue ty vp /\ vp.ptr_location <> LocMemory /\
  unwrap_value ce saved prepared = (src,ready) /\ fn_has_code prepared ready func /\
  fn_inst_ids_distinct func /\ alloca_history func p /\ ~p.vs_halted /\
  p.vs_current_bb = prepared.cs_current_bb /\ p.vs_inst_idx = LENGTH prepared.cs_current_insts /\
  return_buf_frame ret ce prepared p /\ storage_trace_domain cx st0 ee.storage_trace ==>
  ?z Gz tz. ^ptr_path /\ ^copy_tail_post /\ return_buf_frame ret ce ready z /\
    (?first last. first = prepared /\ last = ready /\ ^restored_src)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vp.ptr_location = LocCode`
  >- suspend "code" >> suspend "slot"
QED

Resume restore_copy_at_prepared[code]:
  drule_all abi_encode_saved_code_restore_packet_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`x`,`w`,`a0`]
       (map_every assume_tac o CONJUNCTS))) >>
  drule_all copy_tail_frame >> strip_tac >>
  `z.vs_labels = p.vs_labels` by
    (qpat_assum `^ptr_path` (qspec_then `(DF (storage_trace_horizon ee.storage_trace))` mp_tac) >>
     disch_then (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_preserves_labels)) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  qexistsl [`prepared`,`ready`] >> asm_rewrite_tac[] >>
  qpat_x_assum `src = Var x` SUBST_ALL_TAC >> gvs[]
QED

Resume restore_copy_at_prepared[slot]:
  `vp.ptr_location <> LocCalldata` by
    (disch_tac >>
     `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `^at_prepared` (drule_then (assume_tac o cj 1)) >>
     qhdtm_x_assum `abi_encode_saved_row_mods`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
     gvs[bodyFullPostsModsTheory.vv_holds_mods_def,vv_holds_def]) >>
  Q.SUBGOAL_THEN `vp.ptr_location = LocStorage \/ vp.ptr_location = LocTransient` assume_tac
  >- (Cases_on `vp.ptr_location` >> gvs[]) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  drule_all abi_encode_saved_slot_restore_packet_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`w`,`x`]
       (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `?u. exec_alloca _ _ _ = OK u /\ _`
    (qx_choose_then `a0` (map_every assume_tac o CONJUNCTS)) >>
  `!aid q n. aid < prepared.cs_next_id /\ FLOOKUP p.vs_allocas aid = SOME (q,n) ==>
      regions_disjoint (w2n w) (type_memory_size tv) q n` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!aid q n. aid < prepared.cs_next_id /\ _ ==> regions_disjoint _ _ _ _ /\ _`
       (qspecl_then [`aid`,`q`,`n`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o cj 1)) >>
  drule_all copy_tail_frame >> strip_tac >>
  `z.vs_labels = p.vs_labels` by
    (qpat_assum `^ptr_path` (qspec_then `(DF (storage_trace_horizon ee.storage_trace))` mp_tac) >>
     disch_then (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_preserves_labels)) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  qexistsl [`prepared`,`ready`] >> asm_rewrite_tac[] >>
  qpat_x_assum `src = Var x` SUBST_ALL_TAC >> gvs[]
QED

Finalise restore_copy_at_prepared

val prefix_at_prepared = ``abi_encode_values_prefix_at ats avs hl (b+32) cursor loc slot i prepared p Gp tp``;
val prefix_at_ready = ``abi_encode_values_prefix_at ats avs hl (b+32) cursor loc slot i ready z Gz tz``;
val ready_endpoint = ``ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner b capacity root dst selector ready z Gz tz``;

val old_operands = ``
  (!op w. (!x. op = Var x ==> not_fresh_at prepared x) /\
    eval_operand op p = SOME w ==> eval_operand op z = SOME w /\ op_taint tz op = op_taint tp op) /\
  (!x w n. not_fresh_at prepared x /\ eval_operand (Var x) p = SOME w /\
    ptr_covers Gp tp x p n ==> eval_operand (Var x) z = SOME w /\ ptr_covers Gz tz x z n)``;

val buffer_sites = ``
  MEM inst (fn_insts func) /\ inst.inst_id = owner /\ inst.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  MEM ci (fn_insts func) /\ ci.inst_id = loc /\ ci.inst_outputs = [croot] /\
  not_local_ptr ce ee.scopes croot /\ 32 <= capacity /\
  b+32 + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= b+capacity /\
  b+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= b+capacity``;

(* The copy is disjoint from old registered regions even if one of those
   regions is also a local. The fixed local regions are preserved by .8.2. *)
Theorem copy_rejoins_packing[local]:
  ^prepared_endpoint /\ ^prefix_at_prepared /\ ^copy_tail_post /\ ^buffer_sites /\
  fn_inst_ids_distinct func /\ ci_mono prepared ready /\ local_ptrs_reserved ce front /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
  ^ready_endpoint /\ ^prefix_at_ready /\ ^old_operands
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `alloca_inv p /\ local_ptrs_rel func ce ee.scopes p /\ alloca_inv z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
       (qspec_then `H0` (drule_then (assume_tac o cj 1))) >>
     qpat_assum `^restored_horizons` (qspec_then `H0` (drule_then (assume_tac o cj 1))) >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `b <= b+32 /\ mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo p.vs_memory /\
    (!j. j < lo /\ j IN tz.t_mem ==> j IN tp.t_mem)` by
    (qpat_assum `!q n. q+n <= lo \/ _ ==> mem_bytes_at q n z.vs_memory = _ /\ _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  qpat_x_assum `inst.inst_id = owner` (SUBST_ALL_TAC o SYM) >>
  drule_all ext_unwrap_protected_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `^old_operands` by
    (conj_tac >- (rpt gen_tac >> disch_tac >> first_x_assum irule >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  suspend "endpoint"
QED

Resume copy_rejoins_packing[endpoint]:
  `front.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `prepared.cs_next_var <= ready.cs_next_var /\ prepared.cs_next_id <= ready.cs_next_id` by fs[ci_mono_def] >>
  `window_alloca_growth s z` by
    (irule window_alloca_growth_trans >> qexists `p` >> asm_rewrite_tac[]) >>
  `local_ptrs_rel func ce ee.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `local_ptrs_reserved ce prepared` by metis_tac[local_ptrs_reserved_next_var] >>
  `!n q k. local_region ce ee.scopes s n q k <=> local_region ce ee.scopes p n q k` by
    metis_tac[local_region_wb_frame] >>
  `!n q k. local_region ce ee.scopes s n q k <=> local_region ce ee.scopes z n q k` by
    metis_tac[local_region_wb_frame] >>
  `pure_frame ce func ee front s z /\ wb_frame ce ee ee front s z` by
    (conj_tac
     >- (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`ee`,`prepared`,`p`] >> fs[wb_frame_def]) >>
     irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl [`ee`,`prepared`,`p`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce ee front G tn s Gz tz` by
    (irule ghost_kept_at_trans >> qexistsl [`Gp`,`ee`,`p`,`prepared`,`tp`] >>
     asm_rewrite_tac[] >> fs[wb_frame_def] >> metis_tac[]) >>
  `not_fresh_at ready root /\ not_fresh_at ready dst` by metis_tac[not_fresh_at_mono] >>
  `lookup_var root z = SOME (n2w b) /\ ptr_covers Gz tz root z capacity /\
   lookup_var dst z = SOME (n2w (b+32)) /\ ptr_covers Gz tz dst z (capacity-32)` by
    (qpat_assum `!x w n. not_fresh_at prepared x /\ _ ==> _` (fn th =>
       qspecl_then [`root`,`n2w b`,`capacity`] mp_tac th >>
       qspecl_then [`dst`,`n2w (b+32)`,`capacity-32`] mp_tac th) >>
     simp[eval_operand_def] >>
     qpat_assum `wb_frame ce ee ee prepared p z`
       (assume_tac o cj 1 o REWRITE_RULE[wb_frame_def]) >>
     conj_tac >> first_x_assum irule >> simp[]) >>
  `FLOOKUP Gz root = SOME (b,capacity)` by
    (qpat_assum `ghost_kept_at lo ce ee prepared Gp tp p Gz tz`
       (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at prepared x ==> FLOOKUP Gz x = _ /\ _`
       (qspec_then `root` mp_tac) >> simp[]) >>
  pure_once_rewrite_tac [ext_packing_endpoint_mods_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  suspend "protected"
QED

Resume copy_rejoins_packing[protected]:
  qx_gen_tac `q` >> qx_gen_tac `n` >> disch_tac >>
  qpat_assum `!b n. b+n <= lo \/ _ ==> mem_bytes_at b n p.vs_memory = _ /\ _`
    (qspecl_then [`q`,`n`] mp_tac) >>
  (impl_tac >- (qpat_assum `!n q k. local_region _ _ s n q k <=> local_region _ _ z n q k`
                  (pure_once_rewrite_tac o single) >>
                pop_assum mp_tac >> simp[AC ADD_ASSOC ADD_COMM])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at q n z.vs_memory = mem_bytes_at q n p.vs_memory /\
   (!j. q <= j /\ j < q+n /\ j IN tz.t_mem ==> j IN tp.t_mem)` suffices_by
    (strip_tac >> conj_tac >- metis_tac[] >> rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `q+n <= lo \/ _` strip_assume_tac
  >- (qpat_assum `!q n. q+n <= lo \/ (?aid a k. _ < prepared.cs_next_id /\ _) ==> _`
        (qspecl_then [`q`,`n`] mp_tac) >> simp[])
  >- (qpat_assum `!q n. q+n <= lo \/ (?nm b k. local_region _ _ p nm b k /\ _) \/ _ ==> _`
        (qspecl_then [`q`,`n`] mp_tac) >>
      (impl_tac >- (disj2_tac >> disj1_tac >>
        metis_tac[ADD_COMM])) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!q n. q+n <= lo \/ (?aid a k. _ < prepared.cs_next_id /\ _) ==> _`
    (qspecl_then [`q`,`n`] mp_tac) >>
  (impl_tac >- (disj2_tac >>
     qpat_assum `wb_frame ce ee ee front s p`
       (drule_then assume_tac o cj 1 o cj 2 o REWRITE_RULE[wb_frame_def]) >>
     qpat_assum `FLOOKUP p.vs_allocas _ = SOME (_,_)` (irule_at Any) >>
     decide_tac)) >>
  disch_then ACCEPT_TAC
QED

Finalise copy_rejoins_packing

val identity_saved = ``(?tag op. saved = StackValue tag op) \/
  (?vp. saved = LocatedValue ty vp /\ ~is_word_type ty /\ vp.ptr_location = LocMemory)``;

Theorem wb_frame_saved_operand[local]:
  wb_frame ce ee ee front s p /\ p.vs_labels = s.vs_labels /\
  (!x. op = Var x ==> not_fresh_at front x) /\ eval_operand op s = SOME w ==>
  eval_operand op p = SOME w
Proof
  Cases_on `op` >> simp[wb_frame_def,eval_operand_def]
QED

Theorem identity_original_interval[local]:
  ^packing_start /\ ^typed_saved /\ ^identity_saved /\ ^prepared_endpoint /\
  local_ptrs_reserved ce front ==>
  ?first last. last.cs_next_id <= owner /\
    expr_val_at ce cx ty first last ee v (vv_operand saved) p
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  drule_all ext_saved_row_input_mods >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w`,`at`,`bytes`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (fn th =>
      assume_tac (cj 1 (cj 2 th)) >>
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def] o cj 1) th))) >>
  qpat_assum `wb_frame ce ee ee front s p`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  `eval_operand (vv_operand saved) p = SOME w` by
    drule_all_then ACCEPT_TAC wb_frame_saved_operand >>
  `local_ptrs_rel func ce ee.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `vv_at ce cx ty si ss ee raw saved p` by
    (irule vv_at_alloc_map_frame >> qexistsl [`s`,`ss`] >>
     simp[] >> metis_tac[local_region_wb_frame]) >>
  qexistsl [`si`,`ss`] >> conj_tac >- decide_tac >>
  qpat_x_assum `^identity_saved` strip_assume_tac
  >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ _ p` mp_tac >>
      simp[vv_at_def,vv_operand_def]) >>
  simp[vv_operand_def] >> metis_tac[vv_at_memory_val_at]
QED

(* Keep the old ABI index and the already computed operands across unwrap.
   Identity keeps the snapshot interval; a copy owns its unwrap interval. *)
Theorem ext_restore_packing_row_mods:
  ^packing_start /\ ^typed_saved /\ ^prepared_endpoint /\ ^prefix_at_prepared /\
  ^buffer_sites /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce front /\
  return_buf_frame ret ce front s /\ storage_trace_domain cx st0 ee.storage_trace /\
  unwrap_value ce saved prepared = (src,ready) /\ fn_has_code prepared ready func ==>
  ?z Gz tz first last. ^ready_endpoint /\ ^prefix_at_ready /\ ^restored_src /\
    last.cs_next_id <= ready.cs_next_id /\
    (owner < first.cs_next_id \/ last.cs_next_id <= owner) /\
    local_ptrs_reserved ce ready /\ return_buf_frame ret ce ready z /\
    ^old_operands /\ ^ptr_path
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all prepare_saved_at_endpoint >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `^at_prepared` (qspec_then `H0` (drule_then (assume_tac o cj 1))) >>
  `return_buf_frame ret ce prepared p` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`front`] >>
     gvs[wb_frame_def,window_alloca_growth_def]) >>
  `ci_mono prepared ready` by
    (qspecl_then [`ce`,`saved`,`prepared`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `prepared.cs_next_id <= ready.cs_next_id /\ prepared.cs_next_var <= ready.cs_next_var` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved ce ready` by
    (irule local_ptrs_reserved_next_var >> qexists `front` >> simp[] >> decide_tac) >>
  Cases_on `^identity_saved`
  >- suspend "identity" >> suspend "copy"
QED

Resume ext_restore_packing_row_mods[identity]:
  drule_all ext_saved_row_identity_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all identity_original_interval >>
  disch_then (qx_choosel_then [`first`,`last`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`p`,`Gp`,`tp`,`first`,`last`] >>
  gvs[gas_origin_ptr_path_rules] >> decide_tac
QED

Resume ext_restore_packing_row_mods[copy]:
  `?vp. saved = LocatedValue ty vp /\ vp.ptr_location <> LocMemory` by
    (qhdtm_assum `abi_encode_saved_row_mods` (mp_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     metis_tac[]) >>
  drule_all restore_copy_at_prepared >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `^packing_start` (qspec_then `H0` (drule_then (assume_tac o cj 1 o cj 2))) >>
  drule_all copy_rejoins_packing >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?first last. first = prepared /\ last = ready /\ _` strip_assume_tac >>
  qexistsl [`z`,`Gz`,`tz`,`first`,`last`] >> simp[]
QED

Finalise ext_restore_packing_row_mods
