(* Physical and linked frame transport at the actual tuple-operand unwrap. *)
Theory bodyAbiTupleUnwrapLiftMods
Ancestors
  bodyAbiTupleBufferStateMods abiEncoderWindowContract abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic exprSimStorageCopy
  exprLoweringProps venomExecSemantics venomState venomInst finite_map
  wordArgsPtr exprSimWordArgs stateRelProj exprSimSubscriptArrayFrame
  decoderGhostFramePtr exprOperandVar loweringStateRelDefs
  venomMemDefs[qualified] memoryReadProps compileEnv loweringPosts
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullPathHistory fragGasOriginPtr
  bodyPtrDefs ptrDiscipline allocaHistory
  words list arithmetic pred_set
Libs horizonTypeLib

Theorem unwrap_alloca_copy_physical[local]:
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit szw] /\ inst.inst_outputs = [out] /\
  exec_alloca inst u szw = OK mid /\ copy_static z = copy_static mid /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory) /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory ==>
  window_alloca_growth u z /\
  abi_encoder_registered_effect {inst.inst_id} [] u z /\
  abi_encode_exec_frame func u z
Proof
  strip_tac >>
  drule_all_then assume_tac window_exec_alloca_growth >>
  drule_all_then assume_tac window_exec_alloca_effect >>
  drule_all_then assume_tac exec_alloca_static_charge >>
  qpat_x_assum `copy_static z = copy_static mid`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [copy_static_def, venom_state_component_equality]) >>
  conj_tac >-
    (qpat_x_assum `window_alloca_growth u mid` mp_tac >>
     simp_tac bool_ss [window_alloca_growth_def] >>
     disch_then strip_assume_tac >> gvs[] >> metis_tac[]) >>
  `z.vs_fmp = u.vs_fmp /\ z.vs_call_ctx = u.vs_call_ctx /\
   z.vs_data_section = u.vs_data_section /\
   abi_encode_semantic_obs z = abi_encode_semantic_obs u` by
    (qpat_x_assum `exec_alloca inst u szw = OK mid` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs(), update_var_def,
          abi_encode_semantic_obs_fields] >> rw[] >> fs[]) >>
  reverse conj_tac >-
    (`pending_alloca_size func z = pending_alloca_size func mid` by
       simp[pending_alloca_size_def] >>
     simp[abi_encode_exec_frame_def] >> decide_tac) >>
  qpat_x_assum `abi_encoder_registered_effect _ [] u mid` mp_tac >>
  simp[abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem unwrap_registered_bytes[local]:
  abi_encoder_registered_effect {aid} [] u z /\
  FLOOKUP z.vs_allocas aid = SOME (b,n) /\
  (p+k <= b \/ b+n <= p) ==>
  mem_bytes_at p k z.vs_memory = mem_bytes_at p k u.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_bytes >>
  qexistsl [`{aid}`,`[]`] >> simp[venomMemDefsTheory.regions_disjoint_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem unwrap_other_alloc[local]:
  venomMemDefs$alloca_inv z /\ aid <> sid /\
  FLOOKUP z.vs_allocas aid = SOME (p,k) /\ FLOOKUP z.vs_allocas sid = SOME (b,n) ==>
  p+k <= b \/ b+n <= p
Proof
  simp_tac bool_ss [venomMemDefsTheory.alloca_inv_def,
                   venomMemDefsTheory.allocas_non_overlapping_def] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem unwrap_anchored_intervals[local]:
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_reserved ce se /\
  wb_frame ce ee ee se s u /\ lo <= b /\ se.cs_next_id <= sid /\
  venomMemDefs$alloca_inv z /\ FLOOKUP z.vs_allocas sid = SOME (b,n) /\
  abi_encoder_registered_effect {sid} [] u z /\
  (!name p k. local_region ce ee.scopes u name p k ==> p+k <= b \/ b+n <= p) /\
  (!i. i < b \/ b+n <= i ==> i IN tz.t_mem ==> i IN tu.t_mem) /\
  (!p k. ((p = 0 /\ k = lo) \/
          (?name. local_region ce ee.scopes s name p k) \/
          (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k))) ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory /\
    (!i. p <= i /\ i < p+k /\ i IN tu.t_mem ==> i IN tn.t_mem)) ==>
  !p k. ((p = 0 /\ k = lo) \/
         (?name. local_region ce ee.scopes s name p k) \/
         (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k))) ==>
    mem_bytes_at p k z.vs_memory = mem_bytes_at p k s.vs_memory /\
    (!i. p <= i /\ i < p+k /\ i IN tz.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!name p k. local_region ce ee.scopes s name p k ==>
     local_region ce ee.scopes u name p k` by
    (rpt strip_tac >> drule_all_then (fn th => simp[th]) local_region_wb_frame) >>
  `!aid v. FLOOKUP s.vs_allocas aid = SOME v ==> FLOOKUP u.vs_allocas aid = SOME v` by
    fs[wb_frame_def] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!p k. _ ==> mem_bytes_at p k u.vs_memory = _ /\ _`
    (qspecl_then [`p`,`k`] (drule_then strip_assume_tac)) >>
  `p+k <= b \/ b+n <= p` suffices_by
    (disch_tac >> drule_all_then assume_tac unwrap_registered_bytes >>
     simp[] >> rpt strip_tac >>
     `i IN tu.t_mem` by
       (qpat_assum `!j. j < b \/ b+n <= j ==> _`
          (qspec_then `i` irule) >> simp[] >> decide_tac) >>
     qpat_assum `!j. p <= j /\ j < p+k /\ j IN tu.t_mem ==> _`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  (qpat_x_assum `(p = 0 /\ k = lo) \/ _` strip_assume_tac
     >- (gvs[] >> decide_tac)
     >- (qpat_assum `!nm p k. local_region _ _ s nm p k ==> _`
           (drule_then assume_tac) >>
         qpat_assum `!nm p k. local_region _ _ u nm p k ==> _`
           (drule_then ACCEPT_TAC)) >>
     `aid <> sid` by decide_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (p,k)` by metis_tac[] >>
     drule_all_then assume_tac abi_encoder_registered_effect_allocated >>
   irule unwrap_other_alloc >> qexistsl [`aid`,`sid`,`z`] >> simp[])
QED

Theorem unwrap_saved_prefix[local]:
  abi_encoder_registered_effect {sid} [] u z /\ venomMemDefs$alloca_inv z /\
  FLOOKUP z.vs_allocas sid = SOME (b,n) /\ shared <> sid /\
  FLOOKUP u.vs_allocas shared = SOME (pbase,capacity) /\
  LENGTH prefix <= dst_offset /\ dst_offset <= capacity /\
  read_memory (pbase+dst_offset-LENGTH prefix) (LENGTH prefix) u = prefix /\
  (!i. pbase+dst_offset-LENGTH prefix <= i /\ i < pbase+dst_offset ==> i NOTIN tu.t_mem) /\
  (!i. i < b \/ b+n <= i ==> i IN tz.t_mem ==> i IN tu.t_mem) ==>
  FLOOKUP z.vs_allocas shared = SOME (pbase,capacity) /\
  read_memory (pbase+dst_offset-LENGTH prefix) (LENGTH prefix) z = prefix /\
  (!i. pbase+dst_offset-LENGTH prefix <= i /\ i < pbase+dst_offset ==> i NOTIN tz.t_mem)
Proof
  strip_tac >> drule_all_then assume_tac abi_encoder_registered_effect_allocated >>
  `pbase+capacity <= b \/ b+n <= pbase` by
    (irule unwrap_other_alloc >> qexistsl [`shared`,`sid`,`z`] >> simp[]) >>
  `pbase+dst_offset-LENGTH prefix+LENGTH prefix <= b \/
   b+n <= pbase+dst_offset-LENGTH prefix` suffices_by
    (disch_tac >> drule_all_then assume_tac unwrap_registered_bytes >>
     fs[read_memory_eq_mem_bytes_at] >> rpt strip_tac >>
     `i IN tu.t_mem` by
       (qpat_assum `!j. j < b \/ b+n <= j ==> _`
          (qspec_then `i` irule) >> simp[] >> decide_tac) >>
     qpat_assum `!j. _ /\ _ ==> j NOTIN tu.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  decide_tac
QED

(* The saved anchor is not the unwrap entry. Both restore frames start
   at ready, and are composed with the incoming anchor relations. *)
Theorem abi_tuple_unwrap_lift_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix ready u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ ci_mono ready c /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = ready.cs_next_id /\ ready.cs_next_id < c.cs_next_id /\
  inst.inst_operands = [Lit szw] /\ inst.inst_outputs = [out] /\
  not_local_ptr ce ee.scopes out /\ (cursor_site = ready.cs_next_id ==> n = 32) /\
  exec_alloca inst u szw = OK mid /\ copy_static z = copy_static mid /\
  FLOOKUP z.vs_allocas ready.cs_next_id = SOME (b,n) /\ lo <= b /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory) /\
  (!i. i < b \/ b+n <= i ==> i IN tz.t_mem ==> i IN tu.t_mem) /\
  (!name p k. local_region ce ee.scopes u name p k ==> p+k <= b \/ b+n <= p) /\
  (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x u /\
     FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
  tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz) /\
  ~z.vs_halted /\ z.vs_current_bb = c.cs_current_bb /\
  z.vs_inst_idx = LENGTH c.cs_current_insts /\ return_buf_frame d ce c z /\
  wb_frame ce ee ee ready u z /\ ghost_kept_at lo ce ee ready Gu tu u Gz tz /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c z Gz tz /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    ready u Gu tu c z Gz tz
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n)` by simp[] >>
  drule_all_then strip_assume_tac unwrap_alloca_copy_physical >>
  qpat_x_assum `abi_encoder_registered_effect {inst.inst_id} [] u z` mp_tac >>
  simp[] >> disch_tac >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
  `shared <> ready.cs_next_id` by decide_tac >>
  reverse conj_tac >-
    (PURE_REWRITE_TAC[abi_tuple_row_effects_mods_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >-
       (rpt gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
     qexistsl [`{ready.cs_next_id}`,`[]`] >> simp[] >>
     conj_tac >- (qexistsl [`inst`,`out`] >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> i IN tz.t_mem ==> _`
       (qspec_then `i` irule) >> simp[]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace /\ _`
    (qx_choose_then `hz` strip_assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  `venomMemDefs$alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `venomMemDefs$alloca_inv z` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee z`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `se.cs_next_id <= ready.cs_next_id` by decide_tac >>
  drule_all_then strip_assume_tac unwrap_saved_prefix >>
  `wb_frame ce ee ee se s z` by
    (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee ready u z` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gz tz` by
    (irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee ready Gu tu u Gz tz` (irule_at Any) >>
     simp[] >> qexists `ee` >> simp[]) >>
  `!x w k. not_fresh_at ready x /\ eval_operand (Var x) u = SOME w /\ ptr_covers Gu tu x u k ==>
     not_fresh_at c x /\ eval_operand (Var x) z = SOME w /\ ptr_covers Gz tz x z k` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at ready x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[eval_operand_def] >> metis_tac[compiler_ci_mono_not_fresh,ptr_covers_frame]) >>
  `ready.cs_next_var <= c.cs_next_var /\ ready.cs_next_id <= c.cs_next_id` by fs[ci_mono_def] >>
  `s.vs_alloca_next <= z.vs_alloca_next` by fs[window_alloca_growth_def] >>
  qhdtm_x_assum `abi_encode_exec_frame` (strip_assume_tac o REWRITE_RULE[abi_encode_exec_frame_def]) >>
  qpat_assum `abi_encoder_registered_effect _ [] u z`
    (strip_assume_tac o REWRITE_RULE[abi_encoder_registered_effect_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `not_fresh_at c root /\ eval_operand (Var root) z = SOME (n2w pbase) /\
    ptr_covers Gz tz root z capacity` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `not_fresh_at c dst /\ eval_operand (Var dst) z = SOME (n2w (pbase+dst_offset)) /\
    ptr_covers Gz tz dst z (capacity-dst_offset)` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  PURE_REWRITE_TAC[abi_tuple_buffer_state_mods_def] >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  rpt gen_tac >> disch_tac >>
  irule (horizonTypeLib.at_horizon_named "H" unwrap_anchored_intervals) >>
  qpat_assum `abi_encoder_registered_effect {ready.cs_next_id} [] u z` (irule_at Any) >>
  qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
  qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas ready.cs_next_id = SOME (b,n)` (irule_at Any) >>
  qexistsl [`tu`,`lo`] >> asm_rewrite_tac[]
QED

(* A StackValue, or the already-memory nonword case, has the same cut on
   both sides of unwrap. No allocation or output slice is registered. *)
Theorem abi_tuple_unwrap_identity_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu a u Gu tu
Proof
  simp[abi_tuple_row_effects_mods_def, ci_mono_refl, window_alloca_growth_refl] >>
  disch_tac >> qexistsl [`{}`,`[]`] >> simp[abi_encoder_registered_effect_refl]
QED
