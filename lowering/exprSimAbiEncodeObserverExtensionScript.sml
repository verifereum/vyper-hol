Theory exprSimAbiEncodeObserverExtension
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodePhaseExtension exprSimAbiEncodeStagedObserver
  exprSimVVFrame abiDecoderReentry freshWrites varsExt exprSimProps
  loweringPosts compileEnv localPtrsProps finite_map pred_set arithmetic
  exprSimAbiEncodeSemantic venomState emitHelperProps abiDecoderContract
  abiBuiltinAllocation abiEncoderWindowContract venomMemDefs exprLoweringProps
  exprSimAbiEncodeExecFrame exprSimAbiEncodeWindowRoom exprSimAbiEncodeObservationExtension

Theorem abi_encode_observer_local_region_clean[local]:
  local_ptrs_reserved ce st ==>
  (local_region ce scopes (drop_fresh st s) n b sz <=>
   local_region ce scopes s n b sz)
Proof
  strip_tac >> simp[local_region_def] >>
  eq_tac >> rpt strip_tac >> goal_assum (drule_at Any) >>
  fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_drop_fresh]
QED

Theorem abi_encode_staged_observation_clean_initial:
  local_ptrs_reserved ce st ==>
  (abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av
     (drop_fresh st initial) actual <=>
   abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av
     initial actual)
Proof
  strip_tac >>
  simp[abi_encode_staged_observation_def, abi_encode_observer_local_region_clean,
       abi_encode_semantic_obs_def, drop_fresh_def, lookup_var_def,
       FLOOKUP_DRESTRICT] >>
  metis_tac[not_fresh_at_def]
QED

Theorem abi_encode_observer_allocate_vars[local]:
  abi_builtin_allocate_state site n (s with vs_vars := vars) =
    (abi_builtin_allocate_state site n s) with vs_vars := vars
Proof
  simp[abi_builtin_allocate_state_def] >> IF_CASES_TAC >>
  simp[venom_state_component_equality]
QED

Theorem abi_encode_observer_alloca_vars[local]:
  (alloca_inv (s with vs_vars := vars) <=> alloca_inv s) /\
  (alloca_room ctx fn (s with vs_vars := vars) <=> alloca_room ctx fn s)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_room_def, pending_alloca_size_def]
QED

Theorem abi_encode_staged_observer_no_fresh:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room (ctx with ctx_functions := [obs]) obs
    (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  stmt_state_rel ctx func ce cx vs initial /\ local_ptrs_reserved ce st /\
  fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
  32+w <= outsz /\ p <= d /\ d+LENGTH (enc at av) <= p+outsz ==>
  ?actual.
    abi_decode_sim ctx obs initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame obs initial actual /\
    abi_encode_staged_observation ctx func ce cx vs st (FST ops) method_id
      outsz p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt limit_st (drop_fresh st initial)` by
    (irule fresh_vars_wrt_mono >> qexists_tac `st` >>
     rewrite_tac[fresh_vars_wrt_drop_fresh] >> decide_tac) >>
  `eval_operand src (drop_fresh st initial) = SOME (n2w sb)` by
    (`!x. src = Var x ==> not_fresh_at st x` by
       (qpat_assum `abi_decoder_operand_live st.cs_next_var src` mp_tac >>
        Cases_on `src` >> simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
                            not_fresh_at_def, IN_DEF]) >>
     drule eval_operand_drop_fresh >>
     disch_then (qspec_then `initial` (fn th => rewrite_tac [th])) >>
     first_assum ACCEPT_TAC) >>
  `?u. abi_decode_sim ctx obs (drop_fresh st initial) u /\
    ~u.vs_halted /\ u.vs_current_bb = final.cs_current_bb /\
    u.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame obs (drop_fresh st initial) u /\
    abi_encode_staged_observation ctx func ce cx vs st (FST ops) method_id
      outsz p at av (drop_fresh st initial) u /\
    abi_encoder_extend_sim (ctx with ctx_functions := [obs]) obs (drop_fresh st initial) u` by
    (irule abi_encode_staged_observer_extend >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_finish _ _ _ _ = _` (irule_at Any) >>
     qexistsl [`w`, `sb`, `limit_st`, `d`, `cap`] >>
     simp_tac (srw_ss()) [drop_fresh_def, abi_encode_observer_allocate_vars,
                         abi_encode_observer_alloca_vars] >>
     rewrite_tac[GSYM drop_fresh_def] >>
     asm_rewrite_tac [] >> drule stmt_state_rel_drop_fresh >>
     disch_then (qspecl_then [`func`, `cx`, `vs`, `initial`, `ctx`] mp_tac) >>
     asm_rewrite_tac []) >>
  `abi_encode_staged_observation ctx func ce cx vs st (FST ops) method_id
      outsz p at av initial u` by
    (drule abi_encode_staged_observation_clean_initial >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `abi_encode_exec_frame obs initial u` by
    (qpat_assum `abi_encode_exec_frame _ (drop_fresh _ _) _` mp_tac >>
     simp_tac (srw_ss()) [abi_encode_exec_frame_def, drop_fresh_def,
                         pending_alloca_size_def, abi_encode_semantic_obs_def]) >>
  drule_all abi_encode_lift_clean_observation >> strip_tac >>
  `abi_decode_sim ctx obs initial v` by
    (drule_all abi_decode_sim_ctx_no_invoke >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts` by
    (drule abi_encode_bounded_vars_ext >>
     simp_tac bool_ss [vars_ext_def] >> strip_tac >>
     qpat_x_assum `v = u with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `v` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
