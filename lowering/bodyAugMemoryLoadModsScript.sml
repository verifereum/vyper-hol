(* Load the old word from the live memory place selected by AugAssign. *)
Theory bodyAugMemoryLoadMods
Ancestors
  bodyWriteTargetStageMods augAssignFullLoadMemoryStep bodySimAugPlaceLoad
  assignTuplePtrLoadStep exprPtrCtorImmStore nameLoweringProps stateRelProj
  exprSimProps exprSimUnwrap exprSimBuffer exprSimHypsDefs
  exprLoweringProps valueEncodingProps vyperState
  loweringShapeRules loweringPosts bodyFullShadowBodyInv bodyFullTargetDefs
  vyperTypeEnv vyperTypeInvariants vyperValueOperation vyperPlaceStatePreservation
  vyperStorageFootprint fragGasOriginPtr bodyPtrDefs ptrDiscipline
  venomInst venomState compileEnv finite_map words arithmetic

Theorem aug_memory_entry_type_mods[local]:
  expr_sim_inv_mods mods cenv cx env st /\
  lookup_scopes id st.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >>
  fs[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def,
     state_well_typed_def] >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  drule_all_then strip_assume_tac scope_well_typed_lookup_scopes >> simp[] >>
  `cenv.ce_var_type id = SOME ety` by
    (qpat_assum `!i t. _ ==> cenv.ce_var_type i = SOME t` irule >> simp[]) >>
  `ty = ety` by fs[] >> gvs[] >>
  qpat_assum `!i t e. _ ==> evaluate_type _ t = SOME e.type` irule >>
  qexists_tac `id` >> simp[]
QED

Theorem aug_memory_word_resources_mods[local]:
  stmt_state_rel H ctx func cenv cx st s /\
  ghost_inv_at_mods D lo d cenv cx st G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r G tn s /\
  eval_operand (FST r) s = SOME (b + n2w k) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\ lookup_scopes id st.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  evaluate_subscripts entry.type entry.value path = INL cur /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty ==>
  mload (w2n (b + n2w k)) s = typed_val_to_w256 ptv cur /\
  w2n (b + n2w k) + 32 <= s.vs_alloca_next /\
  (!j. w2n (b + n2w k) <= j /\ j < w2n (b + n2w k) + 32 ==> j NOTIN tn.t_mem) /\
  (!iid out. ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid MLOAD [FST r] [out]) s)
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  gvs[eval_operand_def] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `type_memory_size ptv = 32` by metis_tac[word_tv_memory_size] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  `value_has_type ptv cur` by metis_tac[evaluate_subscripts_type] >>
  `ptr_covers G tn p s sz /\ allocas_from lo s /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory entry.type entry.value (w2n b) mem)` by
    (fs[ghost_inv_at_mods_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory ptv cur (w2n b + k) mem` by
    (rpt strip_tac >> irule aug_place_path_project >>
     qexistsl_tac [`entry.value`,`path`,`entry.type`] >> simp[]) >>
  drule_all_then strip_assume_tac robust_typed_word_clean >>
  simp[] >> conj_tac
  >- (qpat_assum `!m. _ ==> mem_word_at _ _ = _`
        (qspec_then `s.vs_memory` mp_tac) >>
      simp[mem_agree_outside_def, mem_word_at_eq_mload] >>
      (metis_tac[mem_agree_outside_def, mem_word_at_eq_mload, ADD_COMM])) >>
  `?q. FST r = Var q /\ ptr_covers G tn q s 32` by suspend "access" >>
  gvs[] >> metis_tac[ptr_inst_ok_mload_lo]
QED

Resume aug_memory_word_resources_mods[access]:
  fs[target_ptr_ok_def, ptr_covers_def] >>
  Cases_on `FST r` >> gvs[op_prov_def, eval_operand_def] >>
  qexists_tac `b + n2w k` >> simp[] >> decide_tac
QED

Finalise aug_memory_word_resources_mods

Theorem augassign_memory_load_mods:
  expr_sim_inv_mods mods cenv cx env st /\ is_word_type ty /\
  storage_trace_domain cx st0 st.storage_trace /\
  (?entry cur. lookup_scopes id st.scopes = SOME entry /\
               evaluate_subscripts entry.type entry.value path = INL cur) /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt
      es sa sb s0 st (PlaceR (MemoryPlace id path)) (Type ty) r G0 tn0 G tn s) /\
  emit_op MLOAD [FST r] sb = (old,sc) /\ fn_has_code sb sc func ==>
  ?addr cur ptv u G1 tn1.
    FST (SND r) = SOME LocMemory /\ eval_operand (FST r) s = SOME addr /\
    read_place cx (MemoryPlace id path) st = (INL cur,st) /\
    place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
    (!H. valid_horizon cx st0 H st.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1)) /\
    eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
    eval_operand (FST r) u = SOME addr /\
    op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
    (!q. old = Var q ==> not_fresh_at sc q) /\
    (!q. FST r = Var q ==> not_fresh_at sc q) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
          FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_assum (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[write_target_location_mods_def, place_ptr_rel_def] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac aug_memory_entry_type_mods >> gvs[] >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `value_has_type tv cur` by metis_tac[evaluate_subscripts_type] >>
  `read_place cx (MemoryPlace id path) st = (INL cur,st) /\
   place_type_value cx (MemoryPlace id path) st = (INL tv,st)` by
    simp[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
         lift_sum_def, return_def, read_memory_path_def, place_type_value_def] >>
  drule_all_then strip_assume_tac aug_memory_word_resources_mods >>
  drule_then strip_assume_tac emit_op_facts >>
  `!q. FST r = Var q ==> not_fresh_at sc q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD] >>
  qabbrev_tac `x = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sb.cs_next_id MLOAD [FST r] [x]` >>
  qabbrev_tac `raw = update_var x (mload (w2n (b + n2w k)) s) s` >>
  qexistsl_tac [`cur`,`raw with vs_inst_idx := SUC s.vs_inst_idx`,
                `step_prov PG G i raw`,`step_taint i s raw tn`] >>
  simp[] >>
  qpat_assum `mload _ _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (rpt strip_tac >> qpat_assum `!K. valid_horizon _ _ K _ ==> _`
       (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
     drule_all_then strip_assume_tac aug_memory_word_resources_mods >> simp[Abbr `i`]) >>
  mp_tac (BETA_RULE (Q.ISPEC `\H. valid_horizon cx st0 H st.storage_trace`
     augassign_mload_joint_step)) >>
  disch_then (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  simp[Abbr `x`,Abbr `i`,Abbr `raw`] >>
  disch_then (qspecl_then [`DF`,`lo`,`explicit`,`ctx`,`func`,`PG`,
                           `b + n2w k`,`s`,`G`,`tn`] mp_tac) >> simp[]
QED
