(* Storage and transient arrays save places, not the values read from them. *)
Theory bodyForArraySlotLengthMods
Ancestors
  bodyForArrayRouteMods bodyForArrayHeaderMods bodyForRangeScalarFrameMods
  bodyPtrSignedConvertSourceFrame reasonEndpointResourcesPtr bodyFullIfExpReach
  bodyBinopFragMemory stmtReasonLitFragMemory typedMemoryCopy
  exprSimSource exprSimCopy bodyMemoryDefs exprSimHypsDefs vyperTypeInvariants
  vyperStorageFootprint stmtSimAppendStorageCompose vyperState vyperAST words list
  bodyFullPostsMods exprLowering exprLoweringProps compileEnv
  fragGasOriginPtr loweringShapeRules venomState venomInst rich_list ptrDiscipline
  bodyPtrDefs exprSimDefs loweringStateRelDefs context loweringPosts
  bodyForRangeHeaderMods bodySimFull bodyFullShadowBodyInv stmtSimDefs
  vyperStorageTrace vyperTypeSystem freshWrites stmtLoweringMono
  stmtSimAugAssignPlaceStorage venomExecSemantics unitTransformDefs contextRawReachable
  allocaHistory
Libs
  monadsyntax

val _ = Parse.hide "Gt";

Theorem slot_capture_source[local]:
  expr_body_pre_mods mods c cx env e es /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),em with gas_obs := tail)) /\
  valid_horizon cx st0 H em.storage_trace /\
  storage_well_formed_on cx es (FST H) /\
  storage_well_formed_on cx em (FST H) /\
  len = (case bd of Fixed cnt => cnt | Dynamic _ =>
    w2n (lookup_storage slot (get_storage cx em tr))) /\
  bound_length bd <= n ==>
  ?vs off root path delta.
    vs = GENLIST (\i. PlaceR (StoragePlace tr
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
       n2w (i * type_slot_size et)) et)) len /\
    LENGTH vs = len /\ compatible_bound bd len /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    MEM (StorageRoot tr off root) em.storage_trace /\
    storage_subregion root path delta (ArrayTV et bd) /\
    slot = n2w off + n2w delta
Proof
  strip_tac >>
  `expr_body_pre_mods mods c cx env e (es with gas_obs := prefix)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ _ es` mp_tac >>
     rewrite_tac[expr_body_pre_mods_def,expr_sim_inv_mods_def,env_consistent_def,
                 env_scopes_consistent_def,env_immutables_consistent_def,
                 state_well_typed_def] >>
     CONV_TAC (RATOR_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [])) THENC
               RAND_CONV (SIMP_CONV (srw_ss()) [])) >>
     disch_then ACCEPT_TAC) >>
  `storage_well_formed_on cx (es with gas_obs := prefix) (FST H) /\
   storage_well_formed_on cx (em with gas_obs := []) (FST H)` by
    fs[storage_well_formed_on_def,get_storage_gas_obs] >>
  `eval_expr cx e (es with gas_obs := prefix) =
    (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),em with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H (em with gas_obs := []).storage_trace` by simp[] >>
  `len = (case bd of Fixed cnt => cnt | Dynamic _ =>
    w2n (lookup_storage slot (get_storage cx (em with gas_obs := []) tr)))` by
    simp[get_storage_gas_obs] >>
  drule_all_then strip_assume_tac for_array_storage_capture_mods >>
  qexistsl [`vs`,`off`,`root`,`path`,`delta`] >> simp[] >> gvs[]
QED

(* Only the dynamic cut writes a register. In both cuts the allocation
   history is at the actual cursor, not copied from the previous cursor. *)
Theorem slot_length_run[local]:
  vv_post_mods H ctx func c cx e es sa sb s0 em
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv u /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv em Gu tu u /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
  ~is_word_type (post_value_type c e) /\
  len = (case bd of Fixed cnt => cnt | Dynamic _ =>
    w2n (lookup_storage slot (get_storage cx em tr))) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                      (vv_operand vv)) sb = (len_op,saL) /\
  fn_has_code sb saL func /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  loc = slot_loc tr /\ eval_operand (vv_operand vv) u = SOME slot /\
  op_taint tu (vv_operand vv) = {} /\
  ?t Gt tt.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = saL.cs_current_bb /\
    t.vs_inst_idx = LENGTH saL.cs_current_insts /\ alloca_history func t /\
    eval_operand len_op t = SOME (n2w len) /\
    op_taint tt len_op = {} /\ op_prov Gt len_op = NONE /\
    (!x. len_op = Var x ==> not_fresh_at saL x) /\ sb.cs_next_var <= saL.cs_next_var /\
    t = u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gt x = FLOOKUP Gu x /\ op_taint tt (Var x) = op_taint tu (Var x)) /\
    tt.t_mem = tu.t_mem /\ tt.t_stor = tu.t_stor /\
    tt.t_trans = tu.t_trans /\ tt.t_imm = tu.t_imm
Proof
  strip_tac >> drule_all_then strip_assume_tac for_array_slot_operand_mods >>
  `loc = slot_loc tr` by gvs[vv_location_def] >>
  simp[vv_operand_def] >>
  Cases_on `bd`
  >- (gvs[comp_return_def] >> qexistsl [`u`,`Gu`,`tu`] >>
      simp[gas_origin_ptr_path_rules,eval_operand_def,op_taint_def,op_prov_def]) >>
  qpat_x_assum `loc = (case _ of NONE => _ | SOME l => l)` kall_tac >>
  fs[] >> drule_all for_array_storage_dynamic_length_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sb = (Var out,saL)` by
    (Cases_on `tr` >> gvs[compile_ptr_load_def,slot_loc_def,vv_operand_def]) >>
  drule_then strip_assume_tac emit_op_facts >> fs[] >>
  qpat_x_assum `out = out'` (SUBST_ALL_TAC o SYM) >>
  qexistsl [`t`,`G1`,`tn1`] >>
  `alloca_history func t` by
    (drule_all_then strip_assume_tac fn_has_code_code >>
     qpat_x_assum `isPREFIX _ _`
       (qx_choose_then `rest` assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     `t with vs_inst_idx := u.vs_inst_idx + LENGTH
        [mk_inst sb.cs_next_id (if tr then TLOAD else SLOAD) [p.ptr_operand] [out]] = t` by
       simp[venom_state_component_equality] >>
     pop_assum (SUBST1_TAC o SYM) >> irule alloca_history_no_alloca_slice >>
     simp[mk_inst_def,update_var_def] >> Cases_on `tr` >> simp[]) >>
  `!x. not_fresh_at sb x ==> x <> out` by
    (rpt strip_tac >> gvs[]) >>
  qpat_x_assum `len_op = Var _` SUBST_ALL_TAC >>
  simp[eval_operand_def,update_var_def,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[arithmeticTheory.ADD1] >>
  rpt strip_tac >> `x <> out` by (strip_tac >> gvs[]) >>
  qpat_assum `!x. x <> out ==> _` drule >> simp[]
QED

Theorem slot_length_linked_frame[local]:
  local_ptrs_reserved c sb /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  t = u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x u /\
    FLOOKUP Gt x = FLOOKUP Gu x /\ op_taint tt (Var x) = op_taint tu (Var x)) /\
  tt.t_mem = tu.t_mem /\ tt.t_stor = tu.t_stor /\ tt.t_trans = tu.t_trans /\ tt.t_imm = tu.t_imm /\
  alloca_history func t /\
  stmt_state_rel H ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
  ghost_inv_at_mods D lo d c cx em Gu tu u /\
  for_array_outer_frame_mods ctx func c sa es s0 G0 tn0 em Gu tu u /\
  ret_pc_ok c sa u /\ return_buf_frame d c sa u /\ return_buf_sep d c em u ==>
  stmt_state_rel H ctx func c cx em t /\ immutable_frame_mods func c cx em t /\
  ghost_inv_at_mods D lo d c cx em Gt tt t /\
  for_array_outer_frame_mods ctx func c sa es s0 G0 tn0 em Gt tt t /\
  ret_pc_ok c sa t /\ return_buf_frame d c sa t /\ return_buf_sep d c em t /\
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >>
  `t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
   t.vs_alloca_next = u.vs_alloca_next /\ t.vs_data_section = u.vs_data_section /\
   t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_immutables = u.vs_immutables /\
   t.vs_initial_fmp = u.vs_initial_fmp /\ t.vs_fmp = u.vs_fmp` by
    (rpt conj_tac >> qpat_assum `t = _` (fn th => simp[Once th])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u /\
     FLOOKUP Gt x = FLOOKUP Gu x /\ op_taint tt (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!nm b sz. local_region c em.scopes t nm b sz <=> local_region c em.scopes u nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sb` >> simp[]) >>
  `stmt_state_rel H ctx func c cx em t` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`u`,`sb`] >> simp[]) >>
  `immutable_frame_mods func c cx em t` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`em`,`u`,`sb`] >> simp[]) >>
  `ghost_inv_at_mods D lo d c cx em Gt tt t` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`Gu`,`em`,`u`,`sb`,`tu`] >> simp[]) >>
  simp[] >> conj_tac
  >- (fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def,
         alloca_frame_def,allocas_below_fmp_def] >>
      rpt conj_tac >-
        (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _` drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- fs[ret_pc_ok_def] >>
  conj_tac >-
    (irule return_buf_frame_frame >> qexistsl [`c`,`u`,`sa`] >> simp[]) >>
  conj_tac >- (Cases_on `d` >> simp[return_buf_sep_def] >>
               PairCases_on `x` >> fs[return_buf_sep_def,allocas_from_def] >>
               conj_tac >> first_assum ACCEPT_TAC) >>
  fs[ghost_inv_at_mods_def]
QED

Theorem slot_old_operand[local]:
  copy_old_operand sa op /\ t.vs_labels = u.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u /\
    FLOOKUP Gt x = FLOOKUP Gu x /\ op_taint tt (Var x) = op_taint tu (Var x)) ==>
  eval_operand op t = eval_operand op u /\ op_prov Gt op = op_prov Gu op /\
  op_taint tt op = op_taint tu op
Proof
  Cases_on `op` >> simp[copy_old_operand_def,eval_operand_def,op_prov_def,op_taint_def]
  >> strip_tac >> first_x_assum drule >> simp[op_taint_def]
QED

(* The witnesses are chosen once, before transport to arbitrary horizons
   or to the endpoint of the fresh item allocation. *)
Theorem for_array_slot_length_ready_mods:
  expr_body_pre_mods mods c cx env e es /\
  post_value_type c e = ArrayT elem bd /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
  bound_length bd <= n /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    storage_well_formed_on cx es (FST H) /\
    vv_post_mods H ctx func c cx e es sa sb s0 em
      (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv u /\
    ghost_inv_at_mods (DF H) lo d c cx em Gu tu u) /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv em Gu tu u /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\ local_ptrs_reserved c sa /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                      (vv_operand vv)) sb = (len_op,saL) /\
  fn_has_code sb saL func /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  for_array_outer_frame_mods ctx func c sa es s0 G0 tn0 em Gu tu u /\
  ret_pc_ok c sa u /\ return_buf_frame d c sa u /\ return_buf_sep d c em u /\
  (!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = (0:num)) /\
  (!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q) ==>
  loc = slot_loc tr /\
  ?len vs off root path delta t Gt tt.
    len = (case bd of Fixed cnt => cnt | Dynamic _ =>
      w2n (lookup_storage slot (get_storage cx em tr))) /\
    vs = GENLIST (\i. PlaceR (StoragePlace tr
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
       n2w (i * type_slot_size et)) et)) len /\
    LENGTH vs = len /\ len < dimword (:256) /\ compatible_bound bd len /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    MEM (StorageRoot tr off root) em.storage_trace /\
    storage_subregion root path delta (ArrayTV et bd) /\
    slot = n2w off + n2w delta /\
    (!tail. array_iterator_results cx (expr_type e)
      (PlaceR (StoragePlace tr slot (ArrayTV et bd))) (em with gas_obs := tail) =
      (INL vs,em with gas_obs := tail)) /\
    ~t.vs_halted /\ t.vs_current_bb = saL.cs_current_bb /\
    t.vs_inst_idx = LENGTH saL.cs_current_insts /\
    (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q) /\
    for_array_capture_frame_mods c (em,sb,saL,t,tt) em tt t /\
    eval_operand (vv_operand vv) t = SOME slot /\ op_taint tt (vv_operand vv) = {} /\
    eval_operand len_op t = SOME (n2w len) /\ op_taint tt len_op = {} /\ op_prov Gt len_op = NONE /\
    (!z Gz tz.
      z.vs_labels = t.vs_labels /\
      (!x. not_fresh_at saL x ==> lookup_var x z = lookup_var x t /\
        FLOOKUP Gz x = FLOOKUP Gt x /\ op_taint tz (Var x) = op_taint tt (Var x)) ==>
      eval_operand (vv_operand vv) z = SOME slot /\ op_taint tz (vv_operand vv) = {} /\
      eval_operand len_op z = SOME (n2w len) /\ op_taint tz len_op = {} /\ op_prov Gz len_op = NONE) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt) /\
      storage_place_observed H (StoragePlace tr slot (ArrayTV et bd)) /\
      stmt_state_rel H ctx func c cx em t /\ immutable_frame_mods func c cx em t /\
      storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods (DF H) lo d c cx em Gt tt t /\
      for_array_outer_frame_mods ctx func c sa es s0 G0 tn0 em Gt tt t /\
      ret_pc_ok c sa t /\ return_buf_frame d c sa t /\ return_buf_sep d c em t /\
      allocas_from lo t /\ lo <= t.vs_alloca_next)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `storage_well_formed_on cx em (FST H0)` by fs[vv_post_mods_def] >>
  qabbrev_tac `len = case bd of Fixed cnt => cnt | Dynamic _ =>
    w2n (lookup_storage slot (get_storage cx em tr))` >>
  `len = (case bd of Fixed cnt => cnt | Dynamic _ =>
    w2n (lookup_storage slot (get_storage cx em tr)))` by simp[Abbr `len`] >>
  drule_all_then strip_assume_tac slot_capture_source >>
  `~is_word_type (post_value_type c e)` by simp[is_word_type_def] >>
  `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
  `alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  drule_all slot_length_run >> disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `t.vs_labels = u.vs_labels` by (qpat_assum `t = _` (fn th => simp[Once th])) >>
  qpat_x_assum `t = _` (mk_asm "length_state") >>
  `len < dimword (:256)` by
    (`bound_length bd < dimword (:256)` by
       (irule typed_copy_array_count_bound >> qexistsl [`elem`,`get_tenv cx`,`ArrayTV et bd`] >>
        qpat_assum `post_value_type c e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `compatible_bound bd len` mp_tac >>
     qpat_assum `bound_length bd < _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> simp[vyperValueTheory.compatible_bound_def,bound_length_def] >> decide_tac) >>
  `copy_old_operand sb (vv_operand vv)` by
    (drule_all_then ACCEPT_TAC compile_expr_old_operand) >>
  `eval_operand (vv_operand vv) t = SOME slot /\ op_taint tt (vv_operand vv) = {}` by
    (`eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u /\
      op_prov Gt (vv_operand vv) = op_prov Gu (vv_operand vv) /\
      op_taint tt (vv_operand vv) = op_taint tu (vv_operand vv)` by
       (irule slot_old_operand >> conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac `sb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`c`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved c sb` by (fs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`len`,`vs`,`off`,`root`,`path`,`delta`,`t`,`Gt`,`tt`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC ORELSE all_tac)
  >- (irule for_array_slot_result_replay_mods >> qexists_tac `len` >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H0` assume_tac) >>
      drule gas_origin_ptr_path_dalloca_fmp_headroom >>
      disch_then (mk_asm "reach") >> rpt gen_tac >> strip_tac >>
      asm "reach" irule >> conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `fn` >> first_assum ACCEPT_TAC)
  >- (simp[for_array_capture_frame_mods_def,alloca_frame_def] >>
      rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >>
      `copy_old_operand saL (vv_operand vv) /\ copy_old_operand saL len_op` by
        (fs[copy_old_operand_def] >> metis_tac[not_fresh_at_mono]) >>
      `!op. copy_old_operand saL op ==>
          eval_operand op z = eval_operand op t /\ op_prov Gz op = op_prov Gt op /\
          op_taint tz op = op_taint tt op` by
        (gen_tac >> strip_tac >> irule slot_old_operand >>
         conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `saL` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `!op. copy_old_operand saL op ==> _`
        (qspec_then `len_op` (fn th => drule_then strip_assume_tac th)) >>
      qpat_x_assum `!op. copy_old_operand saL op ==> _`
        (qspec_then `vv_operand vv` (fn th => drule_then strip_assume_tac th)) >>
      rpt conj_tac >> PURE_ASM_REWRITE_TAC[] >> REFL_TAC) >>
  gen_tac >> strip_tac >>
  conj_tac >- (first_x_assum irule) >>
  conj_tac >-
    (irule aug_place_storage_rooted_observed >>
     qexistsl [`cx`,`delta`,`off`,`path`,`st0`,`em.storage_trace`,`root`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!K. valid_horizon cx st0 K em.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
  qpat_assum `vv_post_mods H ctx func c cx e es sa sb s0 em _ vv u`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  asm_x "length_state" assume_tac >>
  drule_all_then strip_assume_tac slot_length_linked_frame >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
