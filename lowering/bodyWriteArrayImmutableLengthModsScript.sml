(* A constructor write target reads its length from the qualified current region. *)
Theory bodyWriteArrayImmutableLengthMods
Ancestors
  bodyWriteArrayPacketMods bodyFullSubscriptLiveImmSelect bodyInvSplit exprSimHypsDefs
  immutableRegionFrameProps immutableRegionTypingProps bodyInvCodeProps bodyInvMetadataProps
  exprBodyPreProps vyperTypeEnv vyperTypeInvariants vyperFixedShapePath
  vyperPlaceStatePreservation vyperInterpreter vyperState vyperTyping
  vyperValueOperation vyperValue exprSimProps targetSubscriptMemory
  moduleVariableKeyProps supportedNameRoot allocLimits bodyFullPostsMods
  bodyFullShadowBodyInv bodyFullTargetArrayLoad words finite_map alist
  bodyWriteTargetStageMods loweringPosts stateRelProj exprLoweringProps
  bodyPtrBopInMemoryContents bodyPtrBopInRepresentation bodyPtrDefs
  valueEncoding valueEncodingProps exprSimSubscriptArraySuffix
  venomExecSemantics venomInst venomState ptrDiscipline memSafeRun
  instMemFrontier contextCodegenRel codegenRel memLocDefs
  augAssignPtrScalarSafety augAssignPtrScalarCertificate immutableRegionLoadPtr
  stmtAppendStorageRunPtr emitHelperProps emitHelper context compileEnv

Theorem write_array_immutable_key[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==>
  ~cx_const_name_mods mods (src,id) /\
  ?tops ty. ALOOKUP cenv.ce_modules src = SOME tops /\
            FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods src id off bytes` by metis_tac[] >>
  reverse conj_tac
  >- (drule_then assume_tac contract_inv_cenv_modules >>
      drule_all_then strip_assume_tac immutable_region_mods_type >> simp[]) >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
  drule_then assume_tac contract_inv_unqualified_variable_keys >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[] >>
  `supported_variable_decl tops (NONE,id) = SOME (vis,Immutable,ty,slot)` by
    metis_tac[supported_variable_decl_distinct_mem] >>
  strip_tac >>
  `MEM id (MAP FST (module_consts_env tops []))` by
    (fs[cx_const_name_mods_def] >> metis_tac[optionTheory.SOME_11]) >>
  drule distinct_module_consts_env_names_constant >>
  disch_then (qspec_then `id` mp_tac) >> simp[]
QED

Theorem write_array_immutable_root_tag[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP env.bare_globals (owner,id) = SOME ty /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (rt,v) ==>
  evaluate_type (get_tenv cx) ty = SOME rt
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  fs[env_consistent_def, env_immutables_consistent_def] >>
  qpat_assum `!src id ty tv v. _ ==> evaluate_type _ ty = SOME tv`
    (qspecl_then [`owner`,`id`,`ty`,`rt`,`v`] mp_tac) >> simp[]
QED

Theorem write_array_immutable_root_typed[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (rt,v) ==>
  well_formed_type_value rt /\ value_has_type rt v
Proof
  strip_tac >> `state_well_typed es` by fs[expr_sim_inv_mods_def] >>
  drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
  drule_all imms_well_typed_get_source_immutables >> simp[]
QED

Theorem write_array_immutable_fixed_current[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP env.bare_globals (owner,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ fixed_shape_path rt path ==>
  ?imms iv a. ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (rt,iv) /\
    evaluate_subscripts rt iv path = INL a
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all_then strip_assume_tac env_consistent_bare_global_ready_src >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >- gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables owner imms) id` >> gvs[] >>
  rename1 `FLOOKUP (get_source_immutables owner imms) id = SOME entry` >>
  PairCases_on `entry` >> drule_all_then assume_tac write_array_immutable_root_tag >>
  gvs[] >> drule_all_then strip_assume_tac write_array_immutable_root_typed >>
  irule fixed_shape_path_live >> simp[]
QED

Theorem write_array_current_path[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env mid1 /\
  expr_sim_inv_mods mods cenv cx env mid2 /\
  expr_body_pre_mods mods cenv cx env e (mid1 with gas_obs := gs) /\
  bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := gs) = (INL v,mid2) /\
  target_root bt = TopLevelNameTarget (owner,id) /\
  ~target_subscript_overlap cenv bt e /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP mid1.immutables cx.txn.target = SOME imms1 /\
  FLOOKUP (get_source_immutables owner imms1) id = SOME (rt,iv1) /\
  evaluate_subscripts rt iv1 path = INL a1 /\
  (~target_through_dynarray cenv bt ==> fixed_shape_path rt path) ==>
  ?imms iv a. ALOOKUP mid2.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (rt,iv) /\
    evaluate_subscripts rt iv path = INL a
Proof
  strip_tac >>
  `~cx_const_name_mods mods (owner,id) /\
   ?tops ty. ALOOKUP cenv.ce_modules owner = SOME tops /\
             FLOOKUP env.bare_globals (owner,id) = SOME ty` by
    (drule_all write_array_immutable_key >> simp[]) >>
  Cases_on `target_through_dynarray cenv bt`
  >- (Cases_on `eval_expr cx e (mid1 with gas_obs := gs)` >>
      gvs[bind_def] >> rename1 `eval_expr _ _ _ = (raw,after)` >>
      Cases_on `raw` >> gvs[] >> drule_then SUBST_ALL_TAC read_result_state >>
      drule_all_then mp_tac immutable_target_index_frame_mods >> simp[] >>
      Cases_on `ALOOKUP after.immutables cx.txn.target`
      >- simp[get_source_immutables_def] >>
      strip_tac >> rename1 `ALOOKUP after.immutables cx.txn.target = SOME imms2` >>
      qexistsl [`imms2`,`iv1`,`a1`] >> fs[]) >>
  `evaluate_type (get_tenv cx) ty = SOME rt` by
    (drule_all write_array_immutable_root_tag >> simp[]) >>
  `fixed_shape_path rt path` by simp[] >>
  drule_all write_array_immutable_fixed_current >> simp[]
QED

Theorem write_array_immutable_current_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  cenv.ce_is_ctor /\ FST (SND rb) = SOME LocCode /\
  ?off k itv imms iv etv av.
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP mid2.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    evaluate_subscripts itv iv path = INL (ArrayV av) /\
    well_formed_type_value itv /\ value_has_type itv iv /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    array_length (ArrayTV etv bd) av < dimword (:256) /\
    eval_operand (FST rb) t1 = SOME (n2w (off+k))
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_reached_immutable_mods >>
  qhdtm_x_assum `write_array_reached_mods`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  `~target_subscript_overlap cenv bt e` by fs[alloc_limits_expr_def] >>
  drule_all_then strip_assume_tac write_array_current_path >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\ ptv = ArrayTV etv bd` by
    fs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  drule_all_then strip_assume_tac write_array_immutable_root_typed >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `value_has_type (ArrayTV etv bd) a'` by
    (irule evaluate_subscripts_type >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `a'` >> gvs[value_has_type_def] >>
  rename1 `evaluate_subscripts itv _ path = INL (ArrayV av)` >>
  `array_length (ArrayTV etv bd) av < dimword (:256)` by
    (irule target_memory_array_length_bound >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  metis_tac[]
QED

Theorem write_array_ctor_iload_step[local]:
  emit_op ILOAD [addr] sa = (Var out,sb) /\
  eval_operand addr s = SOME a /\ op_prov G addr = NONE /\
  op_taint tn addr = {} /\ w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  array_length_step_ok lo ctx func ILOAD [addr] (mload (w2n a) s)
    sa out sb s G tn
Proof
  strip_tac >> simp[array_length_step_ok_def, below_frontier_ILOAD] >>
  conj_tac
  >- (`mk_inst sa.cs_next_id ILOAD [addr] [out] =
       instruction sa.cs_next_id ILOAD [addr] [out]` by
        simp[mk_inst_def, instruction_component_equality] >>
      simp[step_inst_base_ILOAD]) >>
  simp[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mem_read_ops_def, mk_inst_def] >>
  decide_tac
QED

Theorem write_array_ctor_load_packet[local]:
  compile_ptr_load T imm LocCode addr sa = (p,sb) /\
  eval_operand addr s = SOME a /\ op_prov G addr = NONE /\ op_taint tn addr = {} /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!rb. imm = SOME rb ==>
    eval_operand rb s = SOME 0w /\ op_prov G rb = NONE /\ op_taint tn rb = {}) ==>
  ?t G' tn'. array_length_loader_ok T imm LocCode addr (mload (w2n a) s)
    sa p sb lo ctx func PG s G tn t G' tn'
Proof
  Cases_on `imm` >> simp[compile_ptr_load_def, compile_imm_load_word_def] >> strip_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      rename1 `p = Var out` >> gvs[] >>
      simp[array_length_loader_ok_def, compile_ptr_load_def, compile_imm_load_word_def] >>
      qexists `ILOAD` >> simp[] >> irule write_array_ctor_iload_step >> simp[]) >>
  rename1 `emit_op ADD [addr;rb]` >>
  Cases_on `emit_op ADD [addr;rb] sa` >>
  gvs[comp_bind_def] >>
  rename1 `emit_op ADD [addr;rb] sa = (ap,sm)` >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qmatch_asmsub_abbrev_tac `ap = Var out1` >> gvs[] >>
  qpat_assum `emit_op ILOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qmatch_asmsub_abbrev_tac `p = Var out2` >> gvs[] >>
  rename1 `emit_op ADD [addr;rb] sa = (Var out1,sm)` >>
  rename1 `emit_op ILOAD [Var out1] sm = (Var out2,sb)` >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ADD [addr;rb] [out1]` >>
  qabbrev_tac `u1 = update_var out1 a s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  qabbrev_tac `G1 = step_prov PG G i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 s u1 tn` >>
  `eval_operand (Var out1) s1 = SOME a /\ mload (w2n a) s1 = mload (w2n a) s /\
   s1.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (fs[Abbr `s1`, Abbr `u1`, allocas_from_def, allocas_below_fmp_def,
        mload_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `op_prov G1 (Var out1) = NONE /\ op_taint tn1 (Var out1) = {}` by
    (conj_tac
     >- simp[Abbr `G1`, Abbr `i1`, add_selected_provenance, first_prov_def] >>
     simp[Abbr `tn1`, Abbr `i1`, scalar_add_taint, Abbr `u1`, update_var_def,
          op_taint_def, FLOOKUP_UPDATE]) >>
  `access_ok lo G func i1 s /\ taint_ok func tn i1 s` by
    (irule scalar_access_taint_ok_lo >>
     simp[Abbr `i1`, scalar_shape_def, scalar_binary_def, mk_inst_def]) >>
  `array_length_step_ok lo ctx func ILOAD [Var out1] (mload (w2n a) s)
     sm out2 sb s1 G1 tn1` by
    (qpat_assum `mload _ s1 = _` (once_rewrite_tac o single o GSYM) >>
     irule write_array_ctor_iload_step >> simp[]) >>
  `inst_mem_below_frontier i1 s` by
    (irule below_frontier_no_ranges >> simp[Abbr `i1`, mk_inst_def]) >>
  simp[array_length_loader_ok_def, LET_THM, WORD_ADD_0] >>
  `LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 1` by simp[] >>
  qpat_assum `LENGTH sm.cs_current_insts = _` (once_rewrite_tac o single o GSYM) >>
  simp[Abbr `tn1`, Abbr `G1`, Abbr `s1`, Abbr `u1`, Abbr `i1`, WORD_ADD_0]
QED

Theorem write_array_ctor_base_clean[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ lo <> 0 /\
  cenv.ce_imm_alloca = SOME base_op ==>
  eval_operand base_op s = SOME 0w /\ op_prov G base_op = NONE /\ op_taint tn base_op = {}
Proof
  strip_tac >> drule_all_then assume_tac membership_immutable_base_value >>
  Cases_on `base_op` >> fs[ghost_inv_at_mods_def, op_prov_def, op_taint_def]
QED

Theorem write_array_ctor_header[local]:
  mem_path_offset itv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  well_formed_type_value itv /\ value_has_type itv iv /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) /\
  off + type_memory_size itv <= lo /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory itv iv off m) ==>
  off + k + 32 <= lo /\
  mload (off+k) s = n2w (array_length (ArrayTV etv (Dynamic cap)) av) /\
  mem_word_taint tn.t_mem (off+k) = {}
Proof
  strip_tac >> drule_then strip_assume_tac mem_path_offset_sound >>
  conj_tac >- (fs[type_memory_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (off+k) m` by
    (rpt strip_tac >> irule mem_path_offset_current_value >>
     qexistsl [`iv`,`path`,`itv`] >> simp[]) >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  conj_tac
  >- (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
      simp[mem_agree_outside_def, val_in_memory_dynarray, mem_word_at_eq_mload,
           array_length_def]) >>
  metis_tac[dynarray_memory_header_clean]
QED

(* The saved operand supplies the address, never the length.  A dynamic
   bound comes from the current qualified value after evaluation of e. *)
Theorem write_array_immutable_length_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP mid2.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand (FST rb) t2 = SOME (n2w (off+k)) /\
  op_prov G2 (FST rb) = NONE /\ op_taint tn2 (FST rb) = {} /\
  i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) ==>
  let cnt = array_length (ArrayTV etv bd) av in
    off + type_memory_size itv <= lo /\ off+k < dimword (:256) /\
    (valid_index (ArrayTV etv bd) av i <=>
      idx_in_range (is_signed_type (expr_type e)) iw (n2w cnt)) /\
    (!cap. bd = Dynamic cap ==>
      w2n (n2w (off+k):bytes32) + 32 <= lo /\
      mload (off+k) t2 = n2w cnt /\ mem_word_taint tn2.t_mem (off+k) = {} /\
      !p sl. compile_ptr_load T cenv.ce_imm_alloca LocCode (FST rb) sn = (p,sl) ==>
        ?t G' tn'. array_length_loader_ok T cenv.ce_imm_alloca LocCode (FST rb)
          (n2w cnt) sn p sl lo ctx func PG t2 G2 tn2 t G' tn')
Proof
  strip_tac >> simp[LET_THM] >>
  drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  qhdtm_x_assum `write_array_reached_mods`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  `?tops. ALOOKUP cenv.ce_modules owner = SOME tops` by
    (drule_all write_array_immutable_key >> metis_tac[]) >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by fs[write_target_entry_mods_def] >>
  `stmt_state_rel H ctx func cenv cx mid2 t2 /\
   immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor mid2 t2` by
    fs[expr_post_mods_def, expr_post_def, immutable_frame_mods_def] >>
  `off + type_memory_size itv <= lo /\
   !m. mem_agree_outside tn2.t_mem t2.vs_memory m ==> val_in_memory itv iv off m` by
    (drule_all (SIMP_RULE bool_ss []
       (Q.INST [`entry` |-> `es`] qualified_immutable_ctor_frame_mods)) >> simp[]) >>
  `t2.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> metis_tac[alloca_room_next_lt]) >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `off+k < dimword (:256)` by
    (drule_then strip_assume_tac mem_path_offset_sound >> decide_tac) >>
  simp[] >> conj_tac
  >- (drule_all target_memory_array_length_bound >>
      disch_then (mp_then Any mp_tac array_index_word_bounds) >> simp[]) >>
  gen_tac >> disch_then SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac write_array_immutable_root_typed >>
  drule_all_then strip_assume_tac write_array_ctor_header >>
  `w2n (n2w (off+k):bytes32) = off+k` by simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[] >>
  `!base_op. cenv.ce_imm_alloca = SOME base_op ==>
    eval_operand base_op t2 = SOME 0w /\ op_prov G2 base_op = NONE /\ op_taint tn2 base_op = {}` by
    (rpt strip_tac >> `lo <> 0` by decide_tac >>
     drule_all write_array_ctor_base_clean >> simp[]) >>
  conj_tac >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `mload (off+k) t2 = _` (once_rewrite_tac o single o GSYM) >>
  qpat_assum `w2n (n2w (off+k):bytes32) = _` (once_rewrite_tac o single o GSYM) >>
  irule write_array_ctor_load_packet >>
  simp[] >> drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]
QED
