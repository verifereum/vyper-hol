(* The reached Range head is installed before the body fragment is run. *)
Theory bodyForRangeConsEntryMods
Ancestors
  bodyForRangeHeaderMods bodyForRangeScalarFrameMods bodyForEntryInputsMods
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs bodyInvSplit
  bodyBranchCellFrameMods bodyFullForRange bodyFullShared bodyFullPathHistory
  bodyFullIfExpReach forConsBodyGas bodyExprPreFacts bodyMemoryDefs
  exprSimMemorySource[qualified]
  bodyFullForFacts exprSimHypsDefs constSubstCorrect placeTypingProps
  exprLoweringProps loweringStateRelDefs loweringSlice compileEnv exprSimAbiEncodeMemoryLength
  ghostPcTransportPtr wordLoadStorePtr valueEncodingProps valueEncodingTyping
  exprSimOperands exprSimWordArgs exprSimPtrTopLevelImmutableCopy
  stmtSimForRange stmtSimDeclCompose stmtSimProps stmtSimDefs
  vyperTypeInvariants vyperTypeEvalSoundness vyperTypeEnvPreservation
  vyperTypeValues vyperTypeSystem vyperInterpreter vyperState
  stmtLowering stmtSimForLoop exprPtrUnwrapCondition bodyPtrBopInLiteralSuffix codegenRel pred_set
  vyperStorageTrace vyperStorageFootprint venomState venomExecSemantics
  venomInst ptrDiscipline allocaHistory freshWrites finite_map list
  stateRelProj venomMemDefs bodySimFull fragExec fragGasOriginPtr loweringPosts

val _ = Parse.hide "body";

Theorem range_scope_inv_gas[local]:
  expr_sim_inv_mods mods ce cx en (e with gas_obs := obs) =
  expr_sim_inv_mods mods ce cx en e
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem range_scope_inv_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
  declare_local cenv id fty st = (bc,st1) /\ cenv.ce_alloca_locals ==>
  expr_sim_inv_mods mods bc cx (extend_local env id fty F)
    (es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                       value := v; popped := []|>)) :: es.scopes; gas_obs := []|>)
Proof
  strip_tac >>
  qabbrev_tac `sc = FEMPTY |+ (id,<|assignable := F; type := tyv;
                                     value := v; popped := []|>)` >>
  `expr_sim_inv_mods mods bc cx (extend_local env id fty F)
     (es with scopes updated_by CONS sc)` suffices_by
    (`es with <|scopes := sc :: es.scopes; gas_obs := []|> =
       (es with scopes updated_by CONS sc) with gas_obs := []` by
       simp[evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >> pure_rewrite_tac [range_scope_inv_gas] >> simp[]) >>
  qhdtm_x_assum `expr_sim_inv_mods`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `env_consistent (extend_local env id fty F) cx (es with scopes updated_by CONS sc)` by
    (simp[Abbr `sc`] >> irule push_scope_with_var_env_consistent >> simp[]) >>
  `well_formed_type_value tyv` by metis_tac[evaluate_type_well_formed_type_value] >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `popped_keys_indexed (sc :: es.scopes)` by
    (fs[Abbr `sc`, popped_keys_indexed_def] >> simp[FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `bc.ce_var_type = (id =+ SOME fty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
       ?p sz. FLOOKUP bc.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >> metis_tac[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
       bc.ce_var_type n = SOME ty` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _;
                           ce_dynarray_capacity := _|> = cenv`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `(place_map_tables_agree_on_defined bc (extend_local env id fty F) <=>
    place_map_tables_agree_on_defined cenv env)` by
    (irule place_map_tables_agree_on_defined_cong >> fs[extend_local_def]) >>
  `(extend_local env id fty F).fn_sigs = env.fn_sigs /\
   (extend_local env id fty F).current_src = env.current_src` by simp[extend_local_def] >>
  `state_well_typed (es with scopes updated_by CONS sc)` by simp[Abbr `sc`] >>
  pure_asm_rewrite_tac [expr_sim_inv_mods_def, extend_local_bare_globals] >>
  simp[NoAsms] >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Theorem range_cell_extend_mods[local]:
  body_const_cells_agree_mods mods cx (extend_local env id typ a) es <=>
  body_const_cells_agree_mods mods cx env es
Proof
  simp[body_const_cells_agree_mods_def, frame_maps_extend_local,
       checked_frame_context_extend_local, extend_local_def]
QED

Theorem range_scope_source_mods[local]:
  body_const_cells_agree_mods mods cx env es /\
  gas_admissible (eval_for cx tyv id body (Value (IntV z)::rs)) (stmt_res_ok lctx) es /\
  lookup_scopes id es.scopes = NONE /\
  ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                value := IntV z; popped := []|>)) :: es.scopes;
                 gas_obs := []|> ==>
  bind (read_result cx (Value (IntV z))) (push_scope_with_var id tyv)
    (es with gas_obs := []) = (INL (),ep) /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit_lbl incr_lbl)) ep /\
  body_const_cells_agree_mods mods cx (extend_local env id typ F) ep
Proof
  strip_tac >> conj_tac
  >- simp[read_result_def, bind_def, return_def, push_scope_with_var_def,
          evaluation_state_component_equality] >>
  conj_tac
  >- (qpat_assum `ep = _` SUBST1_TAC >> irule captured_storage_body_admissible >>
      simp[] >> qexistsl_tac [`Value (IntV z)`, `lctx`, `stmt_res_ok lctx`, `rs`] >>
      simp[read_result_def, return_def]) >>
  simp[range_cell_extend_mods] >>
  `ep.immutables = es.immutables` by simp[] >>
  drule body_const_cells_agree_mods_immutables >> simp[]
QED

(* A copied iterator item and its source binding use the same reached value. *)
Theorem for_item_push_source_mods:
  read_result cx a es = (INL v,es) /\
  gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
  declare_local cenv id typ st = (bc,st1) /\ cenv.ce_alloca_locals /\
  ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                           value := v; popped := []|>)) :: es.scopes;
                 gas_obs := []|> ==>
  (!tail. bind (read_result cx a) (push_scope_with_var id tyv)
       (es with gas_obs := tail) = (INL (),ep with gas_obs := tail)) /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit_lbl incr_lbl)) ep /\
  expr_sim_inv_mods mods bc cx (extend_local env id typ F) ep /\
  body_const_cells_agree_mods mods cx (extend_local env id typ F) ep
Proof
  strip_tac >> conj_tac
  >- (drule_then assume_tac exprSimMemorySourceTheory.read_result_gas_obs >>
      simp[bind_def, push_scope_with_var_def, return_def,
           evaluation_state_component_equality]) >>
  conj_tac
  >- (qpat_assum `ep = _` SUBST1_TAC >> irule captured_storage_body_admissible >>
      simp[] >> qexistsl_tac [`a`,`lctx`,`stmt_res_ok lctx`,`rs`] >> simp[]) >>
  conj_tac
  >- (qpat_assum `ep = _` SUBST1_TAC >> irule range_scope_inv_mods >>
      simp[] >> qexistsl_tac [`cenv`,`st`,`st1`] >> simp[]) >>
  simp[range_cell_extend_mods] >>
  `ep.immutables = es.immutables` by simp[] >>
  drule body_const_cells_agree_mods_immutables >> simp[]
QED

(* Fix the endpoint and its ghosts before choosing a storage horizon. *)
Theorem range_cons_path_mods[local]:
  for_code func cenv bc ty body id tyv p sz ainst cv ev dv nv cond_lbl
    exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
  lookup_var cv s = SOME (i2w (n1 + &k)) /\ lookup_var ev s = SOME (i2w n2) /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
  lo <= w2n w /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n w + 32 <= s.vs_alloca_next /\
  b = jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1) /\
  u = mstore (w2n w) (i2w (n1 + &k)) b /\ t = u with vs_inst_idx := 1 /\
  Gb = DRESTRICT G (COMPL {dv}) /\ tb = tn with t_var := tn.t_var |+ (dv,{}) /\
  tf = tb with t_mem := tb.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gb,tf)
Proof
  strip_tac >> qx_gen_tac `D` >>
  drule_all (REWRITE_RULE [LET_THM] range_entry_joint_path) >>
  disch_then (qspecl_then [`D`,`explicit`,`PG`] mp_tac) >>
  qhdtm_x_assum `for_code` (strip_assume_tac o REWRITE_RULE [for_code_def]) >>
  qabbrev_tac `be = update_var dv (bool_to_word F) s` >>
  qabbrev_tac `bs = be with vs_inst_idx := 1` >>
  qabbrev_tac `ie = mk_inst j1 EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `ij = mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []` >>
  `step_prov PG G ie be = Gb /\ step_taint ie s be tn = tb` by
    (simp[Abbr `ie`, Abbr `be`, step_prov_def, set_prov_def, out_prov_def,
          mk_inst_def, membership_scalar_ghost_frame] >>
     simp[GSYM mk_inst_def, membership_scalar_ghost_frame]) >>
  `step_prov PG Gb ij b = Gb /\ step_taint ij bs b tb = tb` by
    simp[Abbr `ij`, Abbr `bs`, Abbr `be`, step_prov_def, set_prov_def,
         out_prov_def, step_taint_def, set_var_taint_def, mem_taint_def,
         new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
         range_bytes_def, written_taint_def, store_taint_def, adopt_reset_def,
         imm_taint_def, mk_inst_def, jump_to_def, taint_component_equality,
         FLOOKUP_DEF, DRESTRICT_UNIV, EXTENSION, SF CONJ_ss] >>
  `lookup_var p b = SOME w /\ eval_operand (Var cv) b = SOME (i2w (n1 + &k)) /\
   op_taint tb (Var cv) = {}` by
    fs[eval_operand_def, Abbr `bs`, Abbr `be`, lookup_var_def,
       jump_to_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
  drule_all toplevel_immutable_mstore_ghost_frame >>
  disch_then (qspecl_then [`j3`,`PG`,`Gb`] strip_assume_tac) >>
  disch_then (mp_tac o CONJUNCT1) >>
  qpat_assum `b = _` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `u = _` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `t = _` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `step_prov _ _ ie _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `step_taint ie _ _ _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `step_prov _ _ ij _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `step_taint ij _ _ _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `u = _` (pure_rewrite_tac o single) >>
  simp[NoAsms] >>
  qpat_assum `step_prov _ _ (mk_inst _ MSTORE _ _) _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `step_taint (mk_inst _ MSTORE _ _) _ _ _ = _` (pure_rewrite_tac o single) >>
  qpat_assum `tf = _` (pure_rewrite_tac o single) >> simp[NoAsms]
QED

(* The local-value frame is independent of the immutable floor. Restore the
   linked floor from the unchanged low prefix after installing the local. *)
Theorem range_store_ghost_restore_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es Gb tb b /\
  ghost_inv_at D 0 d bc cx ep Gb tf t /\
  bc.ce_modules = cenv.ce_modules /\ bc.ce_module_vars = cenv.ce_module_vars /\
  bc.ce_imm_alloca = cenv.ce_imm_alloca /\
  t.vs_allocas = b.vs_allocas /\ t.vs_alloca_next = b.vs_alloca_next /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo b.vs_memory /\
  tf.t_var = tb.t_var /\ tf.t_mem SUBSET tb.t_mem ==>
  ghost_inv_at_mods D lo d bc cx ep Gb tf t
Proof
  strip_tac >>
  `imm_section_dead_mods bc = imm_section_dead_mods cenv` by
    simp[FUN_EQ_THM, imm_section_dead_mods_def] >>
  `!x. op_taint tf (Var x) = op_taint tb (Var x)` by simp[op_taint_def] >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def, SUBSET_DEF] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem range_store_state_ghost_mods[local]:
  stmt_state_rel H ctx func cenv cx es b /\
  ghost_inv_at_mods D lo d cenv cx es Gb tb b /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm) /\
  bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
             ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z'. l = PtrVar q z') /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr bc (FEMPTY::es.scopes) p /\
  lookup_var p b = SOME w /\ ptr_covers Gb tb p b sz /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP b.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
  type_memory_size tyv = 32 /\ word_memory_type tyv /\ val_wf tyv (IntV z) /\
  lo <= w2n w /\
  ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                              value := IntV z; popped := []|>)) :: es.scopes;
                 gas_obs := []|> /\
  t = (mstore (w2n w) (i2w z) b) with vs_inst_idx := 1 /\
  tf = tb with t_mem := tb.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} ==>
  stmt_state_rel H ctx func bc cx ep t /\ ghost_inv_at_mods D lo d bc cx ep Gb tf t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es Gb tb b` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `0 <= w2n w` by simp[] >>
  drule_all (REWRITE_RULE [LET_THM] range_entry_store_scope) >> strip_tac >>
  `?ep0. ep = ep0 with gas_obs := [] /\ stmt_state_rel H ctx func bc cx ep0
       (mstore (w2n w) (i2w z) b) /\ ghost_inv_at D 0 d bc cx ep0 Gb tf
       (mstore (w2n w) (i2w z) b)` by
    (qexists_tac `es with scopes := (FEMPTY |+ (id,<|assignable := F;
       type := tyv; value := IntV z; popped := []|>)) :: es.scopes` >>
     simp[evaluation_state_component_equality]) >>
  conj_tac >- simp[stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
  irule range_store_ghost_restore_mods >> conj_tac
  >- (qpat_assum `ep = ep0 with gas_obs := []` SUBST1_TAC >>
      qpat_assum `t = _` SUBST1_TAC >>
      pure_rewrite_tac[ghost_inv_at_inst_idx] >>
      qpat_assum `ghost_inv_at _ 0 _ bc _ ep0 _ _ _` mp_tac >>
      simp[NoAsms, ghost_inv_at_def, GSYM IMP_CONJ_THM, GSYM FORALL_AND_THM] >>
      strip_tac >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`b`,`cenv`,`es`,`tb`] >>
  qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _;
                           ce_dynarray_capacity := _|> = cenv`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo b.vs_memory` by
    simp[mstore_mem_bytes_at_disjoint] >>
  pure_asm_rewrite_tac [] >> simp[mstore_def, SUBSET_DEF]
QED

Theorem range_new_local_regions[local]:
  ep.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
  local_ptrs_reserved cenv sa /\ lookup_var p t = SOME w /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  !n b len. local_region bc ep.scopes t n b len ==>
            local_region cenv es.scopes s n b len \/ (b = w2n w /\ len = sz)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[local_region_def] >> strip_tac >>
  Cases_on `n = id` >- gvs[] >>
  rename1 `FLOOKUP bc.ce_vars n = SOME (PtrVar (Var q) len)` >>
  `FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) len)` by
    (qpat_assum `!n. n <> id ==> _` (drule_then mp_tac) >> simp[]) >>
  `not_fresh_at sa q` by metis_tac[local_ptrs_reserved_def] >>
  `id <> n` by metis_tac[] >>
  qpat_x_assum `lookup_scopes n ep.scopes = _` mp_tac >>
  simp[lookup_scopes_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem range_store_immutable_mods[local]:
  immutable_frame_mods func cenv cx es s /\ ep.immutables = es.immutables /\
  bc.ce_modules = cenv.ce_modules /\ bc.ce_module_vars = cenv.ce_module_vars /\
  bc.ce_module_var_type = cenv.ce_module_var_type /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\ 32 <= sz /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (at,sz) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_data_section = s.vs_data_section /\ t.vs_memory = (mstore at v s).vs_memory /\
  (!n b len. local_region bc ep.scopes t n b len ==>
     local_region cenv es.scopes s n b len \/ (b = at /\ len = sz)) ==>
  immutable_frame_mods func bc cx ep t
Proof
  strip_tac >> fs[immutable_frame_mods_def, immutables_rel_mods_def,
                  immutable_alloca_sep_mods_def] >>
  `!src n b len. local_region (bc with ce_module := src) ep.scopes t n b len ==>
     local_region (cenv with ce_module := src) es.scopes s n b len \/
     (b = at /\ len = sz)` by
    (rpt gen_tac >>
     qpat_assum `!n b len. local_region bc _ _ _ _ _ ==> _`
       (qspecl_then [`n`,`b`,`len`] mp_tac) >>
     simp[NoAsms, local_region_def, GSYM IMP_CONJ_THM, GSYM FORALL_AND_THM] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t` suffices_by
        simp[immutables_rel_def] >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      conj_tac >- simp[abi_encode_mstore_memory_length] >>
      rpt strip_tac >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by simp[] >>
      `regions_disjoint off (type_memory_size tv) at sz` by
        (fs[immutable_alloca_sep_def] >> metis_tac[]) >>
      irule mstore_mem_bytes_at_disjoint >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by simp[] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[NoAsms, immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  rpt strip_tac >> fs[] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  metis_tac[]
QED

Theorem range_condition_state_mods[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa dv /\ not_local_ptr cenv es.scopes dv /\ dv <> p /\
  ptr_covers G tn p s sz /\
  b = jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1) /\
  Gb = DRESTRICT G (COMPL {dv}) /\ tb = tn with t_var := tn.t_var |+ (dv,{}) ==>
  stmt_state_rel H ctx func cenv cx es b /\
  ghost_inv_at_mods D lo d cenv cx es Gb tb b /\ ptr_covers Gb tb p b sz
Proof
  strip_tac >> conj_tac
  >- (simp[stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  reverse conj_tac
  >- fs[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
        jump_to_def, update_var_def, lookup_var_def] >>
  irule ghost_inv_at_mods_exterior_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Only the zero-observation head prefix is executed here. The guarded
   body judgment is exposed to the consumer at this same scoped endpoint. *)
Theorem range_cons_entry_mods:
  for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
    exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  declare_local cenv id typ st = (bc,st1) /\ cenv.ce_alloca_locals /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ id NOTIN FDOM env.var_types /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa dv /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  sa.cs_next_id <= ainst.inst_id /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  body_for_full_ok_mods mods exps cx tyv id body
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
      sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p ainst.inst_id sz w
      H (a::rs) es G tn s) /\
  gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es ==>
  ?k ep t Gf tf.
    a = Value (IntV (n1 + &k)) /\ k + LENGTH (a::rs) = Num (n2 - n1) /\
    rs = GENLIST (\j. Value (IntV (n1 + &((k + 1) + j)))) (LENGTH rs) /\
    value_has_type tyv (IntV (n1 + &k)) /\
    body_stmts_full_ok_mods mods exps cx body /\
    ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                     value := IntV (n1 + &k); popped := []|>)) :: es.scopes;
                   gas_obs := []|> /\
    bind (read_result cx a) (push_scope_with_var id tyv) (es with gas_obs := []) = (INL (),ep) /\
    body_const_cells_agree_mods mods cx (extend_local env id typ F) ep /\
    expr_sim_inv_mods mods bc cx (extend_local env id typ F) ep /\
    gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit_lbl incr_lbl)) ep /\
    cenv_top_ext cenv bc ep.scopes /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!x. x <> dv ==> lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
                     op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ ptr_covers Gf tf p t sz /\
    t.vs_current_bb = sb0.cs_current_bb /\ t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ~t.vs_halted /\ ret_pc_ok bc sb0 t /\ return_buf_frame d bc sb0 t /\
    return_buf_sep d bc ep t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v) /\
    (!H. valid_horizon cx st0 H ep.storage_trace ==>
       stmt_state_rel H ctx func bc cx ep t /\ immutable_frame_mods func bc cx ep t /\
       storage_well_formed_on cx ep (FST H) /\ ghost_inv_at_mods (DF H) lo d bc cx ep Gf tf t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
                               op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 bc ep t /\
    (!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
       (!nm b z. local_region cenv es0.scopes s0 nm b z ==> off + len <= b \/ b + z <= off) /\
       off <= i /\ i < off + len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >> qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then assume_tac) >>
  qhdtm_x_assum `range_header_mods` (strip_assume_tac o REWRITE_RULE [range_header_mods_def]) >>
  drule_all range_suffix_cons_mods >> strip_tac >>
  qpat_x_assum `a = Value _` SUBST_ALL_TAC >>
  `value_has_type tyv (IntV (n1 + &k))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  `val_wf tyv (IntV (n1 + &k))` by (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  `body_stmts_full_ok_mods mods exps cx body` by
    (`Num (n2 - n1) = SUC (k + LENGTH rs)` by
       (qpat_assum `k + 1 + LENGTH rs = _` mp_tac >> decide_tac) >>
     qhdtm_x_assum `body_for_full_ok_mods` mp_tac >>
     simp[body_for_full_ok_mods_def, GENLIST_CONS, read_result_def, return_def]) >>
  qabbrev_tac `entry = <|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>` >>
  qabbrev_tac `ep = es with <|scopes := (FEMPTY |+ (id,entry)) :: es.scopes; gas_obs := []|>` >>
  qabbrev_tac `b = jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)` >>
  qabbrev_tac `u = mstore (w2n w) (i2w (n1 + &k)) b` >>
  qabbrev_tac `t = u with vs_inst_idx := 1` >>
  qabbrev_tac `Gb = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tb = tn with t_var := tn.t_var |+ (dv,{})` >>
  qabbrev_tac `tf = tb with t_mem := tb.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32}` >>
  suspend "prefix"
QED

Resume range_cons_entry_mods[prefix]:
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `lo <= w2n w` by (fs[allocas_from_def] >> first_x_assum drule >> simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def, for_code_def] >>
     first_x_assum drule >> decide_tac) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by fs[range_outer_frame_mods_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gb,tf)` by
    (`b = jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1) /\
      u = mstore (w2n w) (i2w (n1 + &k)) b /\ t = u with vs_inst_idx := 1 /\
      Gb = DRESTRICT G (COMPL {dv}) /\ tb = tn with t_var := tn.t_var |+ (dv,{}) /\
      tf = tb with t_mem := tb.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32}` by
       simp[Abbr `b`, Abbr `u`, Abbr `t`, Abbr `Gb`, Abbr `tb`, Abbr `tf`] >>
     drule_all range_cons_path_mods >>
     disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  qhdtm_x_assum `for_code` (strip_assume_tac o REWRITE_RULE [for_code_def]) >>
  `!x. x <> dv ==> lookup_var x t = lookup_var x s /\
                   FLOOKUP Gb x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, Abbr `u`, Abbr `b`, Abbr `Gb`, Abbr `tf`, Abbr `tb`,
         lookup_var_def, mstore_def, jump_to_def, update_var_def, FLOOKUP_UPDATE,
         FLOOKUP_DRESTRICT, op_taint_def] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_memory = (mstore (w2n w) (i2w (n1 + &k)) s).vs_memory /\
   t.vs_current_bb = sb0.cs_current_bb /\ t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
   ~t.vs_halted` by
    simp[Abbr `t`, Abbr `u`, Abbr `b`, mstore_def, jump_to_def, update_var_def] >>
  `ep.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\ ep.immutables = es.immutables /\
   ep.storage_trace = es.storage_trace` by simp[Abbr `ep`] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `ptr_covers Gb tf p t sz` by
    (qpat_assum `!x. x <> dv ==> _` (qspec_then `p` mp_tac) >>
     `p <> dv` by metis_tac[] >>
     simp[ptr_covers_def] >>
     qpat_assum `ptr_covers G tn p s sz` mp_tac >>
     simp[NoAsms, ptr_covers_def] >> strip_tac >>
     qpat_assum `lookup_var p s = SOME w` (full_simp_tac (srw_ss()) o single)) >>
  suspend "inputs"
QED

Resume range_cons_entry_mods[inputs]:
  `expr_sim_inv_mods mods bc cx (extend_local env id typ F) ep` by
    (simp[Abbr `ep`, Abbr `entry`] >> irule range_scope_inv_mods >> metis_tac[]) >>
  drule_all cenv_top_ext_declare_local >>
  disch_then (qspec_then `FEMPTY |+ (id,entry)` assume_tac) >>
  `bind (read_result cx (Value (IntV (n1 + &k)))) (push_scope_with_var id tyv)
     (es with gas_obs := []) = (INL (),ep) /\
   gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit_lbl incr_lbl)) ep /\
   body_const_cells_agree_mods mods cx (extend_local env id typ F) ep` by
    (irule range_scope_source_mods >>
     conj_tac >- simp[Abbr `ep`, Abbr `entry`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`lctx`,`rs`] >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `not_local_ptr cenv es.scopes p` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[] >>
     drule_all declare_local_ptr >> strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `not_local_ptr bc (FEMPTY::es.scopes) p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`sz`] >> simp[lookup_scopes_def]) >>
     qexists_tac `sb0` >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ep.storage_trace ==>
       stmt_state_rel H ctx func bc cx ep t /\
       storage_well_formed_on cx ep (FST H) /\ ghost_inv_at_mods (DF H) lo d bc cx ep Gb tf t` by
    suspend "horizons" >>
  suspend "frames"
QED

Resume range_cons_entry_mods[horizons]:
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H ep.storage_trace` mp_tac >>
     qpat_assum `ep.storage_trace = es.storage_trace` (rewrite_tac o single)) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (qspec_then `H` (drule_then assume_tac)) >>
  qhdtm_x_assum `range_header_mods` (strip_assume_tac o REWRITE_RULE [range_header_mods_def]) >>
  `not_local_ptr cenv es.scopes dv` by simp[] >>
  `stmt_state_rel H ctx func cenv cx es b /\
   ghost_inv_at_mods (DF H) lo d cenv cx es Gb tb b /\ ptr_covers Gb tb p b sz` by
    (irule range_condition_state_mods >>
     qexistsl_tac [`G`,`body_lbl`,`dv`,`s`,`sa`,`tn`] >>
     simp[Abbr `b`, Abbr `Gb`, Abbr `tb`]) >>
  `lookup_var p b = SOME w /\ b.vs_allocas = s.vs_allocas` by
    fs[Abbr `b`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `storage_well_formed_on cx ep (FST H)` by
    (`storage_well_formed_on cx ep (FST H) <=> storage_well_formed_on cx es (FST H)`
       suffices_by simp[] >>
     irule storage_well_formed_on_backends >> simp[Abbr `ep`]) >>
  `stmt_state_rel H ctx func bc cx ep t /\ ghost_inv_at_mods (DF H) lo d bc cx ep Gb tf t` by
    (irule range_store_state_ghost_mods >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ainst`,`b`,`cenv`,`es`,`id`,`p`,`sz`,`tb`,`tyv`,`w`,`n1 + &k`] >>
     simp[Abbr `ep`, Abbr `entry`, Abbr `t`, Abbr `u`, Abbr `tf`]) >>
  simp[]
QED

Resume range_cons_entry_mods[frames]:
  markerLib.RESUME_TAC >>
  `tf.t_mem SUBSET tn.t_mem` by simp[Abbr `tf`, Abbr `tb`, SUBSET_DEF] >>
  `!n b len. local_region bc ep.scopes t n b len ==>
     local_region cenv es.scopes s n b len \/ (b = w2n w /\ len = sz)` by
    (rpt gen_tac >> strip_tac >> irule range_new_local_regions >>
     qexistsl_tac [`bc`,`entry`,`ep`,`id`,`p`,`sa`,`t`] >> simp[]) >>
  qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `immutable_frame_mods func bc cx ep t` by
    (irule range_store_immutable_mods >>
     qexistsl_tac [`ainst`,`w2n w`,`cenv`,`es`,`s`,`sz`,`i2w (n1 + &k)`] >> simp[]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==> lookup_var x t = SOME z` by simp[] >>
  `return_buf_frame d cenv sa s` by
    (Cases_on `d` >- fs[return_buf_frame_def] >> PairCases_on `x` >>
     qpat_assum `return_buf_frame _ cenv sb0 s` mp_tac >>
     pure_rewrite_tac[return_buf_frame_def] >>
     disch_then (qx_choose_then `x` (qx_choose_then `slot` strip_assume_tac)) >>
     qexistsl_tac [`x`,`slot`] >> simp[]) >>
  `ret_pc_ok bc sb0 t /\ return_buf_frame d bc sb0 t` by
    (conj_tac
     >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
  `return_buf_sep d bc ep t` by
    (Cases_on `d` >- simp[return_buf_sep_def] >> PairCases_on `x` >>
     qpat_assum `return_buf_sep _ cenv es s` mp_tac >>
     pure_rewrite_tac[return_buf_sep_def, allocas_from_def] >> strip_tac >>
     conj_tac >- (qpat_assum `t.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single) >>
                  first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!n b len. local_region bc ep.scopes t n b len ==> _` (drule_then strip_assume_tac)
     >- (qpat_assum `!n b z. local_region cenv es.scopes s n b z ==> _`
           (drule_then ACCEPT_TAC)) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disj1_tac >>
     qpat_assum `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) ==> _`
       (qspecl_then [`ainst.inst_id`,`w2n w`,`sz`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `range_outer_frame_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [range_outer_frame_mods_def]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H0` assume_tac) >>
  drule_all body_full_path_alloca_history >> strip_tac >>
  `!fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v` by
    (map_every qx_gen_tac [`f`,`ins`,`v`] >> strip_tac >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `f` >> first_assum ACCEPT_TAC) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (drule_then mp_tac) >>
     simp[NoAsms, Abbr `t`, Abbr `u`, Abbr `b`, allocas_below_fmp_def, mstore_def, jump_to_def,
          update_var_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  suspend "anchor"
QED

Resume range_cons_entry_mods[anchor]:
  `not_local_ptr cenv es.scopes dv /\ p <> dv` by simp[] >>
  `!q. q <> dv ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> qpat_assum `!q. q <> dv ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa s0 bc ep t /\
   (!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
     (!nm b z. local_region cenv es0.scopes s0 nm b z ==> off + len <= b \/ b + z <= off) /\
     off <= i /\ i < off + len /\ i IN tf.t_mem ==> i IN tn0.t_mem)` by
    (drule_all range_entry_anchor_frame >>
     disch_then (qspec_then `entry` mp_tac) >>
     pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `ep.scopes = _` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[vyperStateTheory.evaluation_state_accfupds, combinTheory.K_THM] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`k`,`ep`,`t`,`Gb`,`tf`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  simp[Abbr `ep`, Abbr `entry`] >> metis_tac[]
QED

Finalise range_cons_entry_mods
