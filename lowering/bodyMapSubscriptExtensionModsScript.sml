(* Mapping Subscript joins, with the index IH used at its actual source state. *)
Theory bodyMapSubscriptExtensionMods
Ancestors
  bodyMapSubscriptStaticMods bodyMapSubscriptEndpointMods bodyMapSubscriptCodeMods
  bodyMapChildrenBindMods bodyMapHashSuffixMods bodyMapSelectNestedMods bodyMapSelectLeafAdapterMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach bodyFullTargetMappingRep
  bodyFullTargetMappingRun exprSimMapKey exprSimMapDefs exprSimHypsDefs exprSimDefs
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowCompileBase
  gasShadow gasShadowState gasContext gasOutcomeFullMods gasOutcomeFullPostMods
  exprLoweringProps exprLowering exprOperandVar compileEnv context
  vyperTypeEvalSoundness vyperTypeInvariants vyperTypeSystem vyperPlaceResultTyping
  vyperAST vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace freshWrites
  loweringPosts bodyFullShadowBodyInv bodyPtrDefs bodyMemoryDefs fragGasOriginPtr fragExec
  venomState ptrDiscipline vyperValue exprSimProps option list arithmetic

Theorem map_br_shape[local]:
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  eval_expr cx obj (es with gas_obs := obs) = (INL br,mid) ==>
  ?tr slot. br = HashMapRef tr slot kt vt
Proof
  strip_tac >>
  qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es with gas_obs := obs`,`INL br`,`mid`] mp_tac) >>
  (impl_tac >- fs[expr_map_pre_mods_def,expr_sim_inv_mods_def]) >> strip_tac >>
  qpat_x_assum `!vt. type_place_expr env obj = SOME vt ==> _`
    (qspec_then `HashMapT kt vt` (drule_at (Pos hd))) >>
  simp[eval_result_typed_def]
QED

Theorem map_key_child[local]:
  (expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es) /\
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  (!s res t. eval_expr cx obj s = (INL res,t) ==> body_expr_full_ok_mods mods exps cx idx) ==>
  !obs br mid. eval_expr cx obj (es with gas_obs := obs) = (INL br,mid) ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type idx) idx mid
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  qpat_assum `!s res t. eval_expr _ _ _ = _ ==> _` (drule_then assume_tac) >>
  drule_all_then strip_assume_tac map_br_shape >>
  qpat_x_assum `br = HashMapRef _ _ _ _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac map_base_success_mods >>
  qhdtm_x_assum `body_expr_full_ok_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
    _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
    (irule o cj 1 o SRULE [IMP_CONJ_THM, FORALL_AND_THM]) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Theorem map_key_post_type[local]:
  expr_type idx = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv ==> post_value_type cenv idx = kt
Proof
  strip_tac >>
  `is_word_type kt \/ is_bytestring_type kt` by
    (qpat_assum `hashmap_key_type kt` mp_tac >>
     qpat_assum `evaluate_type _ kt = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `kt` >> simp[hashmap_key_type_def,is_word_type_def,is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[hashmap_key_type_def,is_word_type_def,is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[is_word_type_def,is_bytestring_type_def,evaluate_type_def,AllCaseEqs()]) >>
  metis_tac[post_value_type_word,post_value_type_bytestring]
QED

(* Neither code split depends on the range being a value or a map. *)
Theorem map_code_suffix_extends[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (outop,sb) ==> cs_extends sn sb
Proof
  strip_tac >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt` >> gvs[cs_extends_refl] >>
     mp_tac (Q.SPECL [`key`,`F`,`sn`] ci_mono_compile_keccak256_key) >>
     simp[ci_mono_def]) >>
  `cs_extends sp sb` by
    (mp_tac (Q.SPECL [`bop`,`hashed`,`sp`] ci_mono_compile_mapping_subscript) >>
     simp[ci_mono_def]) >>
  metis_tac[cs_extends_trans]
QED

Theorem map_code_split[local]:
  place_type cenv obj = MapPT kt vt /\ ~copies_subscript_base cenv obj idx /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Subscript ann obj idx)) shadow_sa =
    (vv,shadow_sb) /\ gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?bvv sm key sn hashed sp outop shadow_sm shadow_sn.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript (vv_operand bvv) hashed sp = (outop,sb) /\
    vv = LocatedValue ann (mk_ptr outop
      (case vv_location bvv of SOME loc => loc | NONE => LocMemory)) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa = (bvv,shadow_sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type idx) (gas_shadow_expr idx)
      shadow_sm = (key,shadow_sn) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sn shadow_func /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_expr_mapping_subscript_parts >>
  `place_type (gas_shadow_env T cenv) (gas_shadow_expr obj) = MapPT kt vt /\
   ~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr obj) (gas_shadow_expr idx)` by
    fs[copies_subscript_base_def] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  qpat_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr _) _) _ = _`
    (mp_then (Pos hd) mp_tac compile_expr_mapping_subscript_parts) >>
  simp[gas_shadow_expr_type] >> strip_tac >>
  rename1 `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa = (bvS,smS)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr idx) smS = (keyS,snS)` >>
  `bvS = bvv /\ gas_shadow_state sm smS` by
    (mp_tac (Q.INST [`ty` |-> `ty`, `e` |-> `obj`, `sd` |-> `T`]
       gas_shadow_stmt_compile_expr_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `keyS = key /\ gas_shadow_state sn snS` by
    (mp_tac (Q.INST [`ty` |-> `expr_type idx`, `e` |-> `idx`, `sd` |-> `T`]
       gas_shadow_stmt_lower_value_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`smS`] mp_tac) >> simp[]) >>
  qexistsl_tac [`smS`,`snS`] >> simp[] >>
  qpat_assum `compile_expr cenv _ obj _ = (_,sm)`
    (mp_then Any strip_assume_tac (cj 1 compile_expr_grows)) >>
  qpat_assum `lower_value _ cenv _ idx _ = (_,sn)`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr obj) _ = (_,smS)`
    (mp_then Any strip_assume_tac (cj 1 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr idx) _ = (_,snS)`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  `cs_extends sn sb /\ cs_extends snS shadow_sb` by
    (conj_tac >> irule map_code_suffix_extends >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sm sb /\ cs_extends smS shadow_sb` by
    (conj_tac >> irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa smS shadow_func /\ fn_has_code smS shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code smS snS shadow_func /\ fn_has_code snS shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

Theorem map_old_operand[local]:
  (!x. bop = Var x ==> not_fresh_at sm x) /\ (!l. bop <> Label l) /\
  eval_operand bop t1 = SOME slot /\ op_taint tn1 bop = {} /\
  wb_frame cenv mid fin sm t1 it /\
  ghost_kept_at lo cenv mid sm (G1 : string |-> num # num) tn1 t1 Gi tni ==>
  eval_operand bop it = SOME slot /\ op_taint tni bop = {}
Proof
  Cases_on `bop` >> simp[eval_operand_def,op_taint_def,wb_frame_def,ghost_kept_at_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem map_pure_join[local]:
  pure_frame cenv func es sa s t /\ pure_frame cenv func mid sm t u /\
  wb_frame cenv es mid sa s t /\ wb_frame cenv mid fin sm t u /\
  sa.cs_next_id <= sm.cs_next_id /\ local_ptrs_reserved cenv sa ==>
  pure_frame cenv func es sa s u
Proof
  strip_tac >> irule pure_frame_trans >> simp[] >>
  qexistsl_tac [`mid`,`sm`,`t`] >> simp[] >>
  fs[wb_frame_def,locals_kept_def] >> metis_tac[]
QED

val select_exit = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : eval_result + exception) ee (gt : (string |-> num # num) # taint) q.
  expr_exit res q /\ halt_exit H cx ee res q /\
  (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s)``;

(* The continuation receives the one hashed-slot endpoint and both joined
   frames. Only the source selection and result representation differ. *)
Theorem map_subscript_extend_mods[local]:
  (expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es) /\
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\ place_type cenv obj = MapPT kt vt /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
  body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  (!s res t. eval_expr cx obj s = (INL res,t) ==> body_expr_full_ok_mods mods exps cx idx) /\
  expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es /\
  (!ex. A (INR ex) ==> expr_res_ok (INR ex)) /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Subscript ann obj idx)) shadow_sa =
    (vv,shadow_sb) /\ gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tr slot v fin it Gi tni outop u Gu tnu.
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
    fin.gas_obs = [] /\ ~it.vs_halted /\
    vv = LocatedValue ann (mk_ptr outop (slot_loc tr)) /\
    eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v)) /\
    op_taint tnu outop = {} /\ op_prov Gu outop = NONE /\
    wb_frame cenv es fin sa s0 u /\
    (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u) /\
    return_buf_frame d cenv sa u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx fin u /\ immutable_frame_mods func cenv cx fin u /\
      storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tnu u) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (select_result cx (expr_type obj) (HashMapRef tr slot kt vt) (ValueSubscript v))
      (fin,it,Gi,tni) Q ^select_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0) Q ^select_exit
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac map_code_split >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `contract_inv _ _ _ _ _`
       (mp_then (Pos hd) mp_tac body_inv_no_phi_mods) >>
     disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `!obs br mid. eval_expr cx obj (es with gas_obs := obs) = (INL br,mid) ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type idx) idx mid` by
    (rpt gen_tac >> strip_tac >> irule (Q.INST [`exps` |-> `exps`] map_key_child) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `module_body_inv _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_place_expr _ _ = _`)) >>
     goal_assum (drule_at (Pat `_ \/ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  irule (BETA_RULE mapping_children_bind_mods) >>
  simp[] >> suspend "bind_witnesses"
QED
Resume map_subscript_extend_mods[bind_witnesses]:
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`A`,`bvv`,`d`,`key`,`sa`,`shadow_func`,`shadow_sa`,
                `shadow_sm`,`shadow_sn`,`sm`,`sn`,`ty`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type idx = kt` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`bobs`,`br`,`mid`,`t1`,`G1`,`tn1`,`kobs`,`v`,`fin`,`it`,`Gi`,`tni`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "marked_endpoints"
QED

Resume map_subscript_extend_mods[marked_endpoints]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?tr slot kt' vt' tp p. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ idx mid _ _ _ fin _ _ _ /\ _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `mid with gas_obs := [] = mid /\ fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := bobs) = (INL br,mid)` by
    (qpat_assum `!tail. eval_expr cx obj (es with gas_obs := bobs ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th])) >>
  `bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := kobs) = (INL v,fin)` by
    (qpat_assum `!tail. bind _ _ (mid with gas_obs := kobs ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => rewrite_tac[th])) >>
  qpat_x_assum `br = HashMapRef _ _ _ _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac map_base_success_mods >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := kobs)` by
    fs[expr_body_pre_mods_def] >>
  qpat_assum `bind _ _ _ = (INL v,fin)`
    (mp_then (Pat `bind _ _ _ = _`) mp_tac map_index_read_type_mods) >>
  disch_then (qspecl_then [`mods`,`kt`,`env`,`cenv`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "hash_entry"
QED

Resume map_subscript_extend_mods[hash_entry]:
  qpat_x_assum `kt' = kt` SUBST_ALL_TAC >> qpat_x_assum `vt' = vt` SUBST_ALL_TAC >>
  drule_all_then assume_tac map_key_post_type >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `wb_frame cenv es mid sa s0 t1` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv mid fin sm t1 it /\ (~expr_has_effect idx ==> pure_frame cenv func mid sm t1 it)` by
    (qpat_assum `expr_post _ _ _ _ _ idx _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,expr_post_def,wb_frame_def] >> metis_tac[]) >>
  `!z. p.ptr_operand = Var z ==> not_fresh_at sm z` by
    (qpat_assum `compile_expr _ _ obj _ = (bvv,sm)`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[vv_operand_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule_all compile_mapping_operand_not_label >> simp[vv_operand_def]) >>
  `eval_operand p.ptr_operand it = SOME slot /\ op_taint tni p.ptr_operand = {}` by
    (irule map_old_operand >> simp[] >>
     qexistsl_tac [`G1`,`Gi`,`cenv`,`fin`,`lo`,`mid`,`sm`,`t1`,`tn1`] >> simp[]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> decide_tac) >>
  `!x. key = Var x \/ p.ptr_operand = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac
     >- (irule compile_lower_value_var >>
         qexistsl_tac [`cenv`,`idx`,`key`,`sm`,`expr_type idx`] >> asm_rewrite_tac[]) >>
     irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[] >> decide_tac) >>
  `allocas_from lo it /\ lo <= it.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ fin _ _ it` mp_tac >>
     simp[NoAsms,ghost_inv_at_mods_def] >> metis_tac[]) >>
  suspend "suffix"
QED

Resume map_subscript_extend_mods[suffix]:
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
      storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ idx mid _ _ _ fin _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `compile_mapping_subscript p.ptr_operand hashed sp = (outop,sb)` by
    fs[vv_operand_def] >>
  `expr_store_bound cx kt v key it` by
    ((qpat_assum `expr_store_bound _ (post_value_type _ idx) _ _ _` mp_tac >> simp[] >> (metis_tac[]))) >>
  drule_all_then assume_tac mapping_index_key_input >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
      ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> stmt_state_rel _ _ _ _ _ _ it /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `?u Gu tnu.
    eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v)) /\
    op_taint tnu outop = {} /\ op_prov Gu outop = NONE /\
    wb_frame cenv fin fin sn it u /\ pure_frame cenv func fin sn it u /\
    ghost_kept_at lo cenv fin sn Gi tni it Gu tnu /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ it.vs_alloca_next <= u.vs_alloca_next /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx fin u /\ immutable_frame_mods func cenv cx fin u /\
      ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tnu u)` by
    (drule_all_then strip_assume_tac
       (BETA_RULE (Q.INST [`P` |-> `\H. valid_horizon cx st0 H fin.storage_trace`,
          `H0` |-> `storage_trace_horizon fin.storage_trace`, `bop` |-> `p.ptr_operand`,
          `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
          (INST_TYPE [Type.alpha |-> ``:256``, Type.beta |-> ``:256``] mapping_suffix_full_run_mods))) >>
     qpat_x_assum `!sh pg. ?t hg tm. eval_operand outop t = _ /\ _`
       (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
     rename1 `eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v))` >>
     rename1 `op_taint tnu outop = {}` >> rename1 `op_prov Gu outop = NONE` >>
     qexistsl_tac [`u`,`Gu`,`tnu`] >> asm_rewrite_tac[]) >>
  suspend "joined_frames"
QED

Resume map_subscript_extend_mods[joined_frames]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   MAP FDOM es.scopes = MAP FDOM fin.scopes /\
   MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (qpat_assum `wb_frame cenv mid fin sm t1 it` mp_tac >>
     qpat_assum `wb_frame cenv es mid sa s0 t1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wb_frame_def,locals_kept_def]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
       (qpat_assum `eval_expr cx obj (es with gas_obs := bobs) = _` mp_tac >>
        qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        `storage_trace_frame (eval_expr cx obj)` by simp[cj 5 evaluate_storage_trace_frame] >>
        drule_all valid_horizon_frame >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `wb_frame cenv es fin sa s0 it /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`G1`,`mid`,`t1`,`sm`,`tn1`] >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `wb_frame cenv es fin sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`Gi`,`fin`,`it`,`sn`,`tni`] >> simp[]) >>
  `~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u` by
    (simp[] >> strip_tac >>
     `pure_frame cenv func es sa s0 it` by (irule map_pure_join >> simp[] >>
       qexistsl_tac [`fin`,`mid`,`sm`,`t1`] >> simp[]) >>
     irule map_pure_join >> simp[] >> qexistsl_tac [`fin`,`fin`,`sn`,`it`] >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv sa u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `wb_frame cenv es fin sa s0 u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wb_frame_def]) >>
  `vv = LocatedValue ann (mk_ptr outop (slot_loc tr))` by fs[vv_location_def] >>
  qpat_assum `!tr slot v fin it Gi tni outop u Gu tnu. _ ==> gas_outcome_full_mods _ _ _ _ (select_result _ _ _ _) _ _ _` irule >>
  asm_rewrite_tac[] >> qexistsl_tac [`Gu`,`outop`,`tnu`,`u`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> stmt_state_rel _ _ _ _ _ _ it /\ _ /\ storage_well_formed_on _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED
Finalise map_subscript_extend_mods


Theorem map_exception_ok[local]:
  !ex. expr_map_res_ok (INR ex) ==> expr_res_ok (INR ex)
Proof
  simp[expr_map_res_ok_def, expr_res_ok_def]
QED

val map_select_post = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : eval_result + exception) ee (G : string |-> num # num) (tn : taint) t.
  ?tr slot kt vt tp p.
    res = INL (HashMapRef tr slot kt vt) /\
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
    vv = LocatedValue tp p /\
    p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand t = SOME slot /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es ee s0 t /\
    (~expr_has_effect (Subscript ann obj idx) ==>
       pure_frame cenv func es sa s0 t) /\
    return_buf_frame d cenv sa t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem subscript_map_map_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
    (!s res t. eval_expr cx obj s = (INL res,t) ==>
       body_expr_full_ok_mods mods exps cx idx) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    expr_map_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es ==>
    expr_map_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac (cj 1 map_subscript_static_mods) >>
  rw[expr_map_sim_full_mods_def] >> rpt gen_tac >>
  `gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es` by
    first_assum ACCEPT_TAC >>
  irule (BETA_RULE (Q.INST
    [`mods` |-> `mods`, `exps` |-> `exps`, `cenv` |-> `cenv`, `cx` |-> `cx`,
     `env` |-> `env`, `ann` |-> `ann`, `obj` |-> `obj`, `idx` |-> `idx`,
     `es` |-> `es`, `kt` |-> `expr_type idx`, `ikt` |-> `ikt`,
     `ivt` |-> `ivt`, `vt` |-> `HashMapT ikt ivt`, `src` |-> `src`,
     `tops` |-> `tops`,
     `ctx` |-> `ctx`, `shadow_ctx` |-> `shadow_ctx`, `DF` |-> `DF`,
     `lo` |-> `lo`, `d` |-> `d`, `PG` |-> `PG`, `func` |-> `func`,
     `shadow_func` |-> `shadow_func`, `ty` |-> `ty`, `T` |-> `T`,
     `sa` |-> `sa`, `sb` |-> `sb`, `shadow_sa` |-> `shadow_sa`,
     `shadow_sb` |-> `shadow_sb`, `vv` |-> `vv`, `s0` |-> `s0`,
     `G0` |-> `G0`, `tn0` |-> `tn0`, `A` |-> `expr_map_res_ok`]
    map_subscript_extend_mods)) >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (ACCEPT_TAC map_exception_ok) >>
  TRY REFL_TAC >>
  qexistsl_tac [`d`,`env`,`exps`,`ikt`,`ivt`,`mods`,`sa`,`sb`,`shadow_func`,
                `shadow_sa`,`shadow_sb`,`src`,`tops`,`ty`,`vv`] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY REFL_TAC >>
  rpt gen_tac >> TRY (strip_tac) >>
  simp[mk_ptr_def] >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`^map_select_post`,`^select_exit`] >> BETA_TAC >>
  reverse conj_tac >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (irule mapping_select_map_mods >> simp[] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qexistsl_tac [`Gu`,`outop`,`tnu`,`u`] >> simp[] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`tr'`,`slot'`,`kt`,`vt`] >> simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `vv` >> gvs[mk_ptr_def]
QED

Theorem subscript_map_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es kt vt.
    (!s res t. eval_expr cx obj s = (INL res,t) ==>
       body_expr_full_ok_mods mods exps cx idx) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt /\
    expr_map_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es ==>
    expr_vv_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac (cj 2 map_subscript_static_mods) >>
  rw[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  `gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es` by
    first_assum ACCEPT_TAC >>
  irule (BETA_RULE (Q.INST
    [`mods` |-> `mods`, `exps` |-> `exps`, `cenv` |-> `cenv`, `cx` |-> `cx`,
     `env` |-> `env`, `ann` |-> `ann`, `obj` |-> `obj`, `idx` |-> `idx`,
     `es` |-> `es`, `kt` |-> `expr_type idx`, `vt` |-> `Type ann`,
     `src` |-> `src`, `tops` |-> `tops`,
     `ctx` |-> `ctx`, `shadow_ctx` |-> `shadow_ctx`, `DF` |-> `DF`,
     `lo` |-> `lo`, `d` |-> `d`, `PG` |-> `PG`, `func` |-> `func`,
     `shadow_func` |-> `shadow_func`, `ty` |-> `ty`, `T` |-> `T`,
     `sa` |-> `sa`, `sb` |-> `sb`, `shadow_sa` |-> `shadow_sa`,
     `shadow_sb` |-> `shadow_sb`, `vv` |-> `vv`, `s0` |-> `s0`,
     `G0` |-> `G0`, `A` |-> `expr_vv_res_ok`]
    map_subscript_extend_mods)) >>
  conj_tac
  >- simp[expr_vv_res_ok_def, expr_res_ok_def]
  >- (conj_tac
      >- first_assum ACCEPT_TAC
      >- (gvs[] >>
          conj_tac
          >- (qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
              rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              disj1_tac >> first_assum ACCEPT_TAC)
          >- (qexistsl_tac [`d`,`sa`,`sb`,`shadow_func`,`shadow_sa`,`shadow_sb`,`ty`,`vv`] >>
              ((rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC) >-
               (rpt gen_tac >> strip_tac >>
                irule gas_outcome_full_mods_post_source >>
                qexistsl_tac
                  [`mapping_leaf_select_post_mods DF lo d ctx func cenv cx ann obj idx
                      es sa sb s0 vv G0 tn0`,
                   `mapping_select_exit_mods ctx cx`] >>
                reverse conj_tac >-
                  (conj_tac
                   >- simp[mapping_select_exit_mods_def]
                   >- (irule mapping_select_leaf_adapter_mods >>
                       rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
                       >- simp[GSYM IS_SOME_EXISTS]
                       >> qexistsl_tac [`Gu`,`outop`,`tnu`,`u`] >> simp[] >>
                       rpt strip_tac >>
                       qpat_assum `!H. valid_horizon _ _ H _ ==> _`
                         (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
                simp[mapping_leaf_select_post_mods_def])) >>
              rpt strip_tac >>
              qpat_assum `!H. valid_horizon _ _ H _ ==> _`
                (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)))
QED

