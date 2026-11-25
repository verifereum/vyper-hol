(* Transport the captured runtime-code array to the reached key cursor.
   The representation witness and the actual source place are kept separately. *)
Theory bodyArrayFramedCodeBaseMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  bodyArrayFramedCodeInputsMods bodyLocalCopyPhysicalRhsMods
  exprSimSubscriptArrayFrame exprSimSubscriptArrayOrigin exprSimSubscriptArraySource
  exprBodyPreProps exprOperandVar exprBopSimProps exprSimProps exprSimWordArgs wordArgsPtr
  vyperEvalExprPreservesScopesDom vyperTyping vyperTypeValues vyperTypeSystem vyperTypeInvariants
  valueTypingMemoryProps loweringPosts bodyFullPostsMods bodyPtrDefs exprSimHypsDefs
  vyperInterpreter vyperAST vyperState vyperValue compileEnv context freshWrites
  vyperStorageFootprint ptrDiscipline finite_map words

Theorem framed_code_key_source[local]:
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  (!t r t'. eval_expr cx idx t = (INL r,t') ==>
     t'.scopes = t.scopes /\ t'.immutables = t.immutables) ==>
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables
Proof
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[evaluation_state_accfupds]
QED

Theorem framed_code_base_shape[local]:
  vv_location bvv = SOME LocCode /\
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?p etv av w. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode /\
    eval_operand p.ptr_operand s = SOME w /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    read_result cx raw mid = (INL (ArrayV av),mid) /\
    value_has_type (ArrayTV etv bd) (ArrayV av)
Proof
  Cases_on `bvv` >> simp[vv_location_def] >> strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def, immutable_holds_mods_def] >> strip_tac >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def, evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem framed_code_base_operand[local]:
  compile_expr cenv ty obj sa = (LocatedValue a p,sm) /\
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ p.ptr_location = LocCode /\
  local_ptrs_reserved cenv sa /\ sm.cs_next_var <= st2.cs_next_var ==>
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x /\ not_fresh_at st2 x) /\
  (!l. p.ptr_operand <> Label l)
Proof
  strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  `vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode` by
    simp[vv_location_def] >>
  drule_all_then assume_tac framed_code_subscript_base_pre >>
  irule compile_array_pointer_not_label >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `env` >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  fs[expr_sim_inv_mods_def] >> first_assum ACCEPT_TAC
QED

Theorem framed_code_read_frame[local]:
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  read_result cx raw mid = (INL v,mid) ==>
  read_result cx raw fin = (INL v,fin)
Proof
  strip_tac >>
  `FST (read_result cx raw fin) = FST (read_result cx raw mid)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  Cases_on `read_result cx raw fin` >> gvs[] >>
  drule read_result_state >> simp[]
QED

Theorem framed_code_place_frame[local]:
  vv_place_ptr_mods cenv cx mid s raw (LocatedValue a p) /\
  p.ptr_location = LocCode /\ fin.immutables = mid.immutables /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s ==>
  vv_place_ptr_mods cenv cx fin it raw (LocatedValue a p)
Proof
  Cases_on `raw` >>
  TRY (rename1 `vv_place_ptr_mods _ _ mid s (PlaceR pl) _` >> Cases_on `pl`) >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, slot_loc_def] >>
  strip_tac >> gvs[]
QED

Theorem framed_code_rep_frame[local]:
  vv_holds_mods cenv cx a raw (LocatedValue a p) mid s /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s ==>
  vv_holds_mods cenv cx a raw (LocatedValue a p) fin it
Proof
  strip_tac >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def, immutable_holds_mods_def] >> strip_tac >>
  `immutable_holds (cenv with ce_module := src) cx a raw w fin it` by
    (irule immutable_holds_runtime_frame >> simp[] >>
     qexistsl_tac [`mid`,`s`] >> simp[]) >>
  simp[] >> qexistsl_tac [`src`,`tops`] >> simp[]
QED

Theorem framed_code_ptr_frame[local]:
  ptr_vv_ok cx a raw (LocatedValue a p) mid G1 tn1 s /\
  p.ptr_location = LocCode /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni ==>
  ptr_vv_ok cx a raw (LocatedValue a p) fin Gi tni it
Proof
  simp[ptr_vv_ok_def] >> strip_tac >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  Cases_on `p.ptr_operand` >>
  gvs[op_taint_def, op_prov_def] >> metis_tac[]
QED

Theorem framed_code_vv_wb_frame[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s ==>
  wb_frame cenv es mid sa s0 s
Proof
  rewrite_tac[vv_post_mods_def, wb_frame_def] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem framed_code_expr_wb_frame[local]:
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  wb_frame cenv mid fin sm s it
Proof
  simp[expr_post_mods_def] >> strip_tac >> drule expr_post_frame >> simp[]
QED

Theorem framed_code_captured_endpoint[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw (LocatedValue (ArrayT et bd) p) s /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  post_value_type cenv obj = ArrayT et bd /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s ==>
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin raw (LocatedValue (ArrayT et bd) p) it
Proof
  strip_tac >>
  drule_then assume_tac framed_code_vv_wb_frame >>
  drule_then assume_tac framed_code_expr_wb_frame >>
  `wb_frame cenv es fin sa s0 it` by (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 it` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 s` by fs[vv_post_mods_def] >>
     `pure_frame cenv func mid sm s it` by
       (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
        drule_all expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> simp[] >> qexistsl_tac [`mid`,`sm`,`s`] >> fs[wb_frame_def]) >>
  `stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
   storage_well_formed_on cx fin (FST H)` by fs[expr_post_mods_def, expr_post_def] >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `post_value_type cenv obj = _` (fn ty_eq =>
    qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [ty_eq])) >>
  drule_all_then assume_tac framed_code_rep_frame >>
  drule_all_then assume_tac framed_code_place_frame >>
  simp[vv_post_mods_def, post_value_type_def, vyperASTTheory.expr_type_def,
       vv_at_def, vv_storage_live_def, expr_has_effect_thm] >>
  fs[vv_at_def, wb_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem framed_code_old_operand_frame[local]:
  eval_operand op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  wb_frame cenv mid fin sm s it ==>
  eval_operand op it = SOME w
Proof
  strip_tac >> irule eval_operand_frame >> simp[] >>
  qexistsl_tac [`sm`,`s`] >> fs[wb_frame_def]
QED

Theorem framed_code_nonstorage[local]:
  eval_expr cx obj ss = (INL raw,mid) /\
  (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) ==>
  !tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)
Proof
  metis_tac[]
QED

Theorem framed_code_cut_entry[local]:
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  valid_horizon cx st0 H fin.storage_trace ==>
  stmt_state_rel H ctx func cenv cx es s0
Proof
  strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem framed_code_reached_base_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_code_case_mods cenv cx obj idx bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  ?p etv av w.
    bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode /\ loc = LocCode /\
    (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
    fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    read_result cx raw mid = (INL (ArrayV av),mid) /\
    read_result cx raw fin = (INL (ArrayV av),fin) /\
    eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand it = SOME w /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x /\ not_fresh_at st2 x) /\
    (!l. p.ptr_operand <> Label l) /\
    ptr_vv_ok cx (ArrayT et bd) raw bvv fin Gi tni it /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
       vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
         es sa st2 s0 fin raw bvv it /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it)
Proof
  strip_tac >>
  qpat_x_assum `linked_subscript_array_context_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qpat_x_assum `subscript_array_framed_code_case_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [subscript_array_framed_code_case_mods_def]) >>
  qpat_assum `array_nocopy_cut_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `vv_location bvv = SOME LocCode` by
    (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn cut =>
       qpat_assum `!ty st. vv_location _ = _`
         (qspecl_then [`ty`,`sa`] (ACCEPT_TAC o PURE_REWRITE_RULE [cut,pairTheory.FST])))) >>
  drule_all_then strip_assume_tac framed_code_key_source >>
  drule_all_then assume_tac framed_code_nonstorage >>
  `post_value_type cenv obj = ArrayT et bd` by simp[] >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then (qx_choosel_then [`p`,`etv`,`av`,`w`] strip_assume_tac) framed_code_base_shape >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac framed_code_base_operand >>
  suspend "endpoint"
QED

Resume framed_code_reached_base_mods[endpoint]:
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> qpat_assum `!x. p.ptr_operand = Var x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac framed_code_expr_wb_frame >>
  drule_all_then assume_tac framed_code_old_operand_frame >>
  drule_all_then assume_tac framed_code_read_frame >>
  `ptr_vv_ok cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) fin Gi tni it` by
    (qpat_assum `post_value_type cenv obj = ArrayT et bd` (fn ty_eq =>
      qpat_assum `ptr_vv_ok _ _ _ _ mid _ _ _` (assume_tac o REWRITE_RULE [ty_eq])) >>
     drule_all framed_code_ptr_frame >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by (drule_all framed_code_cut_entry >> simp[]) >>
  drule_then assume_tac framed_code_vv_wb_frame >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[evaluation_state_accfupds]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
     simp[] >> qexistsl_tac [`G1`,`mid`,`mid`,`s`,`sm`,`tn1`] >> simp[]) >>
  qexistsl_tac [`p`,`etv`,`av`,`w`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx es s0` by (drule_all framed_code_cut_entry >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  simp[] >> irule framed_code_captured_endpoint >> simp[] >>
  goal_assum (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
Finalise framed_code_reached_base_mods

(* Use the completed linked post, not an assumed equality of data sections. *)
Theorem framed_code_reached_view_mods:
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin raw (LocatedValue (ArrayT et bd) p) it /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  ptr_vv_ok cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) fin Gi tni it /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) ==>
  op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE /\
  ?owner owner_tops w.
    ALOOKUP cenv.ce_modules owner = SOME owner_tops /\
    eval_operand p.ptr_operand it = SOME w /\
    immutable_holds (cenv with ce_module := owner) cx (ArrayT et bd) raw w fin it /\
    val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) it.vs_data_section /\
    w2n w + type_memory_size (ArrayTV etv bd) <= LENGTH it.vs_data_section
Proof
  strip_tac >>
  drule local_copy_raw_code_source_mods >>
  simp[post_value_type_def, vyperASTTheory.expr_type_def]
  >> (metis_tac[])
QED
