(* The raw Array body post is still in the declared scope. Recover the
   two distinct pre-loop frames and the live item at the same cursor. *)
Theory bodyForArrayBodyPopMods
Ancestors
  bodyForArrayHeaderMods bodyForRangeBodySuffixMods bodyForRangePopTypingMods
  bodyForRangePopCellsMods bodyFullForRange stateRelProj localPtrsProps
  stmtFragPtr bodyMemoryDefs exprSimOperands freshWrites stmtSimProps stmtSimDefs
  bodyPtrDefs bodySimFull bodyFullShadowBodyInv bodyFullPostsMods bodyFullPredsMods
  bodyForRangeHeaderMods exprSimHypsDefs loweringPosts compileEnv venomState venomInst
  vyperInterpreter
  vyperEvalPreservesScopes vyperStorageFootprint vyperState
  venomMemDefs loweringStateRelDefs finite_map list arithmetic

val _ = Parse.hide "body";

Theorem array_pop_scope[local]:
  push_scope_with_var id tyv v es = (INL (),ep) /\
  lookup_scopes id es.scopes = NONE /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  cenv_top_ext c bc ep.scopes /\ cenv_top_ext bc cb fin.scopes ==>
  ?sc rest. fin.scopes = sc::rest /\
    (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) /\
    cenv_top_ext c cb fin.scopes
Proof
  strip_tac >>
  `ep.scopes = (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                 value := v; popped := []|>)) :: es.scopes` by
    gvs[push_scope_with_var_def, return_def] >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def] >> strip_tac >>
  Cases_on `fin.scopes` >> fs[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> strip_tac >> irule range_full_body_no_shadow >>
      goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[]) >>
  irule cenv_top_ext_trans >> qexistsl_tac [`bc`,`ep.scopes`] >> simp[]
QED

Theorem array_pop_live_var[local]:
  not_fresh_at sbCopy x /\ lookup_var x z = SOME w /\
  (!q a. not_fresh_at sbCopy q /\ lookup_var q z = SOME a ==>
         lookup_var q t = SOME a) /\
  (!q. not_fresh_at sbCopy q ==> FLOOKUP G1 q = FLOOKUP G q /\
       op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  lookup_var x t = SOME w /\ FLOOKUP G1 x = FLOOKUP G x /\
  op_taint tn1 (Var x) = op_taint tn (Var x)
Proof
  strip_tac >> simp[]
QED

Theorem array_pop_item[local]:
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) es G tn z /\
  not_fresh_at sbCopy xd /\ not_local_ptr c ee.scopes xd /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [xd] /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func c cx ee t /\ z.vs_alloca_next <= t.vs_alloca_next /\
  (!q a. not_fresh_at sbCopy q /\ lookup_var q z = SOME a ==>
         lookup_var q t = SOME a) /\
  (!q. not_fresh_at sbCopy q ==> FLOOKUP G1 q = FLOOKUP G q /\
       op_taint tn1 (Var q) = op_taint tn (Var q)) /\
  (!aid row. FLOOKUP z.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) ==>
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee G1 tn1 t
Proof
  strip_tac >> qhdtm_x_assum `for_array_item_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  drule_all_then strip_assume_tac array_pop_live_var >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  simp[for_array_item_mods_def] >>
  conj_tac >- (gvs[ptr_covers_def] >> qexists_tac `dw` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `regions_disjoint (w2n dw) cap b sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM inst (fn_insts func)`)) >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem array_pop_capture[local]:
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) es tn z /\
  alloca_frame c em saExpr u bc ep z /\
  alloca_frame bc ep sbCopy z cb fin t /\
  saExpr.cs_next_id <= sbCopy.cs_next_id /\ saLen.cs_next_var <= sbCopy.cs_next_var /\
  cenv_top_ext c cb fin.scopes /\ fin.scopes = sc::rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) /\
  ee = fin with scopes := rest /\ z.vs_alloca_next <= t.vs_alloca_next /\
  (!q a. not_fresh_at sbCopy q /\ lookup_var q z = SOME a ==>
         lookup_var q t = SOME a) /\
  (!aid row. FLOOKUP z.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!aid off len i. FLOOKUP z.vs_allocas aid = SOME (off,len) /\ aid < sbCopy.cs_next_id /\
     (!nm b sz. local_region bc ep.scopes z nm b sz ==> off+len <= b \/ b+sz <= off) /\
     off <= i /\ i < off+len /\ i IN tn1.t_mem ==> i IN tn.t_mem) ==>
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn1 t
Proof
  strip_tac >> qhdtm_x_assum `for_array_capture_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_capture_frame_mods_def]) >>
  `alloca_frame c em saExpr u cb fin t` by
    (match_mp_tac (Q.INST [`c1` |-> `bc`, `e1` |-> `ep`, `s1` |-> `z`,
                            `sa1` |-> `sbCopy`] alloca_frame_trans) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[for_array_capture_frame_mods_def] >>
  conj_tac
  >- (qpat_x_assum `ee = _` SUBST_ALL_TAC >>
      irule alloca_frame_pop >>
      conj_tac >- (qexists_tac `sc` >> simp[]) >>
      qexists_tac `cb` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!q a. not_fresh_at sbCopy q /\ _ ==> _` irule >>
      conj_tac >- simp[] >>
      irule not_fresh_at_mono >> qexists_tac `saLen` >> simp[]) >>
  match_mp_tac (Q.INST [`c1` |-> `bc`, `e1` |-> `ep`, `s1` |-> `z`,
                         `sa1` |-> `sbCopy`, `tn1` |-> `tn`] alloca_taint_kept_trans) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Old-variable ghosts are carried at the length cut, while the item and
   current index only need to have been defined before the body cut. *)
Theorem for_array_body_pop_live_mods:
  push_scope_with_var id tyv v es = (INL (),ep) /\
  eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
  ee = fin with scopes := TL fin.scopes /\
  lookup_scopes id es.scopes = NONE /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods c cx env es /\
  cenv_top_ext c bc ep.scopes /\ cenv_top_ext bc cb fin.scopes /\
  sa.cs_next_id <= sbCopy.cs_next_id /\ sa.cs_next_var <= sbCopy.cs_next_var /\
  saExpr.cs_next_id <= sbCopy.cs_next_id /\ saLen.cs_next_var <= sbCopy.cs_next_var /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [xd] /\ fn_inst_ids_distinct func /\
  not_local_ptr c ee.scopes xd /\ not_fresh_at sbCopy xd /\
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) es G tn z /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 es G tn z /\
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) es tn z /\
  alloca_frame c es0 sa s0 bc ep z /\ alloca_frame c em saExpr u bc ep z /\
  ret_pc_ok c sa z /\ return_buf_frame d c sa z /\ return_buf_frame d bc sbCopy z /\
  stmt_state_rel H ctx func cb cx fin t /\ immutable_frame_mods func cb cx fin t /\
  storage_well_formed_on cx fin (FST H) /\ return_buf_sep d cb fin t /\
  ghost_inv_at_mods (DF H) lo d cb cx fin G1 tn1 t /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  z.vs_alloca_next <= t.vs_alloca_next /\
  (!q w. not_fresh_at sbCopy q /\ lookup_var q z = SOME w ==> lookup_var q t = SOME w) /\
  (!aid row. FLOOKUP z.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!q. not_fresh_at sbCopy q ==> FLOOKUP G1 q = FLOOKUP G q /\
        op_taint tn1 (Var q) = op_taint tn (Var q)) /\
  alloca_frame bc ep sbCopy z cb fin t /\
  (!aid off len i. FLOOKUP z.vs_allocas aid = SOME (off,len) /\ aid < sbCopy.cs_next_id /\
     (!nm b sz. local_region bc ep.scopes z nm b sz ==> off+len <= b \/ b+sz <= off) /\
     off <= i /\ i < off+len /\ i IN tn1.t_mem ==> i IN tn.t_mem) ==>
  stmt_state_rel H ctx func c cx ee t /\ immutable_frame_mods func c cx ee t /\
  storage_well_formed_on cx ee (FST H) /\ return_buf_sep d c ee t /\
  ghost_inv_at_mods (DF H) lo d c cx ee G1 tn1 t /\
  ret_pc_ok c sa t /\ return_buf_frame d c sa t /\ return_buf_frame d c sbCopy t /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G1 tn1 t /\
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn1 t /\
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee G1 tn1 t /\
  (!q w. not_fresh_at sbCopy q /\ lookup_var q z = SOME w ==>
        lookup_var q t = SOME w /\ FLOOKUP G1 q = FLOOKUP G q /\
        op_taint tn1 (Var q) = op_taint tn (Var q)) /\
  (!q. not_fresh_at saLen q ==> FLOOKUP G1 q = FLOOKUP G q /\
       op_taint tn1 (Var q) = op_taint tn (Var q)) /\
  ((raw = INL () \/ raw = INR ContinueException) ==>
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods c cx env ee /\
    lookup_scopes id ee.scopes = NONE)
Proof
  strip_tac >> drule_all_then strip_assume_tac array_pop_scope >>
  `ee = fin with scopes := rest` by simp[] >>
  `fin = ee with scopes := sc::ee.scopes` by simp[evaluation_state_component_equality] >>
  `ep.scopes <> [] /\ (!n. n IN FDOM (HD ep.scopes) ==> lookup_scopes n (TL ep.scopes) = NONE)` by
    (qpat_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
     simp[NoAsms, push_scope_with_var_def, return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  qhdtm_assum `for_array_outer_frame_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_outer_frame_mods_def, range_outer_frame_mods_def]) >>
  suspend "outer"
QED

Resume for_array_body_pop_live_mods[outer]:
  `stmt_state_rel H ctx func c cx ee t /\ immutable_frame_mods func c cx ee t /\
   storage_well_formed_on cx ee (FST H) /\ return_buf_sep d c ee t /\
   ghost_inv_at_mods (DF H) lo d c cx ee G1 tn1 t /\ ret_pc_ok c sa t /\
   return_buf_frame d c sbCopy t /\
   range_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G1 tn1 t` by
    (irule range_body_pop_frame_mods >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G`,`bc`,`body`,`cb`,`ep with gas_obs := gs`,`raw`,`sc`,`tn`,`z`] >>
     qpat_assum `fin = ee with scopes := _` (pure_rewrite_tac o single o SYM) >>
     `ee.scopes = rest` by
       (qpat_assum `ee = fin with scopes := rest` (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
     qpat_assum `ee.scopes = rest` (pure_rewrite_tac o single) >>
     qpat_assum `fin.scopes = sc::rest` (pure_once_rewrite_tac o single o SYM) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `fin = ee with scopes := _` kall_tac >>
  `!q w. not_fresh_at sa q /\ lookup_var q z = SOME w ==> lookup_var q t = SOME w` by
    (rpt strip_tac >> qpat_assum `!q w. not_fresh_at sbCopy q /\ _ ==> _` irule >>
     simp[] >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d c sa t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`c`,`z`,`sa`] >> simp[]) >>
  suspend "live"
QED

Resume for_array_body_pop_live_mods[live]:
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[ghost_inv_at_mods_def] >>
  pure_rewrite_tac[for_array_outer_frame_mods_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule array_pop_capture >>
      goal_assum (drule_at (Pat `alloca_frame _ _ _ _ bc ep z`)) >>
      goal_assum (drule_at (Pat `for_array_capture_frame_mods _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `alloca_frame bc ep _ z cb fin t`)) >>
      qexistsl_tac [`rest`,`sc`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule array_pop_item >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
      qexistsl_tac [`G`,`es`,`sbCopy`,`tn`,`z`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!q w. not_fresh_at sbCopy q /\ _ ==> _`
        (qspecl_then [`q`,`w`] mp_tac) >>
      qpat_assum `!q. not_fresh_at sbCopy q ==> _` (qspec_then `q` mp_tac) >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `not_fresh_at sbCopy q` by (irule not_fresh_at_mono >> qexists_tac `saLen` >> simp[]) >>
      simp[]) >>
  suspend "typing"
QED

Resume for_array_body_pop_live_mods[typing]:
  disch_tac >>
  `eval_stmts cx body
     ((es with scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                     value := v; popped := []|>))::es.scopes) with gas_obs := gs) = (raw,fin)` by
    (qpat_assum `eval_stmts cx body _ = _` mp_tac >>
     qpat_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
     simp[NoAsms, push_scope_with_var_def, return_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     `es with scopes updated_by CONS (FEMPTY |+ (id,<|assignable := F; type := tyv;
                     value := v; popped := []|>)) =
        es with scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                     value := v; popped := []|>))::es.scopes` by
       simp[NoAsms, evaluation_state_component_equality] >>
     pop_assum (pure_once_rewrite_tac o single) >> simp[NoAsms]) >>
  `body_const_cells_agree_mods mods cx env (fin with scopes := rest)` by
    (irule range_body_pop_cells_mods >>
     conj_tac >- (qexists_tac `sc` >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >> first_assum ACCEPT_TAC) >>
  `expr_sim_inv_mods mods c cx env (fin with scopes := rest) /\ lookup_scopes id rest = NONE` by
    (irule range_body_pop_typing_mods >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `sc` >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ee = fin with scopes := rest` (pure_rewrite_tac o single) >> simp[]
QED

Finalise for_array_body_pop_live_mods
