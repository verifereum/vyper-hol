(* Caller-relative frames at the reached raw-call data and header cuts. *)
Theory bodyRawBytesReachedFramesMods
Ancestors
  bodyBopBytestringBindMods bodyFullPredsMods bodyFullPostsMods
  exprSimSource exprSimWordArgs exprSimConvertFromBytes exprSafeOperand
  wordArgsPtr exprLoweringProps compilerInstructionSuffix exprOperandVar
  bodyMemoryDefs bodyPtrDefs ptrDiscipline loweringPosts venomState
  vyperTypeExprSoundness vyperTypeEvalCaseProofs abiValueEncoding
  vyperStorageFootprint vyperState vyperValue vyperAST list finite_map
  compileEnv exprBodyPreProps loweringShapeRules loweringShapeDefs
Libs monadsyntax

val _ = Parse.hide "ptr";
val _ = Parse.hide "base";
val _ = Parse.hide "size";

Triviality reached_forced_source_cut:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,ee) ==>
  body_exprs_full_ok_mods mods exps cx rest /\ MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
      first_x_assum irule >>
      drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Triviality address_post_preserved:
  expr_val_rel cx (BaseT AddressT) av addr t /\
  (!w. eval_operand addr t = SOME w ==> eval_operand addr u = SOME w) ==>
  expr_val_rel cx (BaseT AddressT) av addr u
Proof
  simp[expr_val_rel_def,is_word_type_def] >> metis_tac[]
QED

Triviality data_cut_address:
  wb_frame cenv esA esD s1 tA tD /\ ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\
  safe_operand s1 addr /\ expr_val_rel cx (BaseT AddressT) av addr tA /\
  op_taint tnA addr = {} /\ op_prov GA addr = NONE ==>
  expr_val_rel cx (BaseT AddressT) av addr tD /\
  op_taint tnD addr = {} /\ op_prov GD addr = NONE
Proof
  strip_tac >>
  `(!w. eval_operand addr tA = SOME w ==> eval_operand addr tD = SOME w) /\
   op_taint tnD addr = {} /\ op_prov GD addr = NONE` by
    (Cases_on `addr` >>
     fs[safe_operand_def,eval_operand_def,op_taint_def,op_prov_def,ghost_kept_at_def] >>
     metis_tac[wb_frame_vars]) >>
  simp[] >> irule address_post_preserved >> goal_assum (drule_at Any) >> simp[]
QED

Triviality data_cut_caller_frames:
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM esA.scopes /\ ci_mono sa s1 /\ ci_mono s1 s2 /\
  wb_frame cenv es esA sa s0 tA /\ wb_frame cenv esA esD s1 tA tD /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA /\
  ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\
  return_buf_frame d cenv sa s0 /\ s0.vs_alloca_next <= tA.vs_alloca_next /\
  tA.vs_alloca_next <= tD.vs_alloca_next ==>
  wb_frame cenv es esD sa s0 tD /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD /\
  return_buf_frame d cenv sa tD /\ return_buf_frame d cenv s2 tD /\
  s0.vs_alloca_next <= tD.vs_alloca_next
Proof
  strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   s1.cs_next_var <= s2.cs_next_var` by fs[ci_mono_def] >>
  conj_asm1_tac
  >- (irule wb_frame_trans >> qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
      qpat_assum `wb_frame cenv es esA sa s0 tA` (irule_at Any) >>
      qexists_tac `s1` >> simp[]) >>
  conj_tac
  >- metis_tac[ghost_kept_at_wb_trans] >>
  `s0.vs_alloca_next <= tD.vs_alloca_next /\ sa.cs_next_var <= s2.cs_next_var` by decide_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x tD = SOME w` by
    (rpt strip_tac >> irule wb_frame_vars >>
     qpat_assum `wb_frame cenv es esD sa s0 tD` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >>
      qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >>
      qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >> simp[]) >>
  simp[]
QED

val postA = ``\(H : (bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
  expr_store_bound cx (post_value_type cenv a) av addr tA /\
  tA.vs_current_bb = s1.cs_current_bb /\ tA.vs_inst_idx = LENGTH s1.cs_current_insts /\
  alloca_history func tA /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tA) /\
  s0.vs_alloca_next <= tA.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx esA GA tnA tA /\
  ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA /\
  (~is_word_type (post_value_type cenv a) ==> ptr_buf_ok cenv a addr GA tA) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA``;

val postD = ``\(H : (bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e esA s1 s2 tA esD vD data tD /\
  expr_store_bound cx (post_value_type cenv e) vD data tD /\
  tD.vs_current_bb = s2.cs_current_bb /\ tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
  alloca_history func tD /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tD) /\
  tA.vs_alloca_next <= tD.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx esD GD tnD tD /\
  ptr_val_ok cx (post_value_type cenv e) vD data GD tnD tD /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e data GD tD) /\
  ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD``;

Theorem raw_bytes_reached_data_frames_mods:
  body_exprs_full_ok_mods mods exps cx (a::e::kws) /\
  expr_body_pre_mods mods cenv cx env a es /\ expr_body_pre_mods mods cenv cx env e esA /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type a = BaseT AddressT /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
  (!tail. bind (eval_expr cx a) (read_result cx) (es with gas_obs := obsA ++ tail) =
          (INL av,esA with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (esA with gas_obs := obsD ++ tail) =
          (INL vD,esD with gas_obs := tail)) /\
  esA.gas_obs = [] /\ esD.gas_obs = [] /\ storage_trace_domain cx st0 esD.storage_trace /\
  (!H. valid_horizon cx st0 H esA.storage_trace ==> (^postA) H) /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==> (^postD) H) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ safe_operand s1 addr /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 ==>
  ?bs. vD = BytesV bs /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) = SOME (BaseTV (BytesT (Dynamic cap))) /\
    body_exprs_full_ok_mods mods exps cx kws /\ expr_sim_inv_mods mods cenv cx env esD /\
    body_const_cells_agree_mods mods cx env esD /\ MAP FDOM es.scopes = MAP FDOM esD.scopes /\
    (!H. valid_horizon cx st0 H esD.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H esD.storage_trace ==>
      expr_post_mods H ctx func cenv cx e esA s1 s2 tA esD (BytesV bs) data tD /\
      ghost_inv_at_mods (DF H) lo d cenv cx esD GD tnD tD) /\
    expr_store_bound cx (post_value_type cenv e) (BytesV bs) data tD /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) data GD tnD tD /\
    tD.vs_current_bb = s2.cs_current_bb /\ tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func tD /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tD) /\
    expr_val_rel cx (BaseT AddressT) av addr tD /\ op_taint tnD addr = {} /\ op_prov GD addr = NONE /\
    wb_frame cenv es esD sa s0 tD /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD /\
    return_buf_frame d cenv sa tD /\ return_buf_frame d cenv s2 tD /\
    s0.vs_alloca_next <= tD.vs_alloca_next
Proof
  BETA_TAC >> strip_tac >>
  qpat_assum `expr_body_pre_mods mods cenv cx env a es`
    (mp_then Any (drule_all_then (qspec_then `st0` (map_every assume_tac o CONJUNCTS)))
      bop_bytestring_operand_source_mods) >>
  qpat_assum `expr_body_pre_mods mods cenv cx env e esA`
    (mp_then Any (drule_all_then (qspec_then `st0` (map_every assume_tac o CONJUNCTS)))
      bop_bytestring_operand_source_mods) >>
  drule_all_then strip_assume_tac reached_forced_source_cut >>
  qpat_assum `body_exprs_full_ok_mods _ _ _ (e::kws)`
    (mp_then Any (drule_all_then strip_assume_tac) reached_forced_source_cut) >>
  `?bs. vD = BytesV bs /\
     evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ esD` (mp_then Any assume_tac expr_sim_inv_mods_env) >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     qpat_x_assum `value_runtime_typed env (expr_type e) vD` mp_tac >>
     simp[value_runtime_typed_def] >> rpt strip_tac >>
     drule_then SUBST_ALL_TAC evaluate_type_base_result >>
     drule_then strip_assume_tac dynamic_bytes_value_typed >> simp[] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H esD.storage_trace ==> valid_horizon _ _ _ esA.storage_trace`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H esA.storage_trace ==> valid_horizon _ _ _ es.storage_trace`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H esD.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H esA.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `expr_post_mods _ _ _ _ _ a _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _` (mp_then Any assume_tac expr_post_frame) >>
  qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _` (mp_then Any assume_tac expr_post_frame) >>
  `is_word_type (expr_type a)` by simp[is_word_type_def] >>
  `post_value_type cenv a = BaseT AddressT` by simp[] >>
  `expr_val_rel cx (BaseT AddressT) av addr tA /\
   op_taint tnA addr = {} /\ op_prov GA addr = NONE` by
    (qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `ptr_val_ok _ _ av addr _ _ _`
       (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
     conj_tac
     >- (qpat_assum `post_value_type cenv a = BaseT AddressT`
           (fn th => pure_once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
     fs[is_word_type_def]) >>
  drule_all_then strip_assume_tac data_cut_address >>
  drule_all_then strip_assume_tac data_cut_caller_frames >>
  qexists_tac `bs` >> gvs[]
QED

Theorem raw_bytes_header_saved_entry_mods:
  wb_frame cenv es esD sa s0 tD /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD /\
  return_buf_frame d cenv sa tD /\ s0.vs_alloca_next <= tD.vs_alloca_next /\
  ci_mono sa s2 /\ ci_mono s1 s2 /\ safe_operand s1 addr /\
  expr_val_rel cx (BaseT AddressT) av addr tD /\ op_taint tnD addr = {} /\ op_prov GD addr = NONE /\
  emit_op MLOAD [data] s2 = (len,s3) /\ emit_op ADD [data; Lit 32w] s3 = (ptr,s4) /\
  (!x. not_fresh_at s2 x ==>
     lookup_var x t4 = lookup_var x tD /\ FLOOKUP G4 x = FLOOKUP GD x /\
     op_taint tn4 (Var x) = op_taint tnD (Var x)) /\
  eval_operand len t4 = SOME (n2w (LENGTH bs)) /\ eval_operand ptr t4 = SOME (n2w (b+32)) /\
  op_taint tn4 len = {} /\ op_prov G4 len = NONE /\ op_taint tn4 ptr = {} /\
  (?p base size. ptr = Var p /\ op_prov G4 ptr = SOME (base,size) /\
    base <= b+32 /\ b+32+LENGTH bs <= base+size /\
    (bs <> [] ==> ptr_covers G4 tn4 p t4 (LENGTH bs))) /\
  t4.vs_alloca_next = tD.vs_alloca_next /\
  (!sa es s0. sa.cs_next_var <= s2.cs_next_var /\ wb_frame cenv es esD sa s0 tD ==>
     wb_frame cenv es esD sa s0 t4) /\
  (!sa es s0 G0 tn0. sa.cs_next_var <= s2.cs_next_var /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD ==>
     ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4) /\
  (!sa df. sa.cs_next_var <= s2.cs_next_var /\ return_buf_frame df cenv sa tD ==>
     return_buf_frame df cenv sa t4 /\ return_buf_frame df cenv s4 t4) ==>
  ?p base size. ptr = Var p /\
    ci_mono sa s4 /\ ci_mono s2 s4 /\
    wb_frame cenv es esD sa s0 t4 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4 /\
    return_buf_frame d cenv sa t4 /\ return_buf_frame d cenv s4 t4 /\
    s0.vs_alloca_next <= t4.vs_alloca_next /\
    EVERY (safe_operand s4) [addr; len; Var p] /\ expr_val_rel cx (BaseT AddressT) av addr t4 /\
    eval_operand len t4 = SOME (n2w (LENGTH bs)) /\ eval_operand (Var p) t4 = SOME (n2w (b+32)) /\
    EVERY (\op. op_taint tn4 op = {}) [addr; len; Var p] /\
    op_prov G4 addr = NONE /\ op_prov G4 len = NONE /\ op_prov G4 (Var p) = SOME (base,size) /\
    base <= b+32 /\ b+32+LENGTH bs <= base+size /\
    (bs <> [] ==> ptr_covers G4 tn4 p t4 (LENGTH bs))
Proof
  strip_tac >>
  `safe_operand s2 addr` by (irule safe_operand_mono >> qexists_tac `s1` >> fs[ci_mono_def]) >>
  `(!w. eval_operand addr tD = SOME w ==> eval_operand addr t4 = SOME w) /\
   op_taint tn4 addr = {} /\ op_prov G4 addr = NONE` by
    (Cases_on `addr` >> fs[safe_operand_def,eval_operand_def,op_taint_def,op_prov_def]) >>
  `expr_val_rel cx (BaseT AddressT) av addr t4` by
    (irule address_post_preserved >> goal_assum (drule_at Any) >> simp[]) >>
  `ci_mono s2 s3` by (qspecl_then [`MLOAD`,`[data]`,`s2`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono s3 s4` by (qspecl_then [`ADD`,`[data;Lit 32w]`,`s3`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono s2 s4` by (irule ci_mono_trans >> qexists_tac `s3` >> simp[]) >>
  `ci_mono sa s4` by (irule ci_mono_trans >> qexists_tac `s2` >> simp[]) >>
  `sa.cs_next_var <= s2.cs_next_var` by fs[ci_mono_def] >>
  qpat_assum `!sa es s0. _ ==> wb_frame _ _ _ _ _ t4` (drule_all_then assume_tac) >>
  qpat_assum `!sa es s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ G4 tn4`
    (drule_all_then assume_tac) >>
  qpat_assum `!sa df. _ ==> return_buf_frame _ _ _ t4 /\ _`
    (drule_all_then strip_assume_tac) >>
  `safe_operand s4 addr` by (irule safe_operand_mono >> qexists_tac `s2` >> fs[ci_mono_def]) >>
  `safe_operand s4 len` by
    (irule safe_operand_mono >> qexists_tac `s3` >>
     qpat_assum `emit_op MLOAD _ s2 = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     fs[ci_mono_def,safe_operand_def]) >>
  `safe_operand s4 ptr` by
    (qpat_assum `emit_op ADD _ s3 = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     gvs[safe_operand_def]) >>
  qexistsl_tac [`p`,`base`,`size`] >> gvs[]
QED
