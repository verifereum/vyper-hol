(* Joint scalar top-level AugAssign: compose the checked phase interfaces. *)
Theory augAssignFullToplevelCase
Ancestors
  augAssignFullToplevelRead augAssignFullToplevelCode augAssignFullToplevelPrefix
  augAssignFullToplevelContinue augAssignFullSource augAssignFullSourcePrefix
  gasOutcomeFullRunning gasOutcomeFullCompose gasOutcomeFull
  bodyFullPreds bodySimFull bodyFullShared bodyPtrDefs
  stmtSimAugAssignStorage stmtSimAugAssign augAssignStorageFieldSource
  exprSimSource exprSimUnwrap exprSimHypsDefs exprSimProps exprBopSimProps
  exprSimTopLevelProps accountsRelProps loweringPosts emitHelperProps
  exprLoweringProps freshWrites gasShadow vyperStorageFootprint loweringStateRelDefs
  vyperTypeValues vyperTyping vyperInterpreter vyperState venomState list finite_map

Theorem augassign_toplevel_source_join_full[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  storage_trace_domain cx st0 root_es.storage_trace /\
  (!H. valid_horizon cx st0 H root_es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) [] (OK t,Gload,tnload)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (root_es,t,Gload,tnload)
    (\H res ee G tn u. ?v. res = INL v /\ Qrhs H v ee G tn u)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!marks v mid G1 tn1 u.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (root_es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> Qrhs H v mid G1 tn1 u) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0) tvt bop cur v))
        (write_place cx (StoragePlace tr (n2w slot) tvt))) (mid,u,G1,tn1) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule augassign_pure_prefix_full >>
  qexistsl_tac [`Gload`, `cur`, `root_es`, `[StorageRoot tr slot tvt]`,
    `StoragePlace tr (n2w slot) tvt`, `tvt`, `t`, `tnload`] >>
  conj_tac
  >- (drule_all eval_target_place_toplevel >> strip_tac >>
      gen_tac >> conj_tac
      >- simp[] >>
      simp[read_place_def, place_type_value_def] >>
      metis_tac[read_storage_slot_storage_trace, read_storage_slot_gas_obs]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule augassign_rhs_bind_full >> qexists_tac `Qrhs` >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Theorem augassign_toplevel_read_ready_full[local]:
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) ==>
  word_value_type ty /\ word_value_type (expr_type e) /\ is_word_type ty /\
  type_slot_size tvt = 1 /\ well_formed_type_value tvt /\
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)) /\
  ?cur. read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
    (!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
      storage_holds cx tr ty (Value cur) (n2w slot) es s0 /\
      key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {})
Proof
  strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty /\ type_slot_size tvt = 1` by
    metis_tac[word_value_type_word, word_type_slot_size] >>
  `well_formed_type_value tvt` by metis_tac[evaluate_type_well_formed_type_value] >>
  `0 < type_slot_size tvt` by simp[] >>
  drule_all observed_storage_toplevel_clean_read_full >> strip_tac >>
  `valid_horizon cx st0
    (storage_trace_horizon (es.storage_trace ++ [StorageRoot tr slot tvt])) es.storage_trace` by
    (fs[storage_trace_domain_def] >> metis_tac[valid_horizon_append]) >>
  `stmt_state_rel (storage_trace_horizon (es.storage_trace ++ [StorageRoot tr slot tvt]))
    ctx func cenv cx es s0` by metis_tac[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem compile_augassign_toplevel_case_full:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx (TopLevelNameTarget (src,id)) s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  well_formed_type env.type_defs ty /\ cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME vtyp /\ is_word_type vtyp /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)))
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) es
Proof
  strip_tac >> rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `!st. eval_target_place cx (TopLevelNameTarget (src,id)) st =
    (INL (StoragePlace tr (n2w slot) tvt),
     st with storage_trace := st.storage_trace ++ [StorageRoot tr slot tvt])` by
    metis_tac[eval_target_place_toplevel] >>
  reverse (Cases_on `storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt])`)
  >- (irule gas_outcome_full_bad_intro >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `G0`, `PG`, `tn0`, `[]`, `s0`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil] >>
      irule augassign_storage_place_bad_root >> metis_tac[]) >>
  drule_all augassign_toplevel_read_ready_full >> strip_tac >>
  qabbrev_tac `root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]` >>
  `expr_body_pre cenv cx env e root_es /\ storage_trace_domain cx st0 root_es.storage_trace` by
    simp[Abbr `root_es`] >>
  drule_all augassign_toplevel_shadow_code_full >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `?out. cur' = Var out` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `cur' = Var out` SUBST_ALL_TAC >>
  `root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]` by
    simp[Abbr `root_es`] >>
  `!H. valid_horizon cx st0 H root_es.storage_trace ==>
    storage_holds cx tr ty (Value cur) (n2w slot) es s0 /\
    key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}` by (simp[Abbr `root_es`] >> metis_tac[]) >>
  drule_all augassign_toplevel_rhs_entry_full >>
  disch_then (qspecl_then [`RetQ`, `PG`] (qx_choosel_then [`t`, `Gload`, `tnload`] strip_assume_tac)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_tac o HO_MATCH_MP gas_outcome_full_value_running) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qrun _` >>
  irule augassign_toplevel_source_join_full >>
  qexistsl_tac [`Gload`, `\H v ee G tn u. Qrun H (INL v) ee G tn u`,
    `cur`, `id_str`, `root_es`, `slot`, `t`, `tnload`, `tr`, `ts`, `tvt`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (simp[Abbr `Qrun`, NoAsms] >> rpt gen_tac >> strip_tac >>
      `value_has_type tvt cur` by metis_tac[vyperTypeStatePreservationTheory.read_storage_slot_success_type] >>
      `word_value cur` by metis_tac[word_value_type_typed] >>
      `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
      irule augassign_toplevel_continue_full >> reverse (rpt conj_tac)
      >- (qexistsl_tac [`Gload`, `e`, `env`, `es`, `gas_explicit marks t.vs_gas_readings`,
        `id`, `id_str`, `rhs`, `out`, `res`, `root_es`, `s1`, `s2`, `s3`, `src`, `t`, `tnload`, `ts`] >>
      rpt conj_tac >> metis_tac[]) >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule)
  >- simp[Abbr `root_es`, NoAsms]
  >> rpt (first_assum ACCEPT_TAC) >> qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `Qrun`, NoAsms]
QED
