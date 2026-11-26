(* Bind the actual typed target run before any AugAssign read or RHS. *)
Theory bodyAugTargetBindMods
Ancestors
  bodyWriteTargetStageMods gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods fragGasOriginPtr augAssignFullRhsSaved
  vyperStorageTrace vyperStorageFootprint vyperExprNoControl vyperInterpreter
  exprSimDefs stmtSimDefs gasContext targetPlaceSimCases vyperState
Libs monadsyntax

val target_suffix = ``\p. do
  cur <- read_place cx p;
  ptv <- place_type_value cx p;
  tv <- eval_expr cx e;
  v <- read_result cx tv;
  u <<- (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0);
  res <- lift_sum (evaluate_binop u ptv bop cur v);
  write_place cx p res
od``;

val augassign_exit = ``\(H : (bool # 256 word # type_value) list # num list) res ee
    (gt : (string, num # num) fmap # taint) r.
  (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
  halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
     allocas_below_fmp s)``;

Theorem augassign_target_source[local]:
  eval_stmt cx (AugAssign ty bt bop e) =
    bind (eval_target_place cx bt) ^target_suffix
Proof
  simp[Once evaluate_def]
QED

Theorem augassign_target_admissible[local]:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR exc)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`,`gs`] >> simp[augassign_target_source, Once bind_def]) >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED

(* Strengthen only the normal alternative, keeping its own path. *)
Theorem augassign_target_post_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\ ee.gas_obs = [] /\
       ?cm. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) cm (OK t,G',tn')) R
Proof
  rw[Once gas_outcome_full_mods_def] >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> qexists_tac `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem augassign_typed_target_bind_mods:
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  (!marks p mid Gt tt t.
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL p,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!id path. p = MemoryPlace id path ==>
      ?entry v. lookup_scopes id mid.scopes = SOME entry /\
                evaluate_subscripts entry.type entry.value path = INL v) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
        mid (PlaceR p) (Type ty) dst G0 tn0 Gt tt t /\
      ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) cm (OK t,Gt,tt)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (^target_suffix p) (mid,t,Gt,tt) Q ^augassign_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (AugAssign ty bt bop e))
    (es,s0,G0,tn0) Q ^augassign_exit
Proof
  strip_tac >> drule_then assume_tac augassign_target_admissible >>
  qpat_x_assum `write_place_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_place_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`ty`,`sa`,`sp`,
    `shadow_sa`,`shadow_sp`,`dst`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (mp_tac o MATCH_MP augassign_target_post_path) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ ChildR` >>
  rewrite_tac[augassign_target_source] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_place >>
      goal_assum (drule_at Any) >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >>
      rpt (irule storage_trace_frame_bind_all >>
           simp[evaluate_storage_trace_frame, storage_trace_frame_read_result,
                storage_trace_frame_read_place, storage_trace_frame_place_type,
                storage_trace_frame_lifts, storage_trace_frame_write_place] >>
           rpt gen_tac)) >>
  qexists_tac `ChildQ` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `ChildR`, Excl "AND_IMP_INTRO"] >>
      rpt gen_tac >> strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
      rename1 `expr_exit (INR exc) r` >> qexists_tac `exc` >>
      conj_tac >- REFL_TAC >>
      irule augassign_expr_exit_to_stmt_exit >> simp[] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type, haltExitProjTheory.halt_exit_INR_type]) >>
  suspend "target_reached"
QED

Resume augassign_typed_target_bind_mods[target_reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`,NoAsms] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac))
    strip_assume_tac) >>
  disj1_tac >> qexists_tac `p` >> fs[] >>
  first_x_assum irule >> conj_tac
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise augassign_typed_target_bind_mods
