(* Bind the actual forced source read of a linked Extract32 expression. *)
Theory bodyExtractSourceBindMods
Ancestors
  bodyExtractOperandCutsMods exprSimExtract32Source bodyFullIfExpReach bodyBranchCellFrameMods
  bodyForcedStorageFrameMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasOutcomeFullPostPathMods gasExemptCertMods haltExitProj stmtSimProps exprSimDefs
  vyperStorageTrace vyperStorageFootprint vyperState
Libs monadsyntax

val forced = ``bind (eval_expr cx src) (read_result cx)``;
val next = ``\v. do
  w <- bind (eval_expr cx off) (read_result cx);
  result <- lift_sum (evaluate_type_builtin cx Extract32 ret
    [expr_type src;expr_type off] [v;w]);
  return (Value result)
  od``;
val outcome = ``gas_outcome_full_mods
  (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0``;
val value_outcome = Term.inst [Type.alpha |-> ``:value``] outcome;
val vv_outcome = Term.inst [Type.alpha |-> ``:eval_result``] outcome;
val exit = ``\(H : (bool # bytes32 # type_value) list # num list)
    res ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val value_exit = Term.inst [Type.alpha |-> ``:value``] exit;
val vv_exit = Term.inst [Type.alpha |-> ``:eval_result``] exit;
val src_post = ``\(H:(bool # bytes32 # type_value) list # num list)
  (res:value + exception) (mid:evaluation_state) (G1:string |-> num # num)
  (tn1:taint) (s:venom_state). ?v. res = INL v /\ srcQ H v mid G1 tn1 s``;
val headroom = ``!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u``;
val marked = ``es with gas_obs := gas_explicit marks s0.vs_gas_readings``;

Theorem extract32_source_bind_mods:
  (^value_outcome) ^forced (es,s0,G0,tn0) ^src_post ^value_exit /\
  body_exprs_full_ok_mods mods exps cx [src;off] /\
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!marks bs mid G1 tn1 s.
     (!tail. ^forced (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL (BytesV bs),mid with gas_obs := tail)) /\
     ^forced ^marked = (INL (BytesV bs),mid) /\
     mid.gas_obs = [] /\ ~s.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
     ^headroom /\ (!H. valid_horizon cx st0 H mid.storage_trace ==> srcQ H (BytesV bs) mid G1 tn1 s) /\
     body_expr_full_ok_mods mods exps cx off /\
     expr_body_pre_mods mods cenv cx env off mid /\
     body_const_cells_agree_mods mods cx env mid /\ LENGTH bs <= m /\
     MAP FDOM es.scopes = MAP FDOM mid.scopes ==>
     (^vv_outcome) ((^next) (BytesV bs)) (mid,s,G1,tn1) Q ^vv_exit) ==>
  (^vv_outcome) (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]))
    (es,s0,G0,tn0) Q ^vv_exit
Proof
  strip_tac >> PURE_REWRITE_TAC[eval_expr_extract32_vv_bind] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame ^forced`]
  >- MATCH_ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >- simp[storage_trace_frame_bind_all,
          bodyForcedStorageFrameModsTheory.bop_forced_storage_frame,
          storage_trace_frame_lifts,storage_trace_frame_return] >>
  qexists_tac `\H res mid G1 tn1 s. (^src_post) H res mid G1 tn1 s /\
                                    ~s.vs_halted /\ mid.gas_obs = [] /\ ^headroom` >>
  BETA_TAC >> conj_tac >- suspend "reached" >>
  suspend "strengthen_post"
QED

Resume extract32_source_bind_mods[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `^forced ^marked = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  `expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) ^marked /\
   body_const_cells_agree_mods mods cx env ^marked` by simp[] >>
  drule_all_then strip_assume_tac extract32_offset_source_mods >>
  qpat_x_assum `MAP FDOM (^marked).scopes = _` (assume_tac o SRULE []) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `BytesV bs` >> pure_rewrite_tac[REFL_CLAUSE, AND_CLAUSES] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> srcQ H (BytesV bs) mid G1 tn1 s` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o PURE_REWRITE_RULE [sumTheory.INL_11]) >>
     qpat_x_assum `BytesV bs = _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!marks bs mid G1 tn1 s. _` (irule o BETA_RULE) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (qexists_tac `marks` >> conj_tac >> first_assum ACCEPT_TAC))
QED

Resume extract32_source_bind_mods[strengthen_post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res mid G1 tn1 s. (^src_post) H res mid G1 tn1 s /\ ^headroom`,
                `^value_exit`] >> BETA_TAC >> reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      goal_assum (drule_at Any) >> BETA_TAC >> rpt gen_tac >> strip_tac >>
      conj_tac >- (qexists_tac `v` >> conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `gas_origin_ptr_path _ _ _ _`
        (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          gas_origin_ptr_path_dalloca_fmp_headroom) >>
      disch_then (fn th => qx_genl_tac [`ff`,`ii`,`z`] >> strip_tac >>
        qspecl_then [`ff`,`ii`,`z`] mp_tac th) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise extract32_source_bind_mods
