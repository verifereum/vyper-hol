(* Advance the linked machine entry at the endpoint of a forced word read. *)
Theory bodySliceWordEntryMods
Ancestors
  bodyMemoryDefs bodyFullPostsMods exprSimFullBundleProps bodyFullIfExpReach
  exprLoweringProps loweringPosts compileEnv exprSimHypsDefs vyperStorageTrace
  vyperStorageFootprint vyperState
Libs monadsyntax

val wp = ``\e es sa sb s0 ee v op t G0 tn0 G tn (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val cut = ``\e es sa sb s0 ee v op t G0 tn0 G tn marks.
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ^wp e es sa sb s0 ee v op t G0 tn0 G tn H)``;

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;

Theorem slice_word_next_entry_mods:
  ^entry es sa s0 G0 tn0 /\ ^cut e es sa sb s0 ee v op t G0 tn0 G tn marks /\
  sa.cs_next_var <= sb.cs_next_var ==>
  ^entry ee sb t G tn /\
  ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)
Proof
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  conj_tac
  >- (simp[] >> rpt conj_tac
      >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
      >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
      >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
      >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
          fs[expr_post_mods_def,expr_post_def])
      >- (rpt strip_tac >> qpat_assum `!fn inst u. frag_reachable _ _ t fn inst u ==> _`
            (drule_then ACCEPT_TAC)) >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      fs[expr_post_mods_def,expr_post_def]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn frame =>
    qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))
QED
