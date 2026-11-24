Theory bodyFullExtCallTargetOutcome
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds exprSimSource exprSimWordArgs exprSimHash exprSafeOperand
  gasOutcomeFullCompose fragGasOriginPtr fragGasSeqPtr contextRawReachable
  unitMemInv venomMemProps byte divides loweringPosts compileEnv valueEncoding
  vyperTyping vyperValue bodySimFull vyperState vyperInterpreter gasOutcomeFull
  bodyMemoryDefs exprSimDefs list

Theorem target_word_decode[local]:
  value_has_type (BaseTV AddressT) v /\
  expr_val_rel cx (BaseT AddressT) v op t ==>
  ?target aw. dest_AddressV v = SOME target /\ eval_operand op t = SOME aw /\
              w2w aw = target
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def, typed_val_to_w256_def] >>
  simp[dest_AddressV_def] >>
  `word_to_bytes (word_of_bytes_be l : address) T = l` by
    (simp[byteTheory.word_of_bytes_be_def] >>
     irule word_bytes_roundtrip >>
     simp[byteTheory.word_of_bytes_be_def, divides_def,
          fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  simp[] >>
  qspec_then `l` mp_tac
    (w2w_word_of_bytes_be_pad_left
     |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
  simp[compute_divides, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  disch_then (rewrite_tac o single o SYM) >> wordsLib.WORD_DECIDE_TAC
QED

Theorem extcall_singleton_source:
  eval_exprs cx [e] st =
    (sum_CASE (FST (bind (eval_expr cx e) (read_result cx) st))
       (\v. INL [v]) INR,
     SND (bind (eval_expr cx e) (read_result cx) st))
Proof
  rewrite_tac[eval_exprs_cons_action] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
  rename1 `bind (eval_expr cx e) (read_result cx) st = (raw,mid)` >>
  Cases_on `raw` >> simp[Once bind_def, bind_def, return_def, eval_exprs_nil]
QED

Theorem singleton_source_map[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_exprs cx [e]) (es,s,G,tn)
    (\H raw ee G' tn' t. ?res. raw = sum_CASE res (\v. INL [v]) INR /\
                               Q H res ee G' tn' t)
    (\H raw ee gt r. ?res. raw = sum_CASE res (\v. INL [v]) INR /\ R H res ee gt r)
Proof
  strip_tac >> ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
  qexists_tac `bind (eval_expr cx e) (read_result cx)` >> simp[] >>
  simp[extcall_singleton_source]
QED

Definition extcall_address_post_def:
  extcall_address_post (DF,lo,d,ctx,func) cenv cx env addr
    (es,sa,sb,s0,ao,G0,tn0) H res ee G tn t <=>
    ?v target aw.
      res = INL [v] /\ dest_AddressV v = SOME target /\
      eval_operand ao t = SOME aw /\ w2w aw = target /\ safe_operand sb ao /\
      expr_sim_inv cenv cx env ee /\
      expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
      expr_store_bound cx (BaseT AddressT) v ao t /\
      ptr_val_ok cx (BaseT AddressT) v ao G tn t /\
      return_buf_frame d cenv sb t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      ~t.vs_halted /\ ee.gas_obs = []
End

Theorem extcall_address_post_intro:
  expr_type addr = BaseT AddressT /\ expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  return_buf_frame d cenv sa s0 /\
  bind (eval_expr cx addr) (read_result cx) (es with gas_obs := obs) = (INL v,ee) /\
  ee.gas_obs = [] /\ ~t.vs_halted /\
  expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
  expr_store_bound cx (BaseT AddressT) v ao t /\
  ptr_val_ok cx (BaseT AddressT) v ao G tn t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  extcall_address_post (DF,lo,d,ctx,func) cenv cx env addr
    (es,sa,sb,s0,ao,G0,tn0) H (INL [v]) ee G tn t
Proof
  strip_tac >>
  `expr_body_pre cenv cx env addr (es with gas_obs := obs)` by simp[] >>
  `expr_sim_inv cenv cx env ee /\ value_has_type (BaseTV AddressT) v` by
    metis_tac[expr_body_pre_base_result] >>
  `is_word_type (expr_type addr)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  qhdtm_assum `expr_post`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >> simp[]) >>
  gvs[extcall_address_post_def] >> drule_all target_word_decode >> strip_tac >>
  qexists_tac `aw` >> gvs[safe_operand_def]
QED

Theorem extcall_request_head_halt_outcome:
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx [addr]) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v target aw.
      res = INL [v] /\ dest_AddressV v = SOME target /\
      eval_operand ao t = SOME aw /\ w2w aw = target /\ safe_operand sb ao /\
      expr_sim_inv cenv cx env ee /\
      expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
      expr_store_bound cx (BaseT AddressT) v ao t /\
      ptr_val_ok cx (BaseT AddressT) v ao G tn t /\
      return_buf_frame d cenv sb t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      ~t.vs_halted /\ ee.gas_obs = [])
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[cj 6 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT AddressT) addr es` by
    (gvs[body_exprs_full_ok_def] >> metis_tac[body_expr_full_ok_def]) >>
  `gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`ao`,
    `s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o MATCH_MP singleton_source_map) >>
  drule gas_outcome_full_post_source >> disch_then irule >>
  (reverse conj_tac
   >- (simp[] >> rpt gen_tac >> disch_then (qx_choose_then `raw` strip_assume_tac) >>
       Cases_on `raw` >> fs[halt_exit_def] >>
       metis_tac[expr_exit_success_map, stmtSimPropsTheory.expr_exit_INR_type])) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]` (strip_assume_tac o MATCH_MP eval_exprs_cons_cases)) >>
  gvs[eval_exprs_nil] >>
  `(ee with gas_obs := []) = ee` by simp[evaluation_state_component_equality] >>
  `post_value_type cenv addr = BaseT AddressT` by
    simp[post_value_type_word,is_word_type_def] >>
  fs[] >>
  `extcall_address_post (DF,lo,d,ctx,func) cenv cx env addr
     (es,sa,sb,s0,ao,G0,tn0) H (INL [v]) ee G' tn' t` by
    (irule extcall_address_post_intro >> simp[] >> qexists_tac `xs` >>
     qpat_assum `bind (eval_expr cx addr) _ _ = (INL _,_)`
       (ACCEPT_TAC o CONV_RULE (DEPTH_CONV ETA_CONV))) >>
  fs[extcall_address_post_def]
QED

(* The non-owning prefixes only need the ordinary exit projection. *)
Theorem extcall_request_head_outcome:
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx [addr]) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v target aw.
      res = INL [v] /\ dest_AddressV v = SOME target /\
      eval_operand ao t = SOME aw /\ w2w aw = target /\ safe_operand sb ao /\
      expr_sim_inv cenv cx env ee /\
      expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
      expr_store_bound cx (BaseT AddressT) v ao t /\
      ptr_val_ok cx (BaseT AddressT) v ao G tn t /\
      return_buf_frame d cenv sb t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      ~t.vs_halted /\ ee.gas_obs = [])
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z` by
    (rpt strip_tac >> drule frag_reachable_members >> disch_then drule >>
     strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM,
        unitTransformDefsTheory.dalloca_fmp_headroom_def] >> metis_tac[]) >>
  irule (Q.INST [`Q'` |-> `Q`,
                  `R` |-> `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
                    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)`]
           gas_outcome_full_post_mono) >>
  BETA_TAC >> rpt conj_tac
  >~ [`gas_outcome_full _ _ _ _ _ _ _ _`]
  >- (irule extcall_request_head_halt_outcome >>
      rpt (goal_assum (drule_at Any)) >> simp[] >>
      conj_tac >- (qexistsl [`shadow_func`,`shadow_sa`,`shadow_sb`] >> simp[]) >>
      qexists `tops` >> simp[]) >>
  simp[]
QED
