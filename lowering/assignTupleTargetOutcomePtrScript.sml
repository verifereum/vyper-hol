(* An effectful tuple destination precedes its actual write continuation. *)
Theory assignTupleTargetOutcomePtr
Ancestors
  bodyPtrPopSeamTargetFrag bodyPtrPopTargetDefs gasSummaryComposePtr gasExemptCert
  bodyPtrDefs exprSimDefs loweringPosts stmtSimDeclGas stmtSimProps gasOutcomeMarkedPtr
  rawCallKeywordPrefixPtr
  vyperInterpreter vyperState compileEnv loweringStateRelDefs

Theorem tuple_target_write_outcome_ptr:
  target_sim_ptr d ctx PG func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p ee H tt u.
    target_post ctx func cenv cx es sa sm s ee (PlaceR p) (Type ty) r u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee H tt u /\ target_ptr_ok cenv (PlaceR p) r H tt u /\
    ghost_kept cenv es sa G tn s H tt ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (write_place cx p v) (ee,u,H,tt) Q (\res ee gt rr. expr_exit res rr)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (assign_tuple_targets cx (BaseTarget bt) v) (es,s,G,tn)
    Q (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >>
  drule pop_target_frag_ptr_of_sim >>
  simp[pop_target_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >> metis_tac[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> metis_tac[]) >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]
QED

(* A write itself reads no source gas; its destination may have read gas. *)
Theorem tuple_target_store_runtime_outcome_ptr:
  target_sim_ptr d ctx PG func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p ee H tt u.
    target_post ctx func cenv cx es sa sm s ee (PlaceR p) (Type ty) r u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee H tt u /\ target_ptr_ok cenv (PlaceR p) r H tt u /\
    ghost_kept cenv es sa G tn s H tt ==>
    ?ee' H' tt' t.
      (!tail. write_place cx p v (ee with gas_obs := tail) =
        (INL (),ee' with gas_obs := tail)) /\
      gas_path_ptr (cx_dead cx) 0 ctx func PG H tt u 0 H' tt' (OK t) /\
      Q (INL ()) (ee' with gas_obs := []) H' tt' t) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (assign_tuple_targets cx (BaseTarget bt) v) (es,s,G,tn)
    Q (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >> mp_tac (SPEC_ALL tuple_target_write_outcome_ptr) >>
  (impl_tac >-
   (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `!p ee H tt u. _` drule_all >>
    disch_then (qx_choosel_then [`ee'`,`H'`,`tt'`,`t`] strip_assume_tac) >>
    simp[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
    qexists_tac `[]` >> disj1_tac >>
    simp[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
    qexistsl_tac [`INL ()`,`ee'`,`H'`,`tt'`,`OK t`] >> simp[])) >>
  asm_rewrite_tac[]
QED

(* Marked source executions expose the concrete gas-observation input. *)
Theorem gas_outcome_ptr_source_witness:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G,tn)
    (\res ee H tt t. Q res ee H tt t /\
      ?obs. source (es with gas_obs := obs) = (res,ee)) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  rpt gen_tac >> strip_tac >> simp[] >>
  qexists_tac `gas_explicit marks s.vs_gas_readings` >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_ptr_def] >>
  disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]
QED

(* The source equation also supplies semantic target typing and writability. *)
Theorem tuple_target_witnessed_write_outcome_ptr:
  target_sim_ptr d ctx PG func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p ee H tt u.
    (?obs. eval_target_place cx bt (es with gas_obs := obs) = (INL p,ee)) /\
    target_post ctx func cenv cx es sa sm s ee (PlaceR p) (Type ty) r u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee H tt u /\ target_ptr_ok cenv (PlaceR p) r H tt u /\
    ghost_kept cenv es sa G tn s H tt ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (write_place cx p v) (ee,u,H,tt) Q (\res ee gt rr. expr_exit res rr)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (assign_tuple_targets cx (BaseTarget bt) v) (es,s,G,tn)
    Q (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >>
  drule pop_target_frag_ptr_of_sim >>
  simp[pop_target_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  drule gas_outcome_ptr_source_witness >> strip_tac >>
  simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >> metis_tac[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> metis_tac[]) >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]
QED

(* A successful counted target prefix also supplies its open runtime state. *)
Theorem tuple_target_ready_write_outcome_ptr:
  target_sim_ptr d ctx PG func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p ee H tt u.
    ~u.vs_halted /\
    (?obs. eval_target_place cx bt (es with gas_obs := obs) = (INL p,ee)) /\
    target_post ctx func cenv cx es sa sm s ee (PlaceR p) (Type ty) r u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee H tt u /\ target_ptr_ok cenv (PlaceR p) r H tt u /\
    ghost_kept cenv es sa G tn s H tt ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (write_place cx p v) (ee,u,H,tt) Q (\res ee gt rr. expr_exit res rr)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (assign_tuple_targets cx (BaseTarget bt) v) (es,s,G,tn)
    Q (\res ee gt rr. expr_exit res rr)
Proof
  strip_tac >>
  drule pop_target_frag_ptr_of_sim >>
  simp[pop_target_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  drule gas_outcome_ptr_nonhalted >> strip_tac >>
  drule gas_outcome_ptr_source_witness >> strip_tac >>
  simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >> metis_tac[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> metis_tac[]) >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]
QED
