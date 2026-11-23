(* The selected ternary's source/physical continuation at its arm exit. *)
Theory entryCreateIfExpOutcome
Ancestors
  entryCreateFocusSpec entryCreateScopedBind bodyFullIfExpPrepare
  vyperStorageTrace vyperStorageFootprint fragGasOriginPtr
  entryCreateCompletedCut gasSummary gasSummaryCompose gasExemptCert stmtSimProps list
  exprSimFullBundleProps s1PrefixDefs exprSimIfExp freshWrites bodySimFull
  exprLoweringProps loweringPosts exprSimDefs allocaHistory venomState
  exprSimMemDefs bodyMemoryDefs bodyPtrDefs gasExplicitSites gasContext bodyFullPreds
  compileEnv vyperState

(* The source step consumes nothing. Both physical suffixes are on the
   same execution that supplies the materialization and final VV posts. *)
Triviality ifexp_conditional_scoped_suffix:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)) /\
  create_operand_full_scope sm sb E ctx fn z [] (OK t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (z,G,tn) [] (OK m,G1,tn1) /\
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (m,G1,tn1) [] (OK t,G2,tn2) /\
    Q H (INL tv) (ee with gas_obs := []) G2 tn2 t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,fn,PG) tops cx st0 sm sb
    (conditional_result cx raw) (ee,z,G,tn) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL tv`,`ee`,`OK t`,`G2`,`tn2`] >>
  simp[gas_explicit_def] >> rpt strip_tac >> res_tac >>
  metis_tac[gas_origin_ptr_path_append,APPEND_NIL]
QED

(* A completed condition transfers the root pre to the actual arm entry.
   This uses the condition's path at its own marks, not parent success. *)
Theorem ifexp_selected_arm_after_test:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfn) ce cx ty (IfExp t c a b) es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  expr_type c = BaseT BoolT /\
  e = (if sel then a else b) /\ lbl = (if sel then tl else el) /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (BoolV sel),mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  ~z.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx c (es,sa,sc,s0,cop,G0,tn0)
      H (INL (BoolV sel)) mid G1 tn1 z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (s0,G0,tn0) marks (OK z,G1,tn1)) /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\ fn_has_code sj sn fnc /\
  sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
  se.cs_current_bb = lbl /\ se.cs_current_insts = [] /\
  compile_expr ce ty e se = (av,sm) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shse = (av,shsm) /\
  gas_shadow_state se shse /\ gas_shadow_state sm shsm /\
  fn_has_code se sm fnc /\ fn_has_code shse shsm shfn /\
  local_ptrs_reserved ce se /\ sa.cs_next_var <= se.cs_next_var /\
  compile_ifexp_arm ce t (lowered_value_type ce e) av sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ fn_has_code sm sx fnc /\ fn_has_code sx sy fnc ==>
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfn) ce cx ty e mid
    (st0,se,sm,shse,shsm,av,jump_to lbl z,G1,tn1) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (z,G1,tn1) [] (OK (jump_to lbl z),G1,tn1))
Proof
  strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (z,G1,tn1) [] (OK (jump_to (if sel then tl else el) z),G1,tn1)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
       [expr_sim_full_post_def, expr_sim_full_endpoint_def]) >>
     `allocas_from lo z` by fs[ghost_inv_at_def] >>
     `op_taint tn1 cop = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
     drule_all ifexp_root_jnz_origin_path >> simp[]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `gas_admissible (eval_expr cx (if sel then a else b)) expr_vv_res_ok mid` by
    (irule ifexp_arm_raw_admissible >>
     drule_all ifexp_root_branch_admissible >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
    [expr_sim_full_post_def, expr_sim_full_endpoint_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (z,G1,tn1) _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_tac >>
  qpat_x_assum `lbl = (if sel then tl else el)` SUBST_ALL_TAC >>
  drule_all ifexp_selected_jump_ready >> strip_tac >>
  `( !x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   ( !x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
     metis_tac[not_fresh_at_mono] >>
  simp[expr_vv_sim_full_pre_def] >> rpt strip_tac
  >- (first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms, expr_sim_full_post_def, ifexp_ghost_inv_at_jump, stmt_state_rel_jump_to, expr_post_def]
QED

(* Finish from the materialization witness. The geometry hypotheses are only
   about the administrative site and appending its local scope. *)
Theorem ifexp_materialized_finish_scoped:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfn) ce cx ty (IfExp t c a b) es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  vyperState$bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL vc,mid) /\
  eval_expr cx e (mid with gas_obs := gs') = (INL raw,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx c (es,sa,sc,s0,cop,G0,tn0)
      H (INL vc) mid G1 tn1 z) /\
  (!tail. conditional_result cx raw (ee with gas_obs := tail) = (INL tv,ee with gas_obs := tail)) /\
  read_result cx raw ee = (INL v,ee) /\ read_result cx tv ee = (INL v,ee) /\
  MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (u,G,tn) [] (OK m,Gm,tm) /\
    expr_post H ctx fnc ce cx (IfExp t c a b) mid se sx (jump_to lbl z) ee v op m /\
    ghost_inv_at (DF H) lo d ce cx ee Gm tm m) /\
  (~is_word_type t ==> vv_at ce cx t se sx ee raw (LocatedValue t (mk_ptr op LocMemory)) m) /\
  (~is_word_type t ==> !id path. raw = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr ce cx ee m raw (LocatedValue t (mk_ptr op LocMemory))) /\
  (!ctv w. conditional_result cx raw ee = (INL ctv,ee) /\ ctv = Value w /\
     ~is_word_type t /\ ~is_bytestring_type t ==>
     vv_own ce cx t se sx ee ctv (LocatedValue t (mk_ptr op LocMemory)) m) /\
  expr_store_bound cx t v op m /\ m.vs_current_bb = sx.cs_current_bb /\
  m.vs_inst_idx = LENGTH sx.cs_current_insts /\ alloca_history fnc m /\
  (jump_to lbl z).vs_alloca_next <= m.vs_alloca_next /\ ptr_val_ok cx t v op Gm tm m /\
  (~is_word_type t ==> !e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gm m) /\
  (~is_word_type t ==> !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
    eval_operand op m = SOME w ==> type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= m.vs_alloca_next) /\
  ghost_kept_at lo ce mid se G1 tn1 (jump_to lbl z) Gm tm /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= se.cs_next_id /\ sx.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  vv = (if is_word_type t then StackValue t (Var rv) else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy fnc /\ fn_has_code sy sz fnc /\
  (!w. eval_operand op m = SOME w ==>
    create_operand_full_scope sx sb (gas_explicit_sites ctx shctx) ctx fnc m []
      (OK (jump_to xl (update_var rv w m with vs_inst_idx := LENGTH sy.cs_current_insts)))) /\
  create_operand_full_scope sm sx (gas_explicit_sites ctx shctx) ctx fnc u [] (OK m) /\
  (!sf. create_operand_full_scope sx sb (gas_explicit_sites ctx shctx) ctx fnc m [] (OK sf) ==>
    create_operand_full_scope sm sb (gas_explicit_sites ctx shctx) ctx fnc u [] (OK sf)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG) (cx_tops cx) cx st0 sm sb
    (conditional_result cx raw) (ee,u,G,tn)
    (\H res ee' G' tn' s.
      create_operand_vv_post (DF,lo,d,ctx,fnc) ce cx (IfExp t c a b) (es,sa,sb,s0,vv,G0,tn0)
        H res ee' G' tn' s /\ s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `storage_trace_frame (vyperState$bind (eval_expr cx c) (read_result cx))` by
    simp[storage_trace_frame_bind, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace` by
    (rpt gen_tac >> strip_tac >>
     `storage_trace_frame (eval_expr cx e)` by simp[evaluate_storage_trace_frame] >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `eval_expr cx e _ = _` (drule_at Any valid_horizon_frame) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `vyperState$bind _ _ _ = _` (drule_at Any valid_horizon_frame) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx fnc ce cx es s0 /\ ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0 /\
       expr_post H ctx fnc ce cx c es sa sc s0 mid vc cop z /\
       stmt_state_rel H ctx fnc ce cx mid (jump_to lbl z) /\
       expr_post H ctx fnc ce cx (IfExp t c a b) mid se sx (jump_to lbl z) ee v op m /\
       ghost_inv_at (DF H) lo d ce cx ee Gm tm m` by
    (rpt gen_tac >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[expr_sim_full_post_def, expr_post_def, stmt_state_rel_jump_to] >>
     metis_tac[]) >>
  suspend "finish"
QED

Resume ifexp_materialized_finish_scoped[finish]:
  FAIL_TAC "inspect finish input"
QED

Finalise ifexp_materialized_finish_scoped
