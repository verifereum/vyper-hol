(* Enrich the success post on the original counted witness. *)
Theory bodyIntCallCountedFrame
Ancestors
  gasOutcome gasSummary vyperState bodyIntCallArgLifetime exprSimDefs
  bodyIntCallSourceFrame

Theorem gas_outcome_success_frame:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R /\
  (!marks res ee t.
    gas_marked_exec memory (ctx,func) source (es,s0) marks res ee (OK t) /\
    Q res (ee with gas_obs := []) t ==>
    Frame res (ee with gas_obs := []) t) ==>
  gas_outcome memory tops (ctx,func) source (es,s0)
    (\res ee t. Q res ee t /\ Frame res ee t) R
Proof
  simp[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

(* Source replay is quantified over the unused observation suffix. *)
Theorem marked_supported_expr_source_frame:
  supported_pure_expr tops e /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e)
    (es,s0) marks res ee r ==>
  (ee with gas_obs := []) =
    es with <|outcomes := ee.outcomes; gas_obs := []|>
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  drule_all supported_eval_expr_outcomes >> simp[]
QED

(* Conditional application to the actual expression IH.  The universal
   implication below is the residual compiler-path obligation, not a fact
   supplied by expr_vv_sim. *)
Theorem expr_vv_sim_deferred_prefix:
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  compile_expr cenv (expr_type e) e sm = (vv,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sm.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  supported_pure_expr (cx_tops cx) e /\
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s0 /\
    vv_at cenv cx ty lo sm es raw held s0 /\
    safe_operand sm (vv_operand held)) hs /\
  (!marks raw ee t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL raw) ee (OK t) /\
    vv_post ctx func cenv cx e es sm sn s0 (ee with gas_obs := [])
      raw vv t /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
       b <= off /\ len + off <= b + sz ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    contract_storage t = contract_storage s0 /\
    contract_transient t = contract_transient s0 /\
    (!ty raw held lo w. MEM (ty,raw,held,lo) hs /\
      immutable_holds cenv cx ty raw w es s0 ==>
      immutable_holds cenv cx ty raw w es t)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t.
      (?raw. res = INL raw /\
        vv_post ctx func cenv cx e es sm sn s0 ee raw vv t /\
        t.vs_current_bb = sn.cs_current_bb /\
        t.vs_inst_idx = LENGTH sn.cs_current_insts) /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held ee t /\
        vv_at cenv cx ty lo sn ee raw held t /\
        safe_operand sn (vv_operand held)) hs)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_success_frame >> conj_tac
  >- (qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
      simp[expr_vv_sim_def] >> disch_then irule >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all marked_supported_expr_source_frame >> strip_tac >>
  irule vv_post_deferred_prefix >> simp[] >> metis_tac[]
QED
