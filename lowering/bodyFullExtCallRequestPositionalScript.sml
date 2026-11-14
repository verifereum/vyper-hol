(* Joint positional operands: representation adapters and CPS composition. *)
Theory bodyFullExtCallRequestPositional
Ancestors
  bodyFullExtCallRequestSnapshotMemory bodyFullExtCallRequestRetag
  bodyFullExtCallRequestSnapshotWord compileEnv
  bodyFullUnwrap gasOutcomeFullCompose gasOutcomeFull bodySimFull
  fragGasOriginPtr vyperStorageFootprint
  exprSimSource exprSimHyps exprSimHypsDefs vyperTypeInvariants vyperTypeExprSoundness
  bodyPtrDefs loweringPosts exprLowering supportedExprTraverse vyperState

(* Discharge both typing premises at the immediate source read. *)
Theorem extcall_snapshot_located_retag:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  ~expr_has_effect e /\ ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e sa = (LocatedValue tag p,sm) /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (post_value_type ce e) raw (LocatedValue tag p) ee s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue tag p) ee G tn s ==>
  vv_holds ce cx (lowered_value_type ce e) raw
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee s /\
  ptr_vv_ok cx (lowered_value_type ce e) raw
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee G tn s
Proof
  strip_tac >> Cases_on `p.ptr_location = LocMemory`
  >- (`post_value_type ce e = expr_type e` by
        (irule post_value_type_not_int_call >> rpt strip_tac >>
         gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]) >>
      `value_runtime_typed env (lowered_value_type ce e) v` by
        (irule memory_rhs_read_lowered_typed_unwidened >>
         qexistsl [`cx`, `es`, `ee`] >> simp[bind_def]) >>
      `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      `?dv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dv /\
            value_has_type dv v` by gvs[value_runtime_typed_def] >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >>
      simp[ext_call_arg_value_def] >>
      irule extcall_request_memory_retag >> metis_tac[]) >>
  irule extcall_nonmemory_retag >> metis_tac[]
QED

(* The word branch can consume expr_sim_full, without repeating unwrap. *)
Theorem extcall_snapshot_word_lower_value:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  vv_holds ce cx (post_value_type ce e) tv vv ee s /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv)
    sm = (sv,sb) ==>
  ?op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
       sv = StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op
Proof
  strip_tac >> drule_all extcall_request_word_snapshot_unwrap >> strip_tac >>
  gvs[lower_value_def, comp_bind_def, comp_return_def] >>
  Cases_on `unwrap_value ce vv sm` >> gvs[]
QED

(* Append only the target unwrap: the raw source result is not mapped or read. *)
Theorem extcall_snapshot_word_unwrap_full:
  let P = (\H res ee G tn t. ?raw.
        res = INL raw /\
        vv_post H ctx func ce cx e es sa sm s0 ee raw vv t /\
        vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv t /\
        ghost_inv_at (DF H) lo d ce cx ee G tn t /\
        ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
        (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
                 ptr_buf_ok ce e p.ptr_operand G t) /\
        (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?v. read_result cx raw ee = (INL v,ee) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                     eval_operand (vv_operand vv) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes /\
        (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
        t.vs_inst_idx = LENGTH sm.cs_current_insts /\
        ghost_kept_at lo ce es sa Gi ti s0 G tn)
  in
  compile_expr ce ty e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  is_word_type (post_value_type ce e) /\ is_word_type (expr_type e) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_expr cx e) (es,s0,Gi,ti) P R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_expr cx e) (es,s0,Gi,ti)
    (\H res ee G tn z. ?raw v.
      res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
      expr_post H ctx func ce cx e es sa sb s0 ee v op z /\
      expr_store_bound cx (expr_type e) v op z /\
      ghost_inv_at (DF H) lo d ce cx ee G tn z /\
      ptr_val_ok cx (post_value_type ce e) v op G tn z /\
      vv_holds ce cx (post_value_type ce e) raw
        (StackValue (post_value_type ce e) op) ee z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_kept_at lo ce es sa Gi ti s0 G tn) R
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P _` >>
  irule gas_outcome_full_zero_suffix_mono >>
  qexistsl [`P`, `R`] >>
  conj_tac >- simp[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  first_assum (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- gvs[storage_trace_domain_def] >>
  strip_tac >> gvs[Abbr `P`] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_origin_ptr >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl [`z`, `G'`, `tn'`] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  simp[vv_holds_def] >>
  gvs[expr_post_def]
QED
