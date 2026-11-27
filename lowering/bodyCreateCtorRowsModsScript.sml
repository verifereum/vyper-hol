(* Constructor operands at the common exit of the linked positional run. *)
Theory bodyCreateCtorRowsMods
Ancestors
  bodyExtPosListRunMods bodyExtPosSavedRowMods bodyCreateCtorRowsReplayMods
  createSizeCtorPayload gasShadowCompileBase exprLowering vyperTypeContract pair list
Libs monadsyntax

val rows = ``\(e,sv) v.
  (?si sm ss vv raw copy.
    compile_expr cenv (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv cenv copy
      (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
    (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
      ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
        eval_operand (vv_operand sv) t = SOME w /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
        val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
          SOME (w2n w,type_memory_size tv) /\
        sm.cs_next_id < ss.cs_next_id /\
        (!n b sz. local_region cenv ee.scopes t n b sz ==>
          regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
    sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
    local_ptrs_reserved cenv si /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    ((?tag op0. sv = StackValue tag op0) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
       lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
    read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
    vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
  vv_storage_live (H : (bool # bytes32 # type_value) list # num list) cx sv ee t /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
    ptr_buf_ok cenv e op G t) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G t) /\
  (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand sv) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem))``;

Theorem create_ctor_rows_project[local]:
  LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx [] sa sb H
      e sv v ee G tn t) (ZIP (xs,svs)) vs ==>
  LIST_REL ^rows (ZIP (xs,svs)) vs
Proof
  match_mp_tac LIST_REL_mono >> Cases >>
  simp[ext_pos_saved_row_mods_def,expr_can_mutate_def]
QED

(* Use the caller's linked checker facts and reached allocation state. *)
Theorem create_ctor_rows_cut_mods:
  body_const_cells_agree_mods mods cx env es /\
  body_exprs_full_ok_mods mods exps cx xs /\ contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sb) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!marks vs ee G tn t.
    (!tail. eval_exprs cx xs (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
            (INL vs,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G,tn)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      LENGTH svs = LENGTH xs /\ LIST_REL ^rows (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      mods cx st0 (next vs) (ee,t,G,tn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (bind (eval_exprs cx xs) next) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule create_ctor_rows_replay_bind_mods >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists_tac `extcall_positional_post_mods F mods DF lo d ctx func cenv cx env
    [] xs svs sa sb es s0 G0 tn0` >>
  reverse (rpt conj_tac)
  >- (qpat_x_assum `compile_create_ctor_args _ cenv _ sa = _`
        (assume_tac o REWRITE_RULE [create_ctor_args_snapshots,compile_abi_encode_args_def]) >>
      qpat_x_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr _) _ = _`
        (assume_tac o REWRITE_RULE [create_ctor_args_snapshots,compile_abi_encode_args_def,
          lowered_value_type_gas_shadow_env]) >>
      irule ext_pos_list_run_mods >> simp[] >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (gen_tac >> disch_tac >>
           qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
             (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
      >- (qexistsl_tac [`shadow_func`,`shadow_sa`,`shadow_sb`] >> simp[])
      >- (qexists_tac `exps` >> simp[])
      >- (qexistsl_tac [`src`,`tops`] >> simp[]))
  >- (simp[extcall_positional_post_mods_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!marks vs ee G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (next vs) _ _ _`
    irule >> reverse conj_tac >- (simp[] >> qexists_tac `marks` >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H _ ==>
    extcall_positional_post_mods F mods DF lo d ctx func cenv cx env
      [] xs svs sa sb es s0 G0 tn0 H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def])) >>
  drule_then assume_tac create_ctor_rows_project >> simp[]
QED
