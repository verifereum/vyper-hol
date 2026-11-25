(* Force an already materialized result without adding code to either run. *)
Theory bodyAggregateReadMods
Ancestors
  bodyFullPostsMods gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimMemorySource exprSimDefs gasSummary fragGasOriginPtr haltExitProj stmtSimProps
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
Libs monadsyntax

Theorem materialized_expr_exit[local]:
  !H (res : eval_result + exception) ee gt r.
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
    ?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r /\
          halt_exit H cx ee (INR exc : value + exception) r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)
Proof
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                   INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Theorem materialized_read_outcome[local]:
  (!gs raw ee. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) ==>
     ?v. raw = Value v) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s,G0,tn0)
    (\H res ee G tn t. ?raw. res = INL raw /\ P H raw ee G tn t) RP /\
  (!H ee v G tn t. valid_horizon cx st0 H ee.storage_trace /\
     P H (Value v) ee G tn t ==> Q H (INL v) ee G tn t) /\
  (!H res ee gt r. RP H res ee gt r ==>
     ?exc. res = INR exc /\ R H (INR exc) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0) Q R
Proof
  strip_tac >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL reached) mid (OK mid_state)` >>
      irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`mid_state`,`reached`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn t.
    (?v. res = INL (Value v) /\ Q H (INL v) ee G tn t) /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ RP` (irule_at Any) >>
      BETA_TAC >> conj_tac
      >- (rpt gen_tac >> strip_tac >> gvs[] >>
          qpat_x_assum `!tail. eval_expr _ _ _ = _`
            (qspec_then `[]` mp_tac) >>
          simp[] >> strip_tac >>
          qpat_assum `!gs raw ee. _ ==> ?v. raw = Value v`
            (drule_then strip_assume_tac) >> gvs[] >>
          qpat_assum `!v G tn t. P _ _ _ _ _ _ ==> Q _ _ _ _ _ _`
            (drule_then assume_tac) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  disj1_tac >> qexists_tac `Value v` >> simp[] >>
  irule gas_outcome_full_mods_pure >> simp[read_result_def, return_def] >>
  qexistsl_tac [`G`,`ee`,`INL v`,`u`,`tn`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[cj 1 gas_origin_ptr_path_rules] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` (mp_tac o BETA_RULE)) >> simp[]
QED

(* The cut may use all the value judgement's entry hypotheses.  Quotation
   templates name its literal interface, without adding HOL predicates. *)
val read_entry = ``
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val read_vv_post = ``
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee raw vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee raw vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list))
    lo d cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G tn t /\
  (!v. raw = Value v /\ ~is_word_type (post_value_type cenv e) /\
       ~is_bytestring_type (post_value_type cenv e) ==>
       vv_own cenv cx (post_value_type cenv e) sa sb ee raw vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx raw ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  (!t' op'. vv = StackValue t' op' /\ ~is_word_type (post_value_type cenv e) ==>
            ptr_buf_ok cenv e op' G t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val read_value_post = ``
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list))
    lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem materialized_value_from_vv_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  (!gs raw ee. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) ==>
     ?v. raw = Value v) /\
  (!st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    ^read_entry ==>
    ?vv. compile_expr cenv ty e sa = (vv,sb) /\
         compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
           (vv,shadow_sb) /\
         !H ee raw v G tn t. valid_horizon cx st0 H ee.storage_trace /\
           raw = Value v /\ ^read_vv_post ==> ^read_value_post) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!st0 sa sb sha shb op s0 G0 tn0. _ ==> ?vv. _`
    (fn th => drule_all_then (qx_choose_then `vv` strip_assume_tac) th) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (fn th => drule_all_then assume_tac (REWRITE_RULE [expr_vv_sim_full_mods_def] th)) >>
  irule materialized_read_outcome >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`\H raw ee G tn t. ^read_vv_post`,
    `\H res ee gt r. expr_exit (res : eval_result + exception) r /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)`] >>
  BETA_TAC >> reverse (rpt conj_tac)
  >- first_assum ACCEPT_TAC
  >- MATCH_ACCEPT_TAC materialized_expr_exit >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qexists_tac `v` >> conj_tac >- REFL_TAC >>
  qpat_assum `!H ee raw v G tn t. _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    irule >>
  asm_rewrite_tac[] >> qexists_tac `Value v` >> asm_rewrite_tac[]
QED
