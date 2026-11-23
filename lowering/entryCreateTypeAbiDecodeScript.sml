(* The singleton ABI decoder starts only after the scoped Bytes child exits. *)
Theory entryCreateTypeAbiDecode
Ancestors
  entryCreateFocusSpec entryCreateCompositeFocus entryCreateIntervalLayout
  entryCreateNativeFirstExit entryCreateRegionLift entryCreateReplayBind
  bodyFullAbiDecodeExprConditional exprSimAbiDecodeBodySuccess
  exprSimAbiDecodeEntryTyping exprOpenFirstOperand exprBodyPreProps bodyInvCodeProps
  gasShadowCompileStmtHelpers gasExemptCert vyperTypeInvariants vyperTypeExprResult
  vyperTypeExprSoundness compileEnv vyperValue s1PrefixDefs gasShadow exprSimSource
  gasShadowState vyperState exprSimHyps vyperTyping
  bodyFullAbiDecodeCallerFull createSizeCutCode createSizeCutRegion
  entryCreatePathScope entryCreatePendingScope entryCreateOperandReplay entryCreateBodyCut
  entryCreateCompletedCut createSizePrefixReplay gasExplicitSites gasOutcomeFull
  exprSimFullBundleProps fragExec fragGasPath fragGasOriginPtr vyperStorageTrace
  vyperStorageFootprint venomRunBounded list arithmetic gasContext abiEncoderProps

Theorem create_abi_decode_child_site[local]:
  expr_body_pre ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_vv_sim_full_pre (DF,lo,delta,ctx,shctx,PG,func,shfunc) ce cx ty0
    (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  ?data start shstart out.
    expr_sim_full_pre (DF,lo,delta,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es
      (st0,sa,start,sha,shstart,data,s0,G0,tn0) /\
    (let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
      lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
        (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
        (type_memory_bytes ce wty) start = (out,sb)) /\
    vv = LocatedValue ty (mk_ptr out LocMemory) /\ fn_has_code start sb func
Proof
  strip_tac >> drule expr_body_pre_type_builtin_head >> strip_tac >>
  fs[expr_vv_sim_full_pre_def] >>
  drule_all abi_decode_singleton_compile >> strip_tac >> gvs[] >>
  `?shstart. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
     (gas_shadow_expr e) sha = (data,shstart) /\ gas_shadow_state start shstart` by
    (qpat_assum `gas_shadow_state sa sha`
       (mp_then Any mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
     disch_then (qspecl_then [`expr_type e`,`e`,`ce`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e) sha` >> simp[]) >>
  `fn_has_code sha shstart shfunc` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     `expr_type (gas_shadow_expr e) = BaseT (BytesT (Dynamic n))` by simp[] >>
     drule_all abi_decode_singleton_compile >> simp[] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`data`,`start`,`shstart`,`out`] >>
  qpat_assum `expr_body_pre _ _ _ e es`
    (assume_tac o MATCH_MP expr_body_pre_gas_admissible) >>
  gvs[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem create_abi_decode_observed_bytes[local]:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
  vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,mid) ==>
  (?bs. v = BytesV bs) /\ MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >> reverse conj_tac >- metis_tac[abi_decode_observed_scopes_dom] >>
  `expr_result_typed env e (Value v)` by
    (irule (cj 3 expr_body_pre_eval) >>
     qexistsl [`ce`,`cx`,`es with gas_obs := obs`,`mid`] >> fs[bind_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  gvs[] >> qpat_x_assum `expr_result_typed _ _ _` mp_tac >>
  Cases_on `v` >>
  simp[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
       value_has_type_def]
QED

(* Suffix rule interface: the exact context and physical setup handoff of
   the committed decoder, but with scope on its chosen endpoint. Only the
   four decoder producer propositions are omitted from the interface. *)
local
  val caller = CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
    abi_decode_caller_full_conditional
  val caller_pre = funpow 4 rand (lhand (concl caller))
  val tail = rand (concl caller)
  val (_, [params,tops,cx,st0,source,init,q,r]) = strip_comb tail
  val stmt = ``^caller_pre /\ create_layout start final ==>
    scoped_operand_outcome ^params ^tops ^cx ^st0 start final ^source ^init ^q ^r``
in
  val decode_selected_tail = list_mk_forall (free_vars stmt,stmt)
end

val decode_tail_inventory = ``
  !ce data wty start out final.
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) start = (out,final) ==>
    create_cut_code {} start final /\
    EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code start final)``

Triviality create_abi_scope_child_post:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G0,tn0)
    Q (create_operand_exit_post C cx) /\
  (!H res ee G tn t. Q H res ee G tn t ==> ?v. res = INL v) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ Q H (INL v) ee G tn t /\ ~t.vs_halted)
    (\H res ee gt r. ?exc. res = INR exc /\
       create_operand_exit_post C cx H (INR exc : eval_result + vyperState$exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> res_tac >> fs[]
      >- (`~t.vs_halted` by metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase,
                                     gas_path_normal] >> metis_tac[]) >>
      Cases_on `res` >>
      fs[create_operand_exit_post_def, exprSimDefsTheory.expr_exit_def,
         exprSimDefsTheory.halt_exit_def,stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Triviality create_abi_right_prefix:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix m b E C f u marks t ==>
  create_expr_prefix a b E C f u marks t
Proof
  strip_tac >> irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
  simp[create_prefix_step_def, frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Triviality create_abi_scope_geometry:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_layout a b /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    (fs[create_cut_code_def] >> metis_tac[create_layout_left_stop]) >>
  conj_tac >- metis_tac[create_left_focus_lift_at] >>
  conj_tac >- metis_tac[create_left_terminal_lift_at] >>
  conj_tac
  >- (qx_genl_tac [`left`,`t`,`right`] >>
      simp[create_operand_full_scope_def,create_operand_focus_scope_def] >>
      disch_then (CONJUNCTS_THEN2 strip_assume_tac
        (qx_choosel_then [`front`,`stop`,`pending`]
          (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "pending"))))) >>
      `create_cut_region m b t` by metis_tac[cj 1 create_cut_region_rules] >>
      `create_expr_prefix a b E C f s left t` by metis_tac[create_left_prefix_lift_at] >>
      `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
      qexistsl [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
      conj_tac >- metis_tac[create_abi_right_prefix,create_expr_prefix_append] >>
      Cases_on `pending = []` >> simp[] >>
      asm "pending" strip_assume_tac >> simp[] >> rpt strip_tac >>
      qpat_assum `create_prefix_step a b E C f stop _ _`
        (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
      first_x_assum irule >> qexists `v` >>
      irule (cj 1 operand_cut_region_edge) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qx_genl_tac [`left`,`t`,`right`,`r`] >> Cases_on `r` >>
  simp[create_operand_full_scope_def] >> strip_tac >>
  `create_expr_prefix a b E C f s left t` by metis_tac[create_left_prefix_lift_at] >>
  metis_tac[create_abi_right_prefix,create_expr_prefix_append,APPEND_ASSOC]
QED

Triviality create_abi_selected_continuation:
  ^decode_selected_tail /\
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_sim_full_pre (DF,lo,delta,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es
    (st0,sa,start,sha,shstart,data,s0,G0,tn0) /\
  (let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) start = (out,final)) /\
  fn_has_code start final func /\ create_layout start final /\ ~s.vs_halted /\
  storage_trace_domain cx st0 es1.storage_trace /\ es1.gas_obs = [] /\
  vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,es1) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
      expr_sim_full_post (DF,lo,delta,ctx,func) ce cx e (es,sa,start,s0,data,G0,tn0)
        H (INL v) es1 G tn s) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 start final
    (vyperState$bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]))
       (\w. return (Value w))) (es1,s,G,tn)
    (\H res ee G' tn' t. create_operand_vv_post (DF,lo,delta,ctx,func) ce cx
      (TypeBuiltin ty (AbiDecode unwrap) ty [e])
      (es,sa,final,s0,LocatedValue ty (mk_ptr out LocMemory),G0,tn0) H res ee G' tn' t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "decode") (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule expr_body_pre_type_builtin_head >> strip_tac >>
  drule_all create_abi_decode_observed_bytes >> strip_tac >> gvs[LET_THM] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >> simp[vyperASTTheory.expr_type_def,optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (drule_at_then (Pos (el 2)) mp_tac valid_horizon_frame >>
        simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
     res_tac >> fs[]) >>
  asm "decode" (mp_tac o BETA_RULE o
    Q.INST [`ann` |-> `ty`, `explicit` |-> `gas_explicit_sites ctx shctx`] o SPEC_ALL) >>
  impl_tac >-
    (conj_tac >- (irule (BETA_RULE (Q.INST [`env` |-> `env`, `n` |-> `n`]
       abi_decode_caller_entry_from_child)) >> simp[]) >> simp[]) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ post_old exit_old` >>
  qmatch_goalsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ post_new exit_new` >>
  `post_old = post_new` by
    (simp[Abbr `post_old`,Abbr `post_new`,FUN_EQ_THM,create_operand_vv_post_def,
          contextTheory.vv_location_def,contextTheory.mk_ptr_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `exit_old = exit_new` by simp[Abbr `exit_old`,Abbr `exit_new`,create_operand_exit_post_def,FUN_EQ_THM] >>
  gvs[]
QED
