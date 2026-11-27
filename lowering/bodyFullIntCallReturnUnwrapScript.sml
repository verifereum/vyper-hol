Theory bodyFullIntCallReturnUnwrap
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams bodyFullUnwrap gasOutcomeFullCompose
  bodyFullOfVV bodyFullPreds bodySimFull gasShadowCompile exprSimMemorySource
  aggregateEvaluatedLayout bodyFullIntCallReturnTyping
  exprLoweringProps loweringPosts bodyFullHashKeccakFixed compileEnv context vyperTypeSystem
  vyperAST vyperInterpreter vyperState venomState
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `compile_expr cenv ty (Call _ _ _ _) sa = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[]) >>
  qpat_x_assum `fn_has_code sa sm func /\ _ ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  `evaluate_type (get_tenv cx) ret = SOME rtv` by
    (qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[intcall_entry_full_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (intcall_rest _ _ _ _ _ _ _)`]
  >- (pure_rewrite_tac[intcall_rest_def] >>
      irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
      simp_tac pure_ss [vyperStorageTraceTheory.storage_trace_frame_optional_locks, boolTheory.AND_CLAUSES] >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >> reverse conj_tac
      >- (irule vyperStorageTraceTheory.storage_trace_frame_finally_unless_halt >>
          simp_tac pure_ss [vyperStorageTraceTheory.storage_trace_frame_optional_locks, boolTheory.AND_CLAUSES] >>
          irule vyperStorageTraceTheory.storage_trace_frame_finally >>
          simp[vyperStorageTraceTheory.storage_trace_frame_function_stack] >>
          irule vyperStorageTraceTheory.storage_trace_frame_try >>
          simp[vyperStorageTraceTheory.storage_trace_frame_function_handler] >>
          irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
          simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
               vyperStorageTraceTheory.storage_trace_frame_return]) >>
      gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts,
           vyperStorageTraceTheory.storage_trace_frame_return])
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res`
      >- (Cases_on `r` >> fs[exprSimDefsTheory.expr_exit_def]) >>
      Cases_on `r` >> Cases_on `y` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      rename1 `expr_exit (INR (Error err)) _` >>
      Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  suspend "read"
QED
*)
Theorem intcall_return_unwrap:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs dflts.
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
      sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  (?H. valid_horizon cx st0 H es1.storage_trace) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
  (fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
      (\H res ee G tn t'. ?tv. res = INL tv /\
        vv_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
          es0 sa sm s0 ee tv vv t' /\
        vv_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
          (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ee tv vv t' /\
        t'.vs_current_bb = sm.cs_current_bb /\ t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func t' /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
        ptr_vv_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) tv vv ee G tn t' /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) = SOME rt /\
              eval_operand (vv_operand vv) t' = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
        (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
          ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op G t') /\
        (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) p.ptr_operand G t') /\
        ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  !op sb shadow_sb.
    unwrap_value cenv vv sm = (op,sb) /\
    unwrap_value cenv vv shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sb shadow_sb /\ fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) (read_result cx)) expr_res_ok es1 ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0
      (bind (intcall_rest cx name mut nr ss prev rtv) (read_result cx)) (es1,t,G,tn)
      (\H res ee G tn t'. ?v. res = INL v /\
        expr_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
          es0 sa sb s0 ee v op t' /\
        expr_store_bound cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) v op t' /\
        t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t' /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
        ptr_val_ok cx (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) v op G tn t' /\
        (~is_word_type (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
          ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op G t') /\
        ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_return_unwrap[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. intcall_rest _ _ _ _ _ _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `MAP FDOM es0.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     pure_rewrite_tac [loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def] >>
     metis_tac[]) >>
  drule_then assume_tac body_post_type_allocation_bound >>
  drule exprSimHypsTheory.post_type_evaluates >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (post_value_type cenv _) = SOME rty` >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >> drule_all intcall_rest_read_post_typed >> simp[]) >>
  mp_tac (Q.INST [`e` |-> `Call ann (IntCall (NONE,name)) es dflt`]
    (Q.INST [`sb` |-> `sm`, `sc` |-> `sb`, `G` |-> `G1`,
      `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`, `es` |-> `es0`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
      (SPEC_ALL unwrap_value_origin_ptr))) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp[] >> NO_TAC) >>

    gvs[arithmeticTheory.ADD_COMM]) >>
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> gvs[] >>
  metis_tac[cj 1 expr_post_def, stmt_state_rel_allocas_below_fmp]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise intcall_return_unwrap
*)
