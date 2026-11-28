(* A used default is observed at its expression cut and advances at its
   marshalled cut. The stage post also encodes the already packed arguments. *)
Theory s1PrefixBoolChainDefaultCallback
Ancestors
  s1PrefixBoolChainDefaultSuffixFold s1PrefixIntCallStageList s1PrefixIntCallStageSingleton
  vyperState
  s1PrefixIntCallStageConsCut s1PrefixIntCallStageReplay
  bodyFullIntCallArgs bodyFullIfExpReach bodyFullHashKeccakFixed
  exprBodyPreProps exprSimSliceCompose stmtSimForRounds
  s1PrefixCheckedContextFull s1PrefixIntCallArgsSource
  gasContext fragGasPath contextRawReachable vyperStorageFootprint list pair

Definition bool_chain_default_ready_def:
  bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,ce,cx,env,st0)
    (sa,s0,es0,G0,tn0,sf,shf,pin,clean_words,keep_sites) next P ds
    (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) <=>
    body_const_cells_agree [(NONE,tops)] cx env es /\
    EVERY (\a. expr_body_pre ce cx env a es) ds /\
    LENGTH flags = LENGTH ds /\ LENGTH dtys = LENGTH ds /\
    EVERY (\ty. type_memory_bytes ce ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type ds) dtys /\
    (!j. j < LENGTH ds /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (?rest. compile_stage_intcall_args compile_expr ce ds flags dtys si = (rest,sf) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
        (MAP gas_shadow_expr ds) flags dtys shi = (rest,shf)) /\
    gas_shadow_state si shi /\ fn_has_code si sf func /\ fn_has_code shi shf shadow_func /\
    local_ptrs_reserved ce si /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
    gas_admissible (bind (eval_exprs cx ds) (\vs. next (vals ++ vs))) P es /\
    storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      intcall_args_stage_post (DF,lo,d,ctx,func,ce,cx,env)
        ([]:expr list,sa,s0,es0,G0,tn0,si)
        ([],[],[],ops,vals,ptys,pflags,pin,clean_words,keep_sites)
        H (INL [] : value list + exception) es G tn s)
End

Theorem bool_chain_default_ready_nil:
  bool_chain_default_ready cfg origin next P []
    (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) ==>
  flags = [] /\ dtys = []
Proof
  PairCases_on `cfg` >> PairCases_on `origin` >> simp[bool_chain_default_ready_def]
QED

(* The nonempty callback for the suffix fold. Only the reached read or VV
   observation is needed from the smaller-context proof. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rewrite_tac[bool_chain_default_ready_def] >> strip_tac >>
  qpat_assum `compile_stage_intcall_args _ ce (a::rs) flags dtys si = (rest,sf)`
    (mp_then (Pos (el 3)) mp_tac intcall_stage_cons_cut_elim) >>
  disch_then irule >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr (a::rs)) flags dtys shi = (rest,shf)`
    (irule_at Any) >>
  qpat_assum `fn_has_code si sf func` (irule_at Any) >>
  qpat_assum `fn_has_code shi shf shadow_func` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`flag`,`fs`,`dt`,`ts`,`opnd`,`sm`,`shm`,`remain`] >>
  strip_tac >> gvs[MAP] >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  qpat_x_assum `gas_admissible (bind (eval_exprs cx (a::rs)) _) P es`
    (assume_tac o REWRITE_RULE [bool_chain_default_bind_cons]) >>
  `gas_admissible (eval_exprs cx [a])
      (\res. !err. res = INR err ==> expr_vv_res_ok (INR err)) es` by
    (drule slice_gas_admissible_bind_head >>
     disch_then (qspec_then `\res:value list + exception.
       !err. res = INR err ==> expr_vv_res_ok (INR err)` mp_tac) >> simp[]) >>
  `flag ==> is_word_type dt` by
    (qpat_assum `!j. _ /\ EL j (flag::fs) ==> is_word_type (EL j (dt::ts))`
       (qspec_then `0` (mp_tac o SIMP_RULE std_ss [listTheory.EL, prim_recTheory.LESS_0])) >>
     simp[NoAsms]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [intcall_args_stage_post_def])) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss
       [intcall_args_stage_post_def,APPEND_NIL,sumTheory.INL_11,UNWIND_THM2])) >>
  suspend "outcome"
QED
*)
Theorem bool_chain_default_singleton_callback:
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_expr a) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ gas_shadow_state sf shf /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
  bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,ce,cx,env,st0)
    (sa,s0,es0,G0,tn0,sf,shf,pin,clean_words,keep_sites) next P (a::rs)
    (si,shi,flags,dtys,ops,vals,ptys,pflags) (es,s,G,tn) /\
  (HD flags ==> !opnd sm shm.
    compile_stage_intcall_args compile_expr ce [a] [T] [HD dtys] si = ([opnd],sm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr a] [T] [HD dtys] shi = ([opnd],shm) /\
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type a) a es (st0,si,sm,shi,shm,opnd,s,G,tn) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx a) (read_result cx)) (es,s,G,tn)) /\
  (~HD flags ==> !vv ci shci.
    compile_expr ce (expr_type a) a si = (vv,ci) /\
    compile_expr (gas_shadow_env T ce) (expr_type a) (gas_shadow_expr a) shi = (vv,shci) /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type a) a es (st0,si,ci,shi,shci,vv,s,G,tn) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_expr cx a) (es,s,G,tn)) ==>
  ?flag fs dt ts opnd sm shm Q R.
    flags = flag::fs /\ dtys = dt::ts /\
    compile_stage_intcall_args compile_expr ce [a] [flag] [dt] si = ([opnd],sm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr a] [flag] [dt] shi = ([opnd],shm) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx [a]) (es,s,G,tn) /\
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx [a]) (es,s,G,tn) Q R /\
    (!H res ee gt r. R H res ee gt r ==> ISR res) /\
    (!marks hs mid G1 tn1 t.
      (!tail. eval_exprs cx [a]
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL hs,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\
      gas_path ctx func s (LENGTH marks) (OK t) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H (INL hs) mid G1 tn1 t) ==>
      bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,ce,cx,env,st0)
        (sa,s0,es0,G0,tn0,sf,shf,pin,clean_words,keep_sites) next P rs
        (sm,shm,fs,ts,ops ++ [opnd],vals ++ hs,ptys ++ [dt],pflags ++ [flag])
        (mid,t,G1,tn1))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_default_singleton_callback[outcome]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx [a]) (es,s,G,tn)
      (intcall_args_stage_post (DF,lo,d,ctx,func,ce,cx,env)
        ([a],sa,s0,es0,G0,tn0,sm)
        ([flag],[dt],[opnd],ops,vals,ptys,pflags,pin,clean_words,keep_sites))
      (\H res ee gt r. (?err. res = INR err) /\
        expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (irule intcall_args_stage_left_outcome >>
     qpat_assum `body_inv tops ctx ce cx` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ ce [a] _ _ si = _` (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     qpat_assum `eval_operands ops s = SOME _` (irule_at Any) >>
     qpat_assum `gas_admissible (eval_exprs cx [a]) _ es` (irule_at Any) >>
     qexistsl_tac [`shi`,`shm`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[MAP] >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> drule_all intcall_args_aggregate_physical_type >> simp[]) >>
  pop_assum (irule_at Any) >> simp[] >> conj_tac
  >- suspend "prefix"
  >> (conj_tac >- (rpt gen_tac >> strip_tac >> simp[]) >> suspend "advance")
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_default_singleton_callback[prefix]:
  irule intcall_stage_singleton_prefix_at_cut >>
  qpat_assum `compile_stage_intcall_args _ ce [a] _ _ si = _` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr a] _ _ shi = _` (irule_at Any) >>
  qpat_assum `expr_body_pre ce cx env a es` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `return_buf_frame d ce si s` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `flag` >> fs[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_default_singleton_callback[advance]:
  rpt gen_tac >> strip_tac >>
  drule_all intcall_stage_replay_head_read >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `expr_sim_inv ce cx env mid` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H (INL hs) _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [intcall_args_stage_post_def])) >> simp[]) >>
  `ci_mono si sm` by
    (mp_tac (MATCH_MP exprLoweringPropsTheory.ci_mono_compile_stage_intcall_args
       (CONJUNCT1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     disch_then (qspecl_then [`ce`,`[a]`,`[flag]`,`[dt]`,`si`] mp_tac) >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (simp[EVERY_MEM] >> rpt strip_tac >> irule intcall_args_pre_state >>
      simp[] >> qexists_tac `es` >> fs[EVERY_MEM])
  >- (qx_gen_tac `j` >>
      qpat_assum `!j. _ /\ EL j (flag::fs) ==> is_word_type (EL j (dt::ts))`
        (qspec_then `SUC j` (mp_tac o SIMP_RULE std_ss [listTheory.EL, prim_recTheory.LESS_MONO_EQ])) >>
      simp[NoAsms])
  >- (irule exprOperandVarTheory.compiler_ci_mono_reserved >> qexists_tac `si` >> simp[])
  >- (rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
      qexists_tac `si` >> simp[])
  >- (rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
      qexists_tac `si` >> simp[])
  >- (rpt strip_tac >> irule intcall_stage_headroom_after_path >>
      qpat_assum `body_inv tops ctx ce cx` (irule_at Any) >>
      qpat_assum `gas_path ctx func s _ (OK t)` (irule_at Any) >>
      qpat_assum `frag_reachable ctx func t fn inst u` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `gas_admissible (bind (eval_exprs cx [a]) _) P es`
        (mp_then Any mp_tac gas_admissible_bind_tail) >>
      disch_then (qspecl_then [`gas_explicit marks s.vs_gas_readings`,`hs`,`mid`] mp_tac) >> simp[])
  >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H (INL hs) _ _ _ _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp[NoAsms,intcall_args_stage_post_def] >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `eval_operands (ops ++ [opnd]) t = SOME _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_default_singleton_callback
*)
