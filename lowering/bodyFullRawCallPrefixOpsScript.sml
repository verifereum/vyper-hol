(* Typed continuations at the prepared raw_call prefix's child boundaries. *)
Theory bodyFullRawCallPrefixOps
Ancestors
  bodyFullRawCallForcedArgs bodyFullWordArgs gasOutcomeFullCompose
  exprSimRawCall gasExemptCert vyperStorageTrace bodyFullRawCallGeneratedPrefix

Definition raw_call_kw_post_def:
  raw_call_kw_post DF lo dframe ctx func cenv cx esD s4 s5 t4 G4 tn4 kws xs
    H (rr : value list + vyperState$exception) mid G tn t <=>
    (?vs. rr = INL vs /\
      typed_args_post H ctx func cenv cx esD s4 t4 mid kws xs vs t /\
      t.vs_current_bb = s5.cs_current_bb /\
      t.vs_inst_idx = LENGTH s5.cs_current_insts /\
      alloca_history func t /\ t4.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx mid G tn t /\
      ghost_kept_at lo cenv esD s4 G4 tn4 t4 G tn /\
      EVERY (\x. op_taint tn x = {}) xs) /\ ~t.vs_halted /\ mid.gas_obs = []
End

(* Non-GAS preparation uses a physical execution, not just equal PCs. *)
Definition raw_call_prep_landing_def:
  raw_call_prep_landing i j s t <=>
    ?u. run_inst_seq (emitted_insts i j) s = OK u /\
        t = u with vs_inst_idx := LENGTH j.cs_current_insts
End

(* Preserve the exact reading and reindexed state exposed by the joint GAS
   producer; a supplied gas keyword leaves the state and marks unchanged. *)
Definition raw_call_gas_landing_def:
  raw_call_gas_landing go i j s n t <=>
    case go of
      SOME g => n = 0 /\ t = s
    | NONE => n = 1 /\ ?gw. gas_prefix 1 s.vs_gas_readings = [gw] /\
        t = update_var (FST (fresh_var i)) gw
           (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                     vs_inst_idx := LENGTH j.cs_current_insts|>)
End

Definition raw_call_forced_intro_def:
  raw_call_forced_intro A (DF,lo,dframe,ctx,func) (cenv,env,cx,tops,st0)
    (a,d,kws) (sa,s1,s2,addr,data) (es,s0,G0,tn0) k Q R <=>
    (!gsA av esA tA GA tnA gsD bs esD tD GD tnD.
      bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
      bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
        (INL (BytesV bs),esD) /\
      esA.gas_obs = [] /\ esD.gas_obs = [] /\
      body_const_cells_agree [(NONE,tops)] cx env esD /\
      body_exprs_full_ok cx kws /\ expr_sim_inv cenv cx env esD /\
      storage_trace_domain cx st0 esD.storage_trace /\
      (!fn inst s. frag_reachable ctx func tD fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H esD.storage_trace ==>
        expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
        expr_store_bound cx (post_value_type cenv a) av addr tA /\
        tA.vs_current_bb = s1.cs_current_bb /\
        tA.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func tA /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp tA) /\
        s0.vs_alloca_next <= tA.vs_alloca_next /\
        ghost_inv_at (DF H) lo dframe cenv cx esA GA tnA tA /\
        ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA /\
        (~is_word_type (post_value_type cenv a) ==> ptr_buf_ok cenv a addr GA tA) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA /\ ~tA.vs_halted /\
        expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
        expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
        tD.vs_current_bb = s2.cs_current_bb /\
        tD.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func tD /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp tD) /\
        tA.vs_alloca_next <= tD.vs_alloca_next /\
        ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD /\
        ptr_val_ok cx (post_value_type cenv d) (BytesV bs) data GD tnD tD /\
        (~is_word_type (post_value_type cenv d) ==> ptr_buf_ok cenv d data GD tD) /\
        ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\ ~tD.vs_halted) ==>
      A s2 (k av (BytesV bs)) (esD,tD,GD,tnD) Q R) ==>
    A sa (bind (bind (eval_expr cx a) (read_result cx))
         (\av. bind (bind (eval_expr cx d) (read_result cx)) (k av))) (es,s0,G0,tn0) Q R
End

Definition raw_call_kw_intro_def:
  raw_call_kw_intro A (DF,lo,dframe,ctx,shadow_ctx,func,PG) (cenv,cx,st0)
    (s4,s5,kws,xs) (esD,t4,G4,tn4) next Q R <=>
    (!marksK resK esK GK tnK tk.
      (!tail. eval_exprs cx kws
        (esD with gas_obs := gas_explicit marksK t4.vs_gas_readings ++ tail) =
        (resK, esK with gas_obs := tail)) /\
      storage_trace_domain cx st0 esK.storage_trace /\
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        raw_call_kw_post DF lo dframe ctx func cenv cx esD s4 s5 t4 G4 tn4 kws xs
          H resK esK GK tnK tk) /\
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t4,G4,tn4) marksK (OK tk,GK,tnK)) ==>
      ?kvs. resK = INL kvs /\ A s5 (next kvs) (esK,tk,GK,tnK) Q R) ==>
    A s4 (bind (eval_exprs cx kws) next) (esD,t4,G4,tn4) Q R
End

Definition raw_call_initial_intro_def:
  raw_call_initial_intro A cx st0 i source (es,s,G,tn) Q R <=>
    storage_trace_frame source /\ ~s.vs_halted /\
    (storage_trace_domain cx st0 es.storage_trace ==> A i source (es,s,G,tn) Q R) ==>
    A i source (es,s,G,tn) Q R
End

Definition raw_call_neutral_intro_def:
  raw_call_neutral_intro A (DF,lo,explicit,ctx,func,PG) cx st0 i j landing Q R <=>
    !source es s G tn n t J u.
      storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
      landing s n t /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (s,G,tn) (REPLICATE n F) (OK t,J,u)) /\
      A j source (es,t,J,u) Q R ==>
      A i source (es,s,G,tn) Q R
End

Theorem raw_call_initial_intro_full:
  raw_call_initial_intro
    (\i. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0)
    cx st0 i source (es,s,G,tn) Q R
Proof
  simp[raw_call_initial_intro_def] >> metis_tac[gas_outcome_full_initial_domain]
QED

Theorem raw_call_neutral_intro_full:
  raw_call_neutral_intro (\i. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0)
    (DF,lo,explicit,ctx,func,PG) cx st0 i j landing Q R
Proof
  simp[raw_call_neutral_intro_def] >> rpt strip_tac >>
  irule raw_call_generated_prefix_full >> simp[] >> metis_tac[]
QED

Theorem raw_call_kw_intro_full:
  (!v. storage_trace_frame (next v)) /\
  (!H exc ee gt r. expr_exit (INR exc) r /\ halt_exit H cx ee (INR exc) r ==>
    R H (INR exc) ee gt r) /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx kws) (esD,t4,G4,tn4)
    (\H rr mid G tn t. ?vs. rr = INL vs /\
      typed_args_post H ctx func cenv cx esD s4 t4 mid kws xs vs t /\
      t.vs_current_bb = s5.cs_current_bb /\
      t.vs_inst_idx = LENGTH s5.cs_current_insts /\
      alloca_history func t /\ t4.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx mid G tn t /\
      ghost_kept_at lo cenv esD s4 G4 tn4 t4 G tn /\
      EVERY (\x. op_taint tn x = {}) xs)
    (\H rr mid gt r. wb_args_exit rr r /\ halt_exit H cx mid rr r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) ==>
  raw_call_kw_intro
    (\i. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0)
    (DF,lo,dframe,ctx,shadow_ctx,func,PG) (cenv,cx,st0) (s4,s5,kws,xs)
    (esD,t4,G4,tn4) next Q R
Proof
  simp[raw_call_kw_intro_def] >> strip_tac >> strip_tac >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[cj 6 evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[] >>
  qexists_tac `raw_call_kw_post DF lo dframe ctx func cenv cx esD s4 s5 t4 G4 tn4 kws xs` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx kws) _ _ _` (irule_at Any) >>
      simp[raw_call_kw_post_def,NoAsms] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimWordArgsTheory.wb_args_exit_def] >>
      first_x_assum irule >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  rpt gen_tac >> strip_tac >> disj1_tac >>
  qpat_assum `!marks res mid G1 tn1 t. _ ==> ?v. _`
    (qspecl_then [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] mp_tac) >> simp[]
QED

(* Guards are the established preconditions of the two child producers. *)
Definition raw_call_forced_ready_def:
  raw_call_forced_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
    (tops,cenv,env,cx,st0) (ann,flags,a,d,kws)
    (sa,s1,s2,shadow_sa,h1,h2,addr,data) (es,s0,G0,tn0) <=>
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
    body_exprs_full_ok cx (a::d::kws) /\
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr a) shadow_sa = (addr,h1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
      (gas_shadow_expr d) h1 = (data,h2) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 h1 /\
    gas_shadow_state s2 h2 /\ gas_shadow_context ctx shadow_ctx /\
    gas_shadow_function func shadow_func /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code shadow_sa h1 shadow_func /\ fn_has_code h1 h2 shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Theorem raw_call_forced_intro_full:
  raw_call_forced_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
    (tops,cenv,env,cx,st0) (ann,flags,a,d,kws)
    (sa,s1,s2,shadow_sa,h1,h2,addr,data) (es,s0,G0,tn0) /\
  (!av dv. storage_trace_frame (k av dv)) /\
  (!H exc ee gt r. expr_exit (INR exc) r /\ halt_exit H cx ee (INR exc) r ==>
    R H (INR exc) ee gt r) ==>
  raw_call_forced_intro
    (\i. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0)
    (DF,lo,dframe,ctx,func) (cenv,env,cx,tops,st0)
    (a,d,kws) (sa,s1,s2,addr,data) (es,s0,G0,tn0) k Q R
Proof
  simp[raw_call_forced_ready_def,raw_call_forced_intro_def] >> strip_tac >>
  strip_tac >> irule raw_call_forced_args_full >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  qexistsl_tac [`tops`,`shadow_sa`,`h2`,`h1`,`shadow_func`,`sa`,`s2`,`s1`,
                `dframe`,`data`,`addr`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Q.INST_TYPE [`:'b` |-> `:value`] stmtSimPropsTheory.expr_exit_INR_type,
       exprSimDefsTheory.halt_exit_def]
QED

Definition raw_call_kw_ready_def:
  raw_call_kw_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
    (tops,cenv,env,cx,st0) (s4,s5,h4,h5,kws,xs) (esD,t4,G4,tn4) <=>
    (!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    body_exprs_full_ok cx kws /\ body_inv tops ctx cenv cx /\
    body_const_cells_agree [(NONE,tops)] cx env esD /\
    shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env esD /\
    lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
    lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
      (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
    gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code s4 s5 func /\ fn_has_code h4 h5 shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv s4 /\
    (!fn inst s. frag_reachable ctx func t4 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    return_buf_frame dframe cenv s4 t4 /\ alloca_history func t4 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t4) /\
    (!H. valid_horizon cx st0 H esD.storage_trace ==>
      stmt_state_rel H ctx func cenv cx esD t4 /\
      storage_well_formed_on cx esD (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx esD G4 tn4 t4) /\
    ~t4.vs_halted /\ t4.vs_current_bb = s4.cs_current_bb /\
    t4.vs_inst_idx = LENGTH s4.cs_current_insts
End

Theorem raw_call_kw_ready_intro_full:
  raw_call_kw_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
    (tops,cenv,env,cx,st0) (s4,s5,h4,h5,kws,xs) (esD,t4,G4,tn4) /\
  (!v. storage_trace_frame (next v)) /\
  (!H exc ee gt r. expr_exit (INR exc) r /\ halt_exit H cx ee (INR exc) r ==>
    R H (INR exc) ee gt r) ==>
  raw_call_kw_intro
    (\i. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0)
    (DF,lo,dframe,ctx,shadow_ctx,func,PG) (cenv,cx,st0) (s4,s5,kws,xs)
    (esD,t4,G4,tn4) next Q R
Proof
  strip_tac >> irule raw_call_kw_intro_full >> simp[] >>
  qpat_x_assum `raw_call_kw_ready _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [raw_call_kw_ready_def]) >>
  mp_tac (Q.SPECL [`kws`,`DF`,`lo`,`dframe`,`ctx`,`shadow_ctx`,`PG`,`tops`,
     `func`,`shadow_func`,`cenv`,`env`,`cx`,`BaseT (UintT 256)`,
     `esD`,`st0`,`s4`,`s5`,`h4`,`h5`,`xs`,`t4`,`G4`,`tn4`]
     lower_word_args_sim_full) >>
  simp[combinTheory.K_DEF] >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]])) >>
  disch_then ACCEPT_TAC
QED
