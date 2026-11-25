(* Request prefixes for the fields of an already allocated struct. *)
Theory s1PrefixStructLitFields
Ancestors
  s1PrefixStructLitCodeCut s1PrefixStructLitFieldOutcome
  s1PrefixStructLitFieldSource s1PrefixPreds s1PrefixOfVV s1PrefixFrame
  bodyFullIfExpReach bodyFullHashKeccakFixed bodyFullStructLit
  bodyFullExprsListFacts bodyFullExprsSingleton
  exprSimAbiEncodeArgsLabelReplay exprSimFullBundleProps exprSimSource
  exprBodyPreProps exprSimHyps bodyMemoryDefs freshWrites typeLayoutProps
  gasContext exprSimDefs bodyFullPreds gasOutcomeFull exprLoweringProps
  s1PrefixDefs loweringPosts list pair option
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

Triviality singleton_admissible:
  expr_body_pre ce cx env e es ==>
  gas_admissible (eval_exprs cx [e])
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es
Proof
  disch_then (mp_tac o MATCH_MP exprSimSourceTheory.expr_body_pre_gas_admissible) >>
  simp[gas_admissible_def, abi_args_singleton_source] >>
  strip_tac >> rpt gen_tac >> Cases_on `rr` >> simp[] >>
  CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [bind_def]))) >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `_ = (raw,mid)` >> Cases_on `raw` >>
  simp[return_def] >> metis_tac[]
QED

Theorem structlit_fields_bundled_prefix:
  !inv'. inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword (:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME (p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) ==>
  !fs tys tvs es si sb shadow_si shadow_sb s0 G0 tn0 cells off out.
    compile_struct_lit compile_expr ce (StructT nsid) fs (Var root) off si = (out,sb) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) (Var root) off shadow_si = (out,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sb,shadow_si,shadow_sb) /\
    body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
    body_inv (cx_tops cx) ctx ce cx /\
    shadow_body_inv (cx_tops cx) ctx shadow_ctx /\
    body_exprs_full_ok cx (MAP SND fs) /\ body_exprs_prefix_ok cx (MAP SND fs) /\
    (?(Hbase : (bool # 256 word # type_value) list # num list).
      stmt_state_rel Hbase ctx func ce cx ees sf) /\
    LIST_REL (\t (name,e). ALOOKUP
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME (t,type_memory_bytes ce t)) tys fs /\
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    return_buf_frame d ce fr sf /\
    (!e st. MEM e (MAP SND fs) /\ expr_sim_inv ce cx env st ==>
      expr_body_pre ce cx env e st) /\
    (pure ==> ~EXISTS expr_has_effect (MAP SND fs)) /\ expr_sim_inv ce cx env es /\
    storage_trace_domain cx st0 es.storage_trace /\
    off + type_memory_size_list tvs <= capacity /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      inv' H es si G0 tn0 s0 cells off) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx (MAP SND fs)) (es,s0,G0,tn0)
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  Induct
  >- (simp[] >> rpt strip_tac >> irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame, Once evaluate_def, return_def] >>
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then mp_tac) >> simp[Abbr `inv'`, GSYM CONJ_ASSOC] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> PairCases_on `h` >> Cases_on `tys` >>
  gvs[LIST_REL_CONS1] >>
  rename1 `ALOOKUP _ fname = SOME (fty,type_memory_bytes ce fty)` >>
  rename1 `arg_type_fits (expr_type e) fty` >>
  rename1 `evaluate_type (get_tenv cx) fty = SOME ftv` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) rest_tys = SOME rest_tvs` >>
  `compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
     (MAP (I ## gas_shadow_expr) ((fname,e)::fs)) (Var root) off shadow_si = (out,shadow_sb)` by simp[] >>
  drule_all structlit_cons_code_cut >> strip_tac >>
  rename1 `compile_expr ce (expr_type e) e si = (vv,sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_si = (vv,shadow_sm)` >>
  rename1 `ci_mono sm ss` >> rename1 `ci_mono shadow_sm shadow_ss` >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `inv' (storage_trace_horizon es.storage_trace) es si G0 tn0 s0 cells off` by metis_tac[] >>
  `return_buf_frame d ce si s0` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`sf`,`fr`] >> simp[] >>
     qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
     simp[Abbr `inv'`, NoAsms, wb_frame_def, expr_sim_full_endpoint_def] >> metis_tac[]) >>
  `!st. expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st` by metis_tac[MEM] >>
  `expr_body_pre ce cx env e es` by simp[] >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    fs[Once body_exprs_full_ok_cons, Once body_exprs_prefix_ok_def] >>
  `type_memory_bytes ce fty = type_memory_size ftv` by
    metis_tac[expr_sim_inv_memory_size] >>
  suspend "head_prefix"
QED

Resume structlit_fields_bundled_prefix[head_prefix]:
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
    (rewrite_tac[gas_prefix_full_bind_read_result] >>
     qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`si`,`sm`,`shadow_si`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
       (qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
        simp[Abbr `inv'`, NoAsms] >>
        metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp]) >>
     impl_tac >-
       (qpat_assum `expr_sim_full_code _ (si,sm,shadow_si,shadow_sm)`
          (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
        drule_then assume_tac expr_body_pre_vv_gas_admissible >>
        `!H. valid_horizon cx st0 H es.storage_trace ==>
             stmt_state_rel H ctx func ce cx es s0 /\
             storage_well_formed_on cx es (FST H) /\
             ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0` by
          (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> inv' _ _ _ _ _ _ _ _`
             (drule_then mp_tac) >> simp[Abbr `inv'`, NoAsms] >> metis_tac[]) >>
        qpat_assum `inv' _ es si G0 tn0 s0 cells off` mp_tac >>
        simp[Abbr `inv'`, NoAsms, expr_sim_full_endpoint_def] >> strip_tac >> simp[] >>
        rpt strip_tac >> metis_tac[]) >> simp[]) >>
  suspend "head_outcome"
QED

Resume structlit_fields_bundled_prefix[head_outcome]:
  qabbrev_tac `Q = (\H (res:value list + exception) mid G tn t. ?v added.
    res = INL [v] /\ expr_sim_inv ce cx env mid /\ value_has_type ftv v /\
    inv' H mid ss G tn t (cells++added) (off+type_memory_size ftv) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
      fields_in_memory [(fname,v)] [(fname,ftv)] (addr+off) m))` >>
  qabbrev_tac `R = (\(H:(bool # 256 word # type_value) list # num list)
      (res:value list + exception) mid (gt:(string |-> num # num) # taint) r.
    ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
    halt_exit H cx mid (INR exc : eval_result + exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0) Q R` by
    (simp[Abbr `Q`, Abbr `R`] >> irule structlit_single_field_store_outcome >>
     `off + type_memory_size ftv <= capacity` by
       (fs[type_memory_size_list_sum] >> decide_tac) >>
     `body_exprs_full_ok cx [e]` by simp[body_exprs_full_ok_singleton] >>
     drule_then assume_tac singleton_admissible >> simp[] >>
     qpat_assum `compile_struct_lit _ ce _ [(fname,e)] _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_full_code _ (si,ss,shadow_si,shadow_ss)` (irule_at Any) >>
     qpat_assum `evaluate_type _ fty = SOME ftv` (irule_at Any) >>
     qexistsl_tac [`tnf`,`sf`,`pure`,`fr`,`ees`,`d`,`capacity`,`aid`,`Hbase`,`Gf`] >>
     simp[Abbr `inv'`, arithmeticTheory.ADD_COMM] >>
     conj_tac
     >- (rpt strip_tac >> qpat_assum `!fn inst s. frag_reachable _ _ s0 fn inst s ==> _`
          (drule_then ACCEPT_TAC)) >>
     qpat_assum `compile_struct_lit _ _ _ (MAP (I ## gas_shadow_expr) [(fname,e)])
                   _ _ shadow_si = (_,shadow_ss)`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [MAP, PAIR_MAP_THM, combinTheory.I_THM])) >>
  suspend "cons"
QED

Resume structlit_fields_bundled_prefix[cons]:
  qabbrev_tac `Qpath = (\H res mid G tn t. Q H res mid G tn t /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z))` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0) Qpath R` by
    (irule gas_outcome_full_post_path >> first_assum (irule_at Any) >>
     simp[Abbr `Qpath`] >> rpt gen_tac >> strip_tac >>
     qpat_assum `expr_sim_full_code _ (si,sm,shadow_si,shadow_sm)`
       (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
     `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (qpat_assum `body_inv _ ctx ce cx` mp_tac >>
        qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[body_inv_no_phi]) >>
     qpat_assum `gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (fn th => rpt strip_tac >> irule th) >>
     qpat_assum `frag_reachable _ _ t _ _ _` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (rpt strip_tac >> qpat_assum `!f i u. frag_reachable _ _ s0 f i u ==> _`
          (drule_then ACCEPT_TAC)))) >>
  irule structlit_fields_cons_prefix_from_singleton >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Qpath R` (irule_at Any) >>
  simp[Abbr `R`] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[sumTheory.ISR]) >>
  map_every qx_gen_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  suspend "tail"
QED

Resume structlit_fields_bundled_prefix[tail]:
  rename1 `gas_prefix_full _ _ _ _ (mid,t,G1,tn1)` >>
  qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `body_exprs_full_ok cx (MAP SND fs) /\ body_exprs_prefix_ok cx (MAP SND fs)` by
    (`?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                       read_result cx tv s1 = (INL v,t1)` suffices_by
       (disch_then (fn guard =>
          qpat_assum `body_exprs_full_ok cx (e::_)`
            (mp_tac o CONJUNCT2 o PURE_ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
          qpat_assum `body_exprs_prefix_ok cx (e::_)`
            (mp_tac o CONJUNCT2 o PURE_ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
          simp[guard])) >>
     qpat_assum `eval_expr cx e _ = (INL _,_)` (irule_at Any) >>
     first_assum (irule_at Any)) >>
  `body_const_cells_agree [(NONE,cx_tops cx)] cx env mid` by
    (`body_const_cells_agree [(NONE,cx_tops cx)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ _ = _` (irule_at Any) >>
     simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Qpath _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[Abbr `Qpath`, Abbr `Q`, NoAsms] >> strip_tac >>
  (* Choose the added cells at the trace's own horizon. Only the relation,
     storage well-formedness and ghost invariant depend on the horizon. *)
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     inv' H mid ss G1 tn1 t (cells++added) (off+type_memory_size ftv)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then mp_tac)) >>
     qpat_assum `inv' _ mid ss G1 tn1 t (cells++added) _` mp_tac >>
     simp[Abbr `inv'`, NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  suspend "induction"
QED

Resume structlit_fields_bundled_prefix[induction]:
  `si.cs_next_var <= ss.cs_next_var` by
    (qpat_assum `ci_mono si sm` mp_tac >> qpat_assum `ci_mono sm ss` mp_tac >>
     simp[NoAsms, ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `si` >> simp[] >> metis_tac[]) >>
  `off + type_memory_size ftv + type_memory_size_list rest_tvs <= capacity` by
    (qpat_assum `off + type_memory_size_list (ftv::rest_tvs) <= capacity` mp_tac >>
     simp[NoAsms, type_memory_size_list_sum] >> decide_tac) >>
  qpat_x_assum `!tys tvs' es' si' sb' shadow_si' shadow_sb' s0' G0' tn0' cells' off' out'. _`
    irule >>
  qpat_assum `expr_sim_full_code _ (ss,sb,shadow_ss,shadow_sb)` (irule_at Any) >>
  qpat_assum `OPT_MMAP _ rest_tys = SOME rest_tvs` (irule_at Any) >>
  qpat_assum `compile_struct_lit _ ce _ fs _ _ ss = _` (irule_at Any) >>
  qexists_tac `cells ++ added` >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  rpt strip_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])
QED

Finalise structlit_fields_bundled_prefix
