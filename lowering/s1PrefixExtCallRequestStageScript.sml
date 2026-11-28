(* Request-prefix companion to bodyFullExtCallRequestStage. *)
Theory s1PrefixExtCallRequestStage
Ancestors
  s1PrefixPreds bodyFullExtCallRequestStage s1PrefixDefs
  s1PrefixExtCallGuardedOperands s1PrefixExtCallTargetOutcome s1PrefixExtCallPosList
  s1PrefixExtCallKeywordHead s1PrefixExtCallKeywordList s1PrefixExtCallKeywordBind
  s1PrefixExtCallRequestPackingContinuation bodyFullExtCallKeywordPackedCut
  gasOutcomeFullCompose exprBodyPreProps bodyFullPreds list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule request_stage_source_boundary >> strip_tac >>
  Cases_on `args` >- gvs[] >> rename1 `addr::tail` >>
  drule_all_then
    (qx_choosel_then [`ao`,`av`,`vo`,`go`,`def`,`gas`,`s1`,`s2`,`s3`,`s5`,`result`,
       `shadow_s1`,`shadow_s2`,`shadow_s3`,`s5'`,`shadow_go`,`gas'`,`result'`]
       (map_every assume_tac o CONJUNCTS)) request_stage_paired_cuts >>
  RULE_ASSUM_TAC (SRULE [GSYM listTheory.MAP_DROP, GSYM listTheory.MAP_TAKE,
    listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss]) >>
  qabbrev_tac `xs = TAKE (LENGTH ats) tail` >>
  qabbrev_tac `kw_es = DROP (LENGTH ats) tail` >>
  simp[exprSimExtCallCaseTheory.eval_extcall_stages, GSYM arithmeticTheory.ADD1] >>
  ho_match_mp_tac (GEN_ALL extcall_guarded_operands_request_prefix) >>
  qexistsl [`tops`,`tail`,`av`,`s1`,`shadow_s1`,`shadow_s2`,`shadow_sa`,
            `shadow_func`,`s2`,`sa`,`LENGTH ats`,`kw_es`,`env`,`d`,`cenv`,
            `addr::tail`,`REPLICATE (LENGTH ats) ARB`,`ao`,`Q`] >>
  conj_tac >- MATCH_ACCEPT_TAC (GEN_ALL extcall_request_head_prefix) >>
  conj_tac >- MATCH_ACCEPT_TAC (GEN_ALL extcall_request_positional_packing_prefix) >>
  simp[exprSimFullBundlePropsTheory.expr_sim_full_code_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss,
       GSYM arithmeticTheory.ADD1] >>
  conj_tac
  >- (qpat_assum `!e st. (e = addr \/ MEM e tail) /\ _ ==> _` irule >>
      simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  conj_tac >- (rpt gen_tac >> disch_tac >> conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[Abbr `kw_es`] >> conj_tac >>
      first_assum (fn th =>
        drule_all_then ACCEPT_TAC (SIMP_RULE (srw_ss()) [GSYM arithmeticTheory.SUC_ONE_ADD] th))) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      metis_tac[rich_listTheory.MEM_TAKE, markerTheory.Abbrev_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_ext_call]) >>
  qx_genl_tac [`obs1`,`obs2`,`v`,`aw`,`mid`,`t`,`G1`,`tn1`,`vs`,`ee`,`u`,`G2`,`tn2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "keywords"
QED
*)
Theorem extcall_request_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats ==> body_exprs_full_ok cx (TAKE n (DROP 1 args))) /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats ==> body_exprs_prefix_ok cx (TAKE n (DROP 1 args))) /\
  (!st target mid n src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats /\ eval_exprs cx (TAKE n (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_full_ok cx (DROP (1 + n) args)) /\
  (!st target mid n src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats /\ eval_exprs cx (TAKE n (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_prefix_ok cx (DROP (1 + n) args)) /\
  body_exprs_full_ok cx (TAKE 1 args) /\
  body_exprs_prefix_ok cx (TAKE 1 args) /\
  compile_expr cenv ty (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
    sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!sp sr u result addr value gas buf off len hasdef def dt v vs kws target value_opt
     calldata ee t G tn.
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL [gas;addr;off;len;buf;
           Lit (n2w (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))]
         else emit_op CALL [gas;addr;value;off;len;buf;
           Lit (n2w (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
         comp_bind (fresh_label "extcall_cont") (\cont_lbl.
         comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
         (comp_ignore_bind (new_block fail_lbl)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
         comp_bind (compile_alloc_buffer 0) (\fb.
         comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
           (new_block cont_lbl)))))))))) sp = (u,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
         compile_default_return_path cenv rt dt buf r.buf_operand def addr skip
           (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (type_to_abi_dec_info cenv.ce_struct_fields cenv
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))
     else comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
       comp_bind
         (compile_return_value_decode
           (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))) (\hi.
       comp_ignore_bind
         (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi
            (type_to_abi_dec_info cenv.ce_struct_fields cenv
              (if needs_external_call_wrap rt then TupleT [rt] else rt)))
         (comp_return r.buf_operand)))) sr = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    fn_has_code sp sr func /\ fn_has_code sr sb func /\
    LENGTH vs = LENGTH ats /\ LENGTH kws = LENGTH opts /\ ext_call_opts_ok stat opts /\
    dest_AddressV v = SOME target /\
    value_opt = (if stat then NONE else
      case ext_call_kwarg EKValue opts kws of NONE => SOME 0 | SOME x => dest_NumV x) /\
    build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas buf off len
      (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
      target value_opt calldata hasdef def dt (ext_call_kwarg EKDefault opts kws) ee t /\
    (IS_SOME (ext_call_kwarg EKDefault opts kws) /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    (!gw g. eval_operand gas t = SOME gw /\
      OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
    (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt) <> 0 ==>
      ?p. buf = Var p /\
          ptr_covers G tn p t
            (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))) /\
    (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def G tn t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers G tn p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
          w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next))) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
      (ee,t,G,tn) Q (\H res ee gt r. expr_exit res r)) /\
  (!sp sr u result addr value gas buf off len hasdef def dt v vs kws target value_opt
     calldata ee t G tn.
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL [gas;addr;off;len;buf;
           Lit (n2w (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))]
         else emit_op CALL [gas;addr;value;off;len;buf;
           Lit (n2w (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
         comp_bind (fresh_label "extcall_cont") (\cont_lbl.
         comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
         (comp_ignore_bind (new_block fail_lbl)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
         comp_bind (compile_alloc_buffer 0) (\fb.
         comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fb.buf_operand;rds] [])
           (new_block cont_lbl)))))))))) sp = (u,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
         compile_default_return_path cenv rt dt buf r.buf_operand def addr skip
           (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (type_to_abi_dec_info cenv.ce_struct_fields cenv
             (if needs_external_call_wrap rt then TupleT [rt] else rt)))
     else comp_bind (compile_alloc_buffer (type_memory_bytes cenv rt)) (\r.
       comp_bind
         (compile_return_value_decode
           (abi_static_size cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))
           (abi_size_bound cenv.ce_struct_fields
             (if needs_external_call_wrap rt then TupleT [rt] else rt))) (\hi.
       comp_ignore_bind
         (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf hi
            (type_to_abi_dec_info cenv.ce_struct_fields cenv
              (if needs_external_call_wrap rt then TupleT [rt] else rt)))
         (comp_return r.buf_operand)))) sr = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    fn_has_code sp sr func /\ fn_has_code sr sb func /\
    LENGTH vs = LENGTH ats /\ LENGTH kws = LENGTH opts /\ ext_call_opts_ok stat opts /\
    dest_AddressV v = SOME target /\
    value_opt = (if stat then NONE else
      case ext_call_kwarg EKValue opts kws of NONE => SOME 0 | SOME x => dest_NumV x) /\
    build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas buf off len
      (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
      target value_opt calldata hasdef def dt (ext_call_kwarg EKDefault opts kws) ee t /\
    (IS_SOME (ext_call_kwarg EKDefault opts kws) /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    (!gw g. eval_operand gas t = SOME gw /\
      OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
    (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt) <> 0 ==>
      ?p. buf = Var p /\
          ptr_covers G tn p t
            (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))) /\
    (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def G tn t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers G tn p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
          w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next))) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
    (ee,t,G,tn)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_expr cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr))
    (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_prefix[keywords]:
  `!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (simp[Abbr `xs`] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  `!e st. MEM e kw_es /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (simp[Abbr `kw_es`] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_exprs >>
     qpat_assum `eval_exprs cx [addr] _ = (INL [v],mid)` (irule_at Any) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def,
         cj 13 vyperTypeSystemTheory.well_typed_expr_def]) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (irule body_const_cells_agree_exprs >>
     qpat_assum `eval_exprs cx xs _ = (INL vs,ee)` (irule_at Any) >>
     simp[constSubstCorrectTheory.frame_well_typed_exprs_every, EVERY_MEM] >>
     rpt strip_tac >>
     qpat_assum `!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==> _`
       (qspecl_then [`e`,`mid`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts)) >>
  `MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts` by
    (simp[Abbr `kw_es`] >> fs[GSYM arithmeticTheory.SUC_ONE_ADD]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    (conj_tac
     >- (qspecl_then [`cenv`,`BaseT AddressT`,`addr`,`sa`] mp_tac
           exprLoweringPropsTheory.ci_mono_lower_value_compile_expr >> simp[]) >>
     qspecl_then [`xs`,`MAP (lowered_value_type cenv) xs`,`compile_expr`,
       `cenv`,`kw_es`,`s1`] mp_tac exprLoweringPropsTheory.ci_mono_compile_ext_call_args >>
     simp[cj 1 exprLoweringPropsTheory.compile_expr_ci_mono]) >>
  `sa.cs_next_var <= s2.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then (strip_assume_tac o SRULE [bodyFullExtCallPosListTheory.extcall_positional_post_def])) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\
      extcall_positional_post F DF lo d ctx func cenv cx env kw_es xs av s1 s2 mid t G1 tn1 H
        (INL vs) ee G2 tn2 u`
    (drule_then (strip_assume_tac o SRULE [bodyFullExtCallPosListTheory.extcall_positional_post_def])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt opts
     (MAP gas_shadow_expr kw_es) shadow_s2 = ((vo,go,def),shadow_s3)` by
    (qpat_assum `shadow_go = go` (fn eq =>
       qpat_assum `compile_ext_call_kwargs _ _ _ _ _ shadow_s2 = _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx kw_es) (ee,u,G2,tn2)` by
    (irule extcall_request_keywords_prefix_from_head >>
     qpat_assum `compile_ext_call_kwargs _ cenv rt opts kw_es s2 = _` (irule_at Any) >>
     qexistsl [`tops`,`shadow_s3`,`shadow_s2`,`shadow_func`,`env`,`d`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (MATCH_ACCEPT_TAC (GEN_ALL extcall_keyword_head_prefix)) >>
     simp[]) >>
  qsuff_tac `?Qkw.
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx kw_es) (ee,u,G2,tn2) Qkw
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)) /\
    (!H res ke G tn z. Qkw H res ke G tn z ==> ?kws. res = INL kws) /\
    (!kw_marks kws ke G3 tn3 z.
      (!tail. eval_exprs cx kw_es
        (ee with gas_obs := gas_explicit kw_marks u.vs_gas_readings ++ tail) =
        (INL kws,ke with gas_obs := tail)) /\
      storage_trace_domain cx st0 ke.storage_trace /\ ke.gas_obs = [] /\
      (!H. valid_horizon cx st0 H ke.storage_trace ==> Qkw H (INL kws) ke G3 tn3 z) ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
        (ke,z,G3,tn3) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)) /\
      ?n zg Gg tng.
        (!H. valid_horizon cx st0 H ke.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng)) /\
        gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
          (ke,zg,Gg,tng))`
  >- suspend "join" >>
  irule_at Any bodyFullExtCallKeywordListTheory.extcall_request_keywords_owned_outcome >>
  qpat_assum `compile_ext_call_kwargs _ cenv rt opts kw_es s2 = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_s3`,`shadow_s2`,`shadow_func`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  BETA_TAC
  >- (rpt strip_tac >> rename1 `res = INL vals` >> qexists_tac `vals` >>
      first_assum ACCEPT_TAC) >>
  qx_genl_tac [`kw_marks`,`kws`,`ke`,`G3`,`tn3`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `xs = TAKE (LENGTH ats) tail` by simp[Abbr `xs`] >>
  mp_tac extcall_request_keyword_packed_cut >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
           (drule_then (ACCEPT_TAC o CONJUNCT1)))
     >- (qx_gen_tac `H` >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\
           extcall_positional_post F DF lo d ctx func cenv cx env kw_es xs av s1 s2 mid t G1 tn1 H
             (INL vs) ee G2 tn2 u`
           (drule_then (strip_assume_tac o SRULE [bodyFullExtCallPosListTheory.extcall_positional_post_def])) >>
         simp[])
     >> qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
     simp[])) >>
  disch_then (qx_choosel_then
    [`sp`,`sr`,`u_ret`,`value_op`,`buf`,`off`,`len`,`has_def`,`def_op`,`def_ty`,
     `target`,`value_opt`,`n`,`zg`,`Gg`,`tng`,`gw`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  suspend "physical"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_prefix[physical]:
  conj_tac
  >- (irule bodyFullRawCallGeneratedPrefixTheory.raw_call_generated_prefix_full >>
      conj_tac >- irule vyperStorageTraceTheory.storage_trace_frame_ext_call >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`Gg`,`n`,`zg`,`tng`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] (BETA_RULE (Q.SPEC
        `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
        (Q.GEN `R` bodyFullIntCallReturnHaltTheory.gas_outcome_full_halt_room)))) >>
      irule extcall_packed_exit_replay >>
      mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
        (Q.INST [`addr` |-> `ao`, `value` |-> `value_op`,
          `hasdef` |-> `has_def`, `def` |-> `def_op`, `dt` |-> `def_ty`,
          `u` |-> `u_ret`] bodyFullExtCallRequestPackingContinuationTheory.extcall_request_packing_continuation))) >>
      (impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp[NoAsms, SF ETA_ss] >> first_assum ACCEPT_TAC)) >>
      simp[NoAsms, SF ETA_ss]) >>
  qexistsl [`n`,`zg`,`Gg`,`tng`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (BETA_RULE (Q.INST [`addr` |-> `ao`, `value` |-> `value_op`,
     `hasdef` |-> `has_def`, `def` |-> `def_op`, `dt` |-> `def_ty`,
     `u` |-> `u_ret`] extcall_request_packing_continuation_prefix)) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[NoAsms, SF ETA_ss] >> first_assum ACCEPT_TAC)) >>
  simp[NoAsms, SF ETA_ss]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_prefix[join]:
  disch_then (qx_choose_then `Qkw` strip_assume_tac) >>
  reverse conj_tac
  >- (irule extcall_request_keyword_bind_prefix >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `Qkw` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >> first_assum (drule_all_then (ACCEPT_TAC o CONJUNCT2))) >>
  irule gas_outcome_full_bind_all >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_ext_call] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (qx_genl_tac [`left_marks`,`left_values`,`left_es`,`left_t`] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      qexistsl [`left_es`,`left_t`,`left_values`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[]) >>
  irule_at Any (Q.INST [`Q'` |-> `\H res ee G tn t. ee.gas_obs = [] /\ Qkw H res ee G tn t`]
    gas_outcome_full_post_source) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Qkw _` (irule_at Any) >>
  qexists_tac `Qkw` >> BETA_TAC >>
  conj_tac >- simp[NoAsms] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >>
      simp[stmtSimPropsTheory.expr_exit_INR_type, exprSimDefsTheory.halt_exit_def,
           exprSimDefsTheory.expr_exit_def]) >>
  qx_genl_tac [`kw_marks`,`kw_res`,`ke`,`G3`,`tn3`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ke.storage_trace) ke.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H res ke G tn z. Qkw H res ke G tn z ==> ?kws. res = INL kws`
    (drule_then (qx_choose_then `kws` SUBST_ALL_TAC)) >>
  disj1_tac >> qexists_tac `kws` >> conj_tac >- REFL_TAC >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==> Qkw H (INL kws) ke G3 tn3 z` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  first_assum (drule_all_then (ACCEPT_TAC o CONJUNCT1))
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extcall_request_prefix
*)
