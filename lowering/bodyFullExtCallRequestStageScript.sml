Theory bodyFullExtCallRequestStage
Ancestors
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullIntCallReturnHalt[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  bodyFullExtCallAddressOwnedPrefix bodyFullExtCallKeywordList
  bodyFullExtCallRequestPostGasPacking bodyFullExtCallRequestPackingContinuation
  bodyFullExtCallKeywordPackingRows bodyFullExtCallPackingReady
  bodyFullExtCallPacking bodyFullRawCallGas bodyFullRawCallGeneratedPrefix
  exprSimExtCallCase gasShadowCompile exprLowering
  gasShadowCompileHelpers gasShadowCompileStmtHelpers
  entryReachBodyFirstEmissionExprSupport entryReachBodyFirstEmissionExpr
  externalEntryShape gasShadowState gasShadowCompileConvert
  evalNoHalt exprSimDefs gasOutcomeFull
  bodyFullBuiltinWordPowCompose[qualified,ignore_grammar]
Libs
  pairLib

(* The compiler cuts used by the guarded operand outcomes. *)
Theorem request_stage_operands_layout[local]:
  compile_expr cenv ty
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::rest) dr) sa = (vv,sb) ==>
  ?ao av vo go def gas s1 s2 s3 s5 result.
    lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,s1) /\
    compile_ext_call_args compile_expr cenv (DROP (LENGTH ats) rest)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
      (TAKE (LENGTH ats) rest) s1 = (av,s2) /\
    compile_ext_call_kwargs compile_expr cenv rt opts
      (DROP (LENGTH ats) rest) s2 = ((vo,go,def),s3) /\
    (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
    compile_external_call_kwargs cenv ao av
      (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
      (abi_size_bound cenv.ce_struct_fields
        (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
      (cenv.ce_method_id name ats)
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (abi_static_size cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (type_memory_bytes cenv rt) stat
      (case vo of SOME v => v | NONE => Lit 0w) gas skip
      (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
      rt (case def of SOME (d,dt) => dt | NONE => rt)
      (type_to_abi_dec_info cenv.ce_struct_fields cenv
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      s5 = (result,sb) /\
    vv = (if rt = NoneT then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[exprSimSendTheory.compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[AllCaseEqs()] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* Only the ExtCall typing clause is needed to seed the operand cuts. *)
Theorem request_stage_source_boundary[local]:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es ==>
  ann = rt /\ dr = NONE /\ ext_call_opts_ok stat opts /\
  LENGTH args = 1 + LENGTH ats + LENGTH opts /\
  expr_type (HD args) = BaseT AddressT /\
  arg_types_fit (MAP expr_type (TAKE (LENGTH ats) (TL args))) ats /\
  MAP expr_type (DROP (1 + LENGTH ats) args) = MAP (ext_call_kw_type rt) opts /\
  (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st)
Proof
  rw[exprSimHypsDefsTheory.expr_body_pre_def,
     cj 13 vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[exprSimHypsDefsTheory.byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
      vyperTypeCallGraphTheory.int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.supported_exprs_exists_every,
      listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >>
  imp_res_tac exprSimSourceTheory.well_typed_exprs_member >>
  imp_res_tac exprSimSourceTheory.byte_widths_exprs_mem >>
  imp_res_tac exprSimSourceTheory.alloc_limits_exprs_mem >>
  imp_res_tac exprSimSourceTheory.call_evaluation_safe_exprs_mem >>
  gvs[GSYM listTheory.EVERY_MEM] >>
  imp_res_tac exprSimSourceTheory.int_calls_exprs_every_mem >>
  gvs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]
QED

(* Pair the positional cuts, including the snapshots chosen by the unchanged
   mutation test. The generic shadow proof is private to its compiler theory. *)
Theorem request_stage_pos_shadow_cut[local]:
  gas_shadow_state a a' /\
  compile_ext_call_args compile_expr ce kws tys xs a = (av,b) /\
  compile_ext_call_args compile_expr ce (MAP gas_shadow_expr kws) tys
    (MAP gas_shadow_expr xs) a' = (av',b') ==>
  av' = av /\ gas_shadow_state b b'
Proof
  `!xs kws tys. gas_shadow_compiles (compile_ext_call_args compile_expr ce kws tys xs)
    (compile_ext_call_args compile_expr ce (MAP gas_shadow_expr kws) tys
      (MAP gas_shadow_expr xs))` suffices_by
    (simp[gas_shadow_compiles_def] >> metis_tac[pairTheory.FST,pairTheory.SND]) >>
  Induct >> rpt gen_tac >> Cases_on `tys` >>
  simp[compile_ext_call_args_def, gas_shadow_compiles_return] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- metis_tac[cj 1 gas_shadow_compile_expr,boolTheory.COND_CLAUSES] >>
  gen_tac >> BETA_TAC >> match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (ONCE_REWRITE_TAC[GSYM listTheory.MAP_APPEND] >>
      simp[gas_shadow_expr_can_mutate, gas_shadow_compiles_snapshot_vv]) >>
  gen_tac >> BETA_TAC >> irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_return]
QED

(* The packed source action no longer evaluates the operands. Its recorded
   replay suffices to exclude Halt, without changing the endpoint or path. *)
Theorem extcall_packed_exit_replay[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_ext_call cx stat skip sig opts vs) (ke,zg,Gg,tng) Q
    (\H res ee gt r. expr_exit res r) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_ext_call cx stat skip sig opts vs) (ke,zg,Gg,tng) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      `res <> INR HaltException` by
        (qpat_assum `!tail. eval_ext_call cx _ _ _ _ _ _ = _`
           (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[eval_ext_call_nh]) >>
      rpt strip_tac >> res_tac >> fs[halt_exit_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The continuation starts before the optional code check, with the physical
   request at the endpoint chosen by operand evaluation and ABI packing. *)
Theorem extcall_request_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats ==> body_exprs_full_ok cx (TAKE n (DROP 1 args))) /\
  (!st target mid n src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats /\ eval_exprs cx (TAKE n (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_full_ok cx (DROP (1 + n) args)) /\
  body_exprs_full_ok cx (TAKE 1 args) /\
  compile_expr cenv ty (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
    sa = (vv,sb) /\
  compile_expr cenv ty (gas_shadow_expr
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_no_wrap inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
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
      (ee,t,G,tn) Q (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr))
    (es,s0,G0,tn0) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  simp[LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule request_stage_source_boundary >> strip_tac >>
  Cases_on `args` >- gvs[] >> rename1 `addr::tail` >>
  drule request_stage_operands_layout >> strip_tac >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _`
    (mp_tac o SRULE [cj 11 gasShadowTheory.gas_shadow_expr_def, listTheory.MAP]) >>
  disch_then (strip_assume_tac o MATCH_MP request_stage_operands_layout) >>
  simp[listTheory.MAP_DROP, listTheory.MAP_TAKE] >>
  RULE_ASSUM_TAC (SRULE [GSYM listTheory.MAP_DROP, GSYM listTheory.MAP_TAKE,
    listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss]) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr addr) shadow_sa = (shadow_ao,shadow_s1)` >>
  `shadow_ao = ao /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`e` |-> `addr`, `ty` |-> `BaseT AddressT`]
        gas_shadow_stmt_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_all request_stage_pos_shadow_cut >> strip_tac >>
  qabbrev_tac `xs = TAKE (LENGTH ats) tail` >>
  qabbrev_tac `kw_es = DROP (LENGTH ats) tail` >>
  rename1 `compile_ext_call_args _ _ _ _ _ shadow_s1 = (shadow_av,shadow_s2)` >>
  rename1 `compile_ext_call_kwargs _ _ rt opts (MAP gas_shadow_expr kw_es) shadow_s2 =
      ((shadow_vo,shadow_go,shadow_def),shadow_s3)` >>
  `gas_shadow_compiles (compile_ext_call_kwargs compile_expr cenv rt opts kw_es)
      (compile_ext_call_kwargs compile_expr cenv rt opts (MAP gas_shadow_expr kw_es))` by
    (mp_tac (Q.INST [`return_type` |-> `rt`, `sh` |-> `T`]
      (MATCH_MP gas_shadow_compiles_ext_call_kwargs (cj 1 gas_shadow_compile_expr))) >> simp[]) >>
  `shadow_vo = vo /\ shadow_go = go /\ shadow_def = def /\ gas_shadow_state s3 shadow_s3` by
    (qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`s2`,`shadow_s2`] mp_tac) >> simp[]) >>
  `cs_extends sa s1 /\ cs_extends shadow_sa shadow_s1` by
    (mp_tac (MATCH_MP externalEntryShapeTheory.lower_value_labels
                     (cj 1 externalEntryShapeTheory.compile_expr_labels)) >>
     disch_then (fn th =>
       qspecl_then [`cenv`,`BaseT AddressT`,`addr`,`sa`] mp_tac th >>
       qspecl_then [`cenv`,`BaseT AddressT`,`gas_shadow_expr addr`,`shadow_sa`] mp_tac th) >>
     simp[]) >>
  `cs_extends s1 s2 /\ cs_extends shadow_s1 shadow_s2` by
    (conj_tac >> irule (cj 1 (MATCH_MP first_emission_ext_call_args
                                      (cj 1 first_emission_compile_expr))) >> metis_tac[]) >>
  `cs_extends s2 s3 /\ cs_extends shadow_s2 shadow_s3` by
    (conj_tac >> irule (cj 1 (MATCH_MP first_emission_ext_call_kwargs
                                      (cj 1 first_emission_compile_expr))) >> metis_tac[]) >>
  `cs_extends s3 s5 /\ cs_extends shadow_s3 s5'` by
    (Cases_on `go` >> fs[compileEnvTheory.cs_extends_refl] >>
     metis_tac[cj 1 emit_op_labels,pairTheory.SND]) >>
  `cs_extends s5 sb /\ cs_extends s5' shadow_sb` by
    metis_tac[cj 1 compile_external_call_kwargs_labels,pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 s5 func /\ fn_has_code s5 sb func /\
   fn_has_code shadow_sa shadow_s1 shadow_func /\
   fn_has_code shadow_s1 shadow_s2 shadow_func /\
   fn_has_code shadow_s2 shadow_s3 shadow_func /\
   fn_has_code shadow_s3 s5' shadow_func` by
    (rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     rpt (qpat_x_assum `!_. _` kall_tac) >>
     metis_tac[compileEnvTheory.cs_extends_refl, compileEnvTheory.cs_extends_trans]) >>
  simp[exprSimExtCallCaseTheory.eval_extcall_stages, GSYM arithmeticTheory.ADD1] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  qexistsl [`Q`,`\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  ho_match_mp_tac (GEN_ALL extcall_request_guarded_operand_prefix_address_owned) >>
  (* Supply the choices of the already observed real and shadow compiler cuts. *)
  qexistsl [`tops`,`tail`,`av`,`s1`,`shadow_s1`,`shadow_s2`,`shadow_sa`,
            `shadow_func`,`s2`,`sa`,`LENGTH ats`,`kw_es`,`env`,`d`,`cenv`,
            `addr::tail`,`REPLICATE (LENGTH ats) ARB`,`ao`] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss,
       GSYM arithmeticTheory.ADD1] >>
  conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
        (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
      strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `!st target mid src vs ee. _ ==> body_exprs_full_ok _ (DROP _ _)` mp_tac >>
      simp[Abbr `kw_es`, GSYM arithmeticTheory.ADD1]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      metis_tac[rich_listTheory.MEM_TAKE, markerTheory.Abbrev_def]) >>
  conj_tac
  >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_ext_call]) >>
  qx_genl_tac [`obs1`,`obs2`,`v`,`aw`,`mid`,`t`,`G1`,`tn1`,
               `vs`,`ee`,`u`,`G2`,`tn2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (simp[Abbr `xs`] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  `!e st. MEM e kw_es /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (simp[Abbr `kw_es`] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts` by
    gvs[Abbr `kw_es`] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    (conj_tac
     >- (qspecl_then [`cenv`,`BaseT AddressT`,`addr`,`sa`] mp_tac
           exprLoweringPropsTheory.ci_mono_lower_value_compile_expr >> simp[]) >>
     qspecl_then [`xs`,`MAP (lowered_value_type cenv) xs`,`compile_expr`,
       `cenv`,`kw_es`,`s1`] mp_tac exprLoweringPropsTheory.ci_mono_compile_ext_call_args >>
     simp[cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,Abbr `kw_es`]) >>
  `sa.cs_next_var <= s2.cs_next_var` by (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_ext_call] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (qx_genl_tac [`left_marks`,`left_values`,`left_es`,`left_t`] >>
      rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      qexistsl [`left_es`,`left_t`,`left_values`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[]) >>
  irule_at Any
    (Q.INST [`Q'` |-> `\H res ee G tn t. ee.gas_obs = [] /\ Q H res ee G tn t`]
      gasOutcomeFullComposeTheory.gas_outcome_full_post_source) >>
  irule_at Any extcall_request_keywords_owned_outcome >>
  qpat_assum `compile_ext_call_kwargs _ _ rt opts kw_es s2 = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_s3`,`shadow_s2`,`shadow_func`,`env`,`d`] >>
  asm_rewrite_tac[] >> simp[NoAsms] >>
  conj_tac
  >- (qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
         (assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
          stmt_state_rel _ _ _ _ _ ee u /\ _`
        (drule_then (ACCEPT_TAC o MATCH_MP
          bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1))) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
          stmt_state_rel _ _ _ _ _ ee u /\ _`
        (drule_then (fn th => ACCEPT_TAC (CONJ (cj 1 th)
          (CONJ (cj 2 th) (cj 3 th)))))) >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >>
    simp[stmtSimPropsTheory.expr_exit_INR_type, halt_exit_def, expr_exit_def]) >>
  qx_genl_tac [`kw_marks`,`kw_res`,`ke`,`G3`,`tn3`,`z`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ke.storage_trace) ke.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ ke.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ke.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `kws` (map_every assume_tac o CONJUNCTS))) >>
  disj1_tac >> qexists `kws` >> simp[] >>
  `eval_exprs cx kw_es (ee with gas_obs := gas_explicit kw_marks u.vs_gas_readings) =
     (INL kws,ke)` by
    (`ke with gas_obs := [] = ke` by simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_exprs cx kw_es _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `storage_trace_frame (eval_exprs cx kw_es)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `?extra. ke.storage_trace = ee.storage_trace ++ extra` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ke z /\
       storage_well_formed_on cx ke (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ke G3 tn3 z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h ke.storage_trace ==> ke.gas_obs = [] /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `kw_res = INL kws` (fn th => SIMP_TAC std_ss [th]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s2.cs_next_var <= s3.cs_next_var /\ s2.cs_next_id <= s3.cs_next_id` by
    (`!ks ys a. ci_mono a (SND (compile_ext_call_kwargs compile_expr cenv rt ks ys a))` by
       (Induct >> Cases_on `ys` >> rpt strip_tac >>
        simp[compile_ext_call_kwargs_def, exprLoweringPropsTheory.ci_mono_comp_return] >>
        ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
        >- simp[exprLoweringPropsTheory.ci_mono_compile_ext_call_kwarg,
                cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
        rpt strip_tac >> simp[pairTheory.UNCURRY] >>
        ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >>
        simp[pairTheory.UNCURRY, exprLoweringPropsTheory.ci_mono_comp_return]) >>
     pop_assum (qspecl_then [`opts`,`kw_es`,`s2`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace /\
       stmt_state_rel H ctx func cenv cx ke z /\
       ghost_inv_at (DF H) lo d cenv cx ke G3 tn3 z` by simp[] >>
  `ci_mono s2 s3` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> simp[]) >>
  `ci_mono s3 s5` by
    (Cases_on `go` >> fs[]
     >- (qspec_then `GAS` (qspecl_then [`[]`,`s3`] mp_tac)
           exprLoweringPropsTheory.ci_mono_emit_op >> simp[]) >>
     fs[exprLoweringPropsTheory.ci_mono_refl]) >>
  `local_ptrs_reserved cenv s3 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x)` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `s2` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s2` >> simp[]) >>
  qabbrev_tac `source_gas = ext_call_kwarg EKGas opts kws` >>
  `(!g. go = SOME g ==> ?w. eval_operand g z = SOME w /\ op_taint tn3 g = {} /\
       (!n. OPTION_BIND source_gas dest_NumV = SOME n ==> n = w2n w)) /\
   (!n. OPTION_BIND source_gas dest_NumV = SOME n ==> IS_SOME go)` by
    (qpat_assum `case source_gas of NONE => go = NONE | SOME x =>
         ?op w. go = SOME op /\ _ /\ _ /\ dest_NumV x = SOME (w2n w) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `source_gas` >> simp[] >>
     strip_tac >> simp[] >> qexists `w` >> simp[]) >>
  `?zg Gg tng gw n.
     eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
     (!k. OPTION_BIND source_gas dest_NumV = SOME k ==> k = w2n gw) /\
     ~zg.vs_halted /\ zg.vs_current_bb = s5.cs_current_bb /\
     zg.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func zg /\
     zg.vs_memory = z.vs_memory /\ zg.vs_allocas = z.vs_allocas /\
     zg.vs_alloca_next = z.vs_alloca_next /\ zg.vs_fmp = z.vs_fmp /\
     zg.vs_labels = z.vs_labels /\
     tng.t_mem = tn3.t_mem /\ tng.t_stor = tn3.t_stor /\
     tng.t_trans = tn3.t_trans /\ tng.t_imm = tn3.t_imm /\
     (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
       FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
     (!H. valid_horizon cx st0 H ke.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng) /\
       ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg /\
       stmt_state_rel H ctx func cenv cx ke zg /\
       storage_well_formed_on cx ke (FST H) /\
       ghost_kept_at lo cenv ke s3 G3 tn3 z Gg tng)` by
    (Cases_on `go`
     >- (mp_tac (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`,
           `sa` |-> `s3`, `sb` |-> `s5`, `shadow_sa` |-> `shadow_s3`, `shadow_sb` |-> `s5'`,
           `shadow_gas` |-> `gas'`, `s` |-> `z`, `G` |-> `G3`, `tn` |-> `tn3`,
           `es` |-> `ke`] raw_call_optional_gas_joint) >>
         (impl_tac >-
           (qpat_assum `(case NONE of NONE => _ | SOME _ => _) = (gas,s5)`
              (assume_tac o SIMP_RULE std_ss []) >>
            qpat_assum `shadow_go = NONE` (fn eq =>
              qpat_assum `(case shadow_go of NONE => _ | SOME _ => _) = (gas',s5')`
                (assume_tac o SIMP_RULE std_ss [eq])) >>
            simp_tac std_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==>
                stmt_state_rel _ _ _ _ _ ke z /\ storage_well_formed_on _ _ _ /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
         disch_then (qx_choose_then `zg0` (qx_choose_then `Gg0`
           (qx_choose_then `tng0` (qx_choose_then `gw0`
             (strip_assume_tac o SIMP_RULE (srw_ss()) []))))) >>
         qexistsl [`zg0`,`Gg0`,`tng0`,`gw0`,`1`] >>
         `!k. OPTION_BIND source_gas dest_NumV <> SOME k` by
           (qpat_assum `!k. OPTION_BIND source_gas dest_NumV = SOME k ==> IS_SOME NONE` mp_tac >>
            simp_tac std_ss [optionTheory.IS_SOME_DEF]) >>
         `REPLICATE 1 F = [F]` by EVAL_TAC >>
         pop_assum (fn th => rewrite_tac [th]) >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         pure_once_asm_rewrite_tac[] >> simp[venomStateTheory.update_var_def] >>
         qpat_assum `!k. OPTION_BIND source_gas dest_NumV <> SOME k` (fn th => simp_tac std_ss [th])) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s5)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     qpat_assum `!g. SOME _ = SOME g ==> _` (qspec_then `gas` mp_tac) >>
     simp_tac std_ss [] >> strip_tac >>
     qexistsl [`z`,`G3`,`tn3`,`w`,`0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  irule raw_call_generated_prefix_full >>
  conj_tac >- irule vyperStorageTraceTheory.storage_trace_frame_ext_call >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gg`,`n`,`zg`,`tng`] >>
  conj_tac >- (rpt strip_tac >> qpat_assum
    `!H. valid_horizon _ _ H ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> simp[]) >>
  `!x. not_fresh_at s2 x ==> not_fresh_at s3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `wb_frame cenv ee ke s2 u zg` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`s3`,`z`] >> simp[]) >>
  `ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng` by
    (pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >>
     qpat_assum `tng.t_mem = tn3.t_mem` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ghost_kept_at lo cenv ee s2 G2 tn2 u G3 tn3`
       (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     conj_tac >- (qx_gen_tac `x` >> disch_tac >>
       qpat_assum `!y. not_fresh_at s3 y ==> lookup_var y zg = _ /\ _`
         (qspec_then `x` mp_tac) >>
       qpat_assum `!y. not_fresh_at s2 y ==> FLOOKUP G3 y = _ /\ _`
         (qspec_then `x` mp_tac) >> simp[]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `(!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==> lookup_var x zg = SOME w) /\
   (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP zg.vs_allocas aid = SOME row) /\
   u.vs_alloca_next <= zg.vs_alloca_next /\ zg.vs_labels = u.vs_labels` by simp[] >>
  `s2.cs_next_var <= s5.cs_next_var /\ s2.cs_next_id <= s5.cs_next_id /\
   sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_id <= s5.cs_next_id` by
    (map_every
       (fn q => qpat_assum q
         (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]))
       [`ci_mono sa s1`, `ci_mono s1 s2`, `ci_mono s2 s3`, `ci_mono s3 s5`] >>
     decide_tac) >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace /\
       stmt_state_rel H ctx func cenv cx ke zg /\
       ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg` by
    (gen_tac >> disch_tac >> conj_tac >- simp[] >>
     qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       drule >> simp[]) >>
  `~exprs_can_mutate cenv kw_es ==>
     ke.scopes = ee.scopes /\ ke.immutables = ee.immutables /\
     (!tr. get_storage cx ke tr = get_storage cx ee tr)` by
    (strip_tac >>
     `get_module_code cx NONE = SOME tops` by
       (qpat_assum `body_inv tops ctx cenv cx`
          (ACCEPT_TAC o cj 3 o REWRITE_RULE [bodySimTheory.body_inv_def])) >>
     `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
        (int_calls_exprs kw_es)` by
       (simp[bodyStorageCasesTheory.body_exprs_main_calls_every, listTheory.EVERY_MEM] >>
        rpt strip_tac >>
        `expr_body_pre cenv cx env e ee` by
          (qpat_assum `!e st. MEM e kw_es /\ _ ==> _`
             (qspecl_then [`e`,`ee`] mp_tac) >> simp[]) >>
        qpat_assum `expr_body_pre cenv cx env e ee`
          (mp_tac o Q.SPEC `c` o REWRITE_RULE [listTheory.EVERY_MEM] o cj 8 o
           REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
        simp[]) >>
     drule_all targetPureWalkSourceTheory.nonmutating_exprs_source_frame >>
     simp[vyperMachineFrameTheory.machine_frame_def] >> strip_tac >>
     gen_tac >> Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `MAP FDOM ke.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `eval_exprs cx kw_es (ee with gas_obs := _) = (INL kws,ke)`
       (mp_tac o MATCH_MP
         vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >>
     simp[]) >>
  mp_tac (Q.INST [`sa` |-> `s1`, `sb` |-> `s2`, `se` |-> `s5`, `svs` |-> `av`,
           `kw_es` |-> `kw_es`, `env` |-> `env`,
           `pos` |-> `ee`, `ee` |-> `ke`, `t` |-> `zg`, `Gp` |-> `G2`,
           `tp` |-> `tn2`, `G` |-> `Gg`, `tn` |-> `tng`]
    extcall_keyword_packing_rows) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >~ [`?H. valid_horizon cx st0 H ke.storage_trace`]
     >- (qexists_tac `storage_trace_horizon ke.storage_trace` >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee u /\ _`
       mp_tac >>
     simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  disch_then (mk_asm "packing_rows") >>
  qpat_assum `compile_external_call_kwargs _ ao av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 = _`
    (mp_tac o MATCH_MP extcall_request_buffer_layout) >>
  disch_then (qx_choose_then `ba` (qx_choose_then `sb1` (qx_choose_then `sb2`
    (qx_choose_then `len` (qx_choose_then `sb3` (qx_choose_then `off`
    (qx_choose_then `sp` (qx_choose_then `sr` (qx_choose_then `u_ret`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))))))) >>
  `cs_extends s5 sb1 /\ cs_extends sb1 sb2 /\ cs_extends sb3 sp` by
    (conj_tac
     >- (qpat_assum `compile_alloc_buffer _ s5 = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 compile_alloc_buffer_labels,pairTheory.SND]) >>
     conj_tac
     >- (qpat_assum `emit_void _ _ sb1 = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 emit_void_labels,pairTheory.SND]) >>
     qpat_assum `emit_op _ _ sb3 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 emit_op_labels,pairTheory.SND]) >>
  sg `cs_extends sb2 sb3`
  >- (qpat_assum `(if av = [] then _ else _) sb2 = (_,sb3)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : operand # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> IF_CASES_TAC >> simp[comp_return_labels] >>
      qmatch_goalsub_abbrev_tac `SND (f sb2)` >>
      sg `!s. cs_extends s (SND (f s)) /\
             EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
      >- (gen_tac >> simp[Abbr `f`] >>
          rpt (FIRST [irule comp_bind_labels, irule comp_ignore_bind_labels] >>
            conj_tac >> rpt gen_tac >> BETA_TAC >>
            simp[emit_op_labels,compile_abi_encode_values_to_buf_labels])) >>
      first_x_assum (qspec_then `sb2` (ACCEPT_TAC o CONJUNCT1))) >>
  sg `cs_extends sp sr`
  >- (qpat_assum `comp_ignore_bind _ _ sp = (_,sr)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : string # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> qmatch_goalsub_abbrev_tac `SND (f sp)` >>
      sg `!s. cs_extends s (SND (f s)) /\
             EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
      >- (gen_tac >> simp[Abbr `f`] >>
          rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
                      irule comp_bind_labels >> conj_tac >> rpt gen_tac,
                      irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
            BETA_TAC >> simp[emit_inst_labels,emit_op_labels,emit_void_labels,
                             compile_alloc_buffer_labels]) >>
          TRY (irule new_block_action_labels >> simp[]) >>
          IF_CASES_TAC >> simp[emit_op_labels,comp_return_labels,compile_extcodesize_check_labels]) >>
      first_x_assum (qspec_then `sp` (ACCEPT_TAC o CONJUNCT1))) >>
  sg `cs_extends sr sb`
  >- (qpat_assum `(if rt = NoneT then _ else _) sr = (_,sb)`
        (SUBST1_TAC o GSYM o REWRITE_RULE [pairTheory.SND] o
         AP_TERM ``SND : operand # compile_state -> compile_state``) >>
      POP_ASSUM_LIST (K ALL_TAC) >> IF_CASES_TAC >> simp[comp_return_labels] >>
      IF_CASES_TAC >>
      (qmatch_goalsub_abbrev_tac `SND (f sr)` >>
       sg `!s. cs_extends s (SND (f s)) /\
              EVERY (isPREFIX "@") (added_labels s (SND (f s)))`
       >- (gen_tac >> simp[Abbr `f`] >>
           rpt (FIRST [irule comp_bind_labels, irule comp_ignore_bind_labels] >>
             conj_tac >> rpt gen_tac >> BETA_TAC >>
             simp[compile_alloc_buffer_labels,compile_default_return_path_labels,
                  compile_return_value_decode_labels,compile_abi_decode_labels,comp_return_labels])) >>
       first_x_assum (qspec_then `sr` (ACCEPT_TAC o CONJUNCT1)))) >>
  sg `fn_has_code s5 sb1 func /\ fn_has_code sb1 sb2 func /\
      fn_has_code sb2 sb3 func /\ fn_has_code sb3 sp func /\
      fn_has_code sp sr func /\ fn_has_code sr sb func`
  >- (qpat_assum `fn_has_code s5 sb func` mp_tac >>
      POP_ASSUM_LIST (map_every assume_tac o
        List.filter (can (match_term ``cs_extends (a:compile_state) b``) o concl)) >>
      disch_tac >> rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
      simp[] >> qexistsl [`sb`,`s5`] >>
      metis_tac[compileEnvTheory.cs_extends_refl,compileEnvTheory.cs_extends_trans]) >>
  qabbrev_tac `tys = MAP (lowered_value_type cenv) xs` >>
  qabbrev_tac `rty = if needs_external_call_wrap rt then TupleT [rt] else rt` >>
  qabbrev_tac `cap = abi_size_bound cenv.ce_struct_fields rty` >>
  qabbrev_tac `value_op = option_CASE vo (Lit 0w) I` >>
  qabbrev_tac `value_opt = if stat then NONE else
    option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV` >>
  qabbrev_tac `def_op = case def of NONE => Lit 0w | SOME (dop,dt) => dop` >>
  qabbrev_tac `def_ty = case def of NONE => rt | SOME (dop,dt) => dt` >>
  qabbrev_tac `has_def = IS_SOME def` >>
  qabbrev_tac `pack_h = storage_trace_horizon ke.storage_trace` >>
  qabbrev_tac `entry_h = storage_trace_horizon es.storage_trace` >>
  `storage_trace_frame (eval_exprs cx [addr])` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `?obs. mid.storage_trace = es.storage_trace ++ obs` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 entry_h es.storage_trace` by
    (`storage_trace_domain cx st0 es.storage_trace` by
       (qpat_assum `mid.storage_trace = es.storage_trace ++ obs` (fn eq =>
          qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
            (ACCEPT_TAC o MATCH_MP vyperStorageFootprintTheory.storage_trace_domain_prefix o
             PURE_REWRITE_RULE [eq]))) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     simp[NoAsms, Abbr `entry_h`]) >>
  `valid_horizon cx st0 pack_h ee.storage_trace` by
    simp[Abbr `pack_h`] >>
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee u /\ _`
    (qspec_then `pack_h` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs = LENGTH ats` by
    (qpat_assum `eval_exprs cx xs _ = (INL vs,ee)`
       (mp_tac o MATCH_MP vyperInterpreterTheory.eval_exprs_length) >>
     qpat_assum `arg_types_fit (MAP expr_type xs) ats`
       (mp_tac o MATCH_MP listTheory.LIST_REL_LENGTH o
        REWRITE_RULE [vyperTypeArgFitsTheory.arg_types_fit_LIST_REL]) >>
     simp[]) >>
  `LENGTH kws = LENGTH opts` by
    (qpat_assum `MAP expr_type (DROP (1 + LENGTH ats) (addr::tail)) = _`
       (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
     simp[Abbr `kw_es`, GSYM arithmeticTheory.ADD1]) >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`H0` |-> `entry_h`, `H` |-> `pack_h`,
      `t0` |-> `t`, `target` |-> `w2w (aw:256 word) : 160 word`,
      `obs3` |-> `gas_explicit kw_marks u.vs_gas_readings`]
      (INST_TYPE [alpha |-> ``:160``] extcall_request_post_gas_packing)))) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (asm "packing_rows" ACCEPT_TAC) >> TRY REFL_TAC
     >~ [`xs = TAKE _ _`] >- simp[Abbr `xs`]
     >~ [`compile_alloc_buffer _ s5 = _`]
     >- (qpat_assum `compile_alloc_buffer _ s5 = _` mp_tac >>
         simp[NoAsms, Abbr `tys`, Abbr `cap`, Abbr `rty`])
     >~ [`(if av = [] then _ else _) sb2 = _`]
     >- (qpat_assum `(if av = [] then _ else _) sb2 = _` mp_tac >>
         simp[NoAsms, Abbr `tys`, listTheory.MAP_MAP_o, combinTheory.o_DEF])
     >~ [`stmt_state_rel entry_h _ _ _ _ es s0`]
     >- (qpat_assum `!K. valid_horizon _ _ K es.storage_trace ==> _`
           (qspec_then `entry_h` mp_tac) >> simp[])
     >- (rpt strip_tac >> qpat_assum
           `!K. valid_horizon _ _ K ke.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           drule >> simp[])
     >~ [`rt = NoneT ==> _`]
     >- (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
           (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def,
             cj 13 vyperTypeSystemTheory.well_typed_expr_def]) >>
         strip_tac >> simp[vyperTypeExtCallSoundnessTheory.ext_call_kwarg_not_mem]) >>
     simp[Abbr `source_gas`])) >>
  disch_then (mk_asm "packed") >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  qexistsl [`Q`,`\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[] >>
  irule (BETA_RULE (Q.SPEC
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
    (Q.GEN `R` bodyFullIntCallReturnHaltTheory.gas_outcome_full_halt_room))) >>
  irule extcall_packed_exit_replay >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`addr` |-> `ao`, `value` |-> `value_op`,
      `buf` |-> `ba.buf_operand`, `hasdef` |-> `has_def`,
      `def` |-> `def_op`, `dt` |-> `def_ty`, `u` |-> `u_ret`,
      `target` |-> `w2w (aw:256 word) : 160 word`] extcall_request_packing_continuation))) >>
  BETA_TAC >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
     >- (qpat_assum `comp_ignore_bind _ _ sp = (_,sr)` mp_tac >>
         simp[NoAsms, Abbr `value_op`, Abbr `cap`, Abbr `rty`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `vo` >> simp[combinTheory.I_THM])
     >- (qpat_assum `(if rt = NoneT then _ else _) sr = (_,sb)` mp_tac >>
         simp[NoAsms, Abbr `cap`, Abbr `rty`, Abbr `has_def`, Abbr `def_op`, Abbr `def_ty`])
     >- (simp[NoAsms, Abbr `value_opt`] >>
         Cases_on `ext_call_kwarg EKValue opts kws` >> simp[NoAsms])
     >- (asm "packed" mp_tac >>
         simp[NoAsms, Abbr `value_op`, Abbr `value_opt`, Abbr `has_def`,
              Abbr `def_op`, Abbr `def_ty`]) >>
     qpat_assum `!sp sr u result. _` mp_tac >>
     simp_tac std_ss [Abbr `cap`, Abbr `rty`, optionTheory.OPTION_BIND_EQUALS_OPTION,
          listTheory.EVERY_DEF, SF ETA_ss])) >>
  simp[NoAsms, SF ETA_ss]
QED
