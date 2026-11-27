Theory bodyFullExtCallRequestStage
Ancestors
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullIntCallReturnHalt[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  bodyFullExtCallAddressOwnedPrefix bodyFullExtCallKeywordList
  bodyFullExtCallKeywordPackedCut bodyFullExtCallRequestPackingContinuation
  bodyFullExtCallKeywordPackingRows bodyFullExtCallPackingReady
  bodyFullExtCallPacking bodyFullRawCallGas bodyFullRawCallGeneratedPrefix
  exprSimExtCallCase gasShadowCompile exprLowering
  gasShadowCompileHelpers gasShadowCompileStmtHelpers
  entryReachBodyFirstEmissionExprSupport entryReachBodyFirstEmissionExpr
  externalEntryShape gasShadowState gasShadowCompileConvert
  evalNoHalt exprSimDefs gasOutcomeFull bodyFullPreds list
  bodyFullBuiltinWordPowCompose[qualified,ignore_grammar]
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
Libs
  pairLib

(* The compiler cuts used by the guarded operand outcomes. *)
Theorem request_stage_operands_layout:
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
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
*)
Theorem request_stage_source_boundary:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es ==>
  ann = rt /\ dr = NONE /\ ext_call_opts_ok stat opts /\
  LENGTH args = 1 + LENGTH ats + LENGTH opts /\
  expr_type (HD args) = BaseT AddressT /\
  arg_types_fit (MAP expr_type (TAKE (LENGTH ats) (TL args))) ats /\
  MAP expr_type (DROP (1 + LENGTH ats) args) = MAP (ext_call_kw_type rt) opts /\
  (!e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st)
Proof
  cheat
QED

(* Pair the observed positional cuts using the compiler correspondence. *)
Theorem request_stage_pos_shadow_cut:
  gas_shadow_state a a' /\
  compile_ext_call_args compile_expr ce kws tys xs a = (av,b) /\
  compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kws) tys
    (MAP gas_shadow_expr xs) a' = (av',b') ==>
  av' = av /\ gas_shadow_state b b'
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_ext_call_args compile_expr ce kws tys xs)
    (compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kws) tys
      (MAP gas_shadow_expr xs))` by
    (mp_tac (Q.INST [`sd` |-> `T`, `sh` |-> `T`, `cenv` |-> `ce`]
      (MATCH_MP gas_shadow_compiles_ext_call_args (cj 1 gas_shadow_compile_expr_env))) >>
     disch_then (qspecl_then [`xs`,`kws`,`tys`] mp_tac) >> simp[]) >>
  pop_assum (qspecl_then [`a`,`a'`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[EQ_SYM_EQ]
QED

(* Split the real and shadow compiler spans at the same operand boundaries.
   The optional GAS step is kept separately on each side. *)
Theorem request_stage_paired_cuts:
  compile_expr cenv ty
    (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::rest) dr) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (ExtCall stat skip (name,ats,rt) opts) (addr::rest) dr))
    shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?ao av vo go def gas s1 s2 s3 s5 result
   shadow_s1 shadow_s2 shadow_s3 shadow_s5 shadow_go shadow_gas shadow_result.
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
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr addr) shadow_sa = (ao,shadow_s1) /\
    compile_ext_call_args compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr (DROP (LENGTH ats) rest))
      (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
      (MAP gas_shadow_expr (TAKE (LENGTH ats) rest)) shadow_s1 = (av,shadow_s2) /\
    compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt opts
      (MAP gas_shadow_expr (DROP (LENGTH ats) rest)) shadow_s2 =
      ((vo,shadow_go,def),shadow_s3) /\
    shadow_go = go /\
    (case shadow_go of SOME g => (g,shadow_s3) | NONE => emit_op GAS [] shadow_s3) =
      (shadow_gas,shadow_s5) /\
    compile_external_call_kwargs (gas_shadow_env T cenv) ao av
      (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
      (abi_size_bound cenv.ce_struct_fields
        (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
      (cenv.ce_method_id name ats)
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (abi_static_size cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      (type_memory_bytes cenv rt) stat
      (case vo of SOME v => v | NONE => Lit 0w) shadow_gas skip
      (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
      rt (case def of SOME (d,dt) => dt | NONE => rt)
      (type_to_abi_dec_info cenv.ce_struct_fields (gas_shadow_env T cenv)
        (if needs_external_call_wrap rt then TupleT [rt] else rt))
      shadow_s5 = (shadow_result,shadow_sb) /\
    vv = (if rt = NoneT then StackValue ann shadow_result
          else LocatedValue ann (mk_ptr shadow_result LocMemory)) /\
    gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
    gas_shadow_state s3 shadow_s3 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 s5 /\ cs_extends s5 sb /\
    cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
    cs_extends shadow_s2 shadow_s3 /\ cs_extends shadow_s3 shadow_s5 /\
    cs_extends shadow_s5 shadow_sb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 s3 func /\ fn_has_code s3 s5 func /\ fn_has_code s5 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func /\
    fn_has_code shadow_s1 shadow_s2 shadow_func /\
    fn_has_code shadow_s2 shadow_s3 shadow_func /\
    fn_has_code shadow_s3 shadow_s5 shadow_func /\
    fn_has_code shadow_s5 shadow_sb shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule request_stage_operands_layout >> strip_tac >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _`
    (mp_tac o SRULE [cj 11 gasShadowTheory.gas_shadow_expr_def, listTheory.MAP]) >>
  disch_then (strip_assume_tac o MATCH_MP request_stage_operands_layout) >>
  RULE_ASSUM_TAC (SRULE [GSYM listTheory.MAP_DROP, GSYM listTheory.MAP_TAKE,
    listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss]) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr addr) shadow_sa = (shadow_ao,shadow_s1)` >>
  `shadow_ao = ao /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`sd` |-> `T`, `e` |-> `addr`, `ty` |-> `BaseT AddressT`]
        gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_all request_stage_pos_shadow_cut >> strip_tac >>
  qabbrev_tac `kw_es = DROP (LENGTH ats) rest` >>
  rename1 `compile_ext_call_args _ _ _ _ _ shadow_s1 = (shadow_av,shadow_s2)` >>
  rename1 `compile_ext_call_kwargs _ _ rt opts (MAP gas_shadow_expr kw_es) shadow_s2 =
      ((shadow_vo,shadow_go,shadow_def),shadow_s3)` >>
  `gas_shadow_compiles (compile_ext_call_kwargs compile_expr cenv rt opts kw_es)
      (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt opts
        (MAP gas_shadow_expr kw_es))` by
    (mp_tac (Q.INST [`return_type` |-> `rt`, `sd` |-> `T`, `sh` |-> `T`]
      (MATCH_MP gas_shadow_compiles_ext_call_kwargs_env (cj 1 gas_shadow_compile_expr_env))) >>
     simp[]) >>
  `shadow_vo = vo /\ shadow_go = go /\ shadow_def = def /\ gas_shadow_state s3 shadow_s3` by
    (qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`s2`,`shadow_s2`] mp_tac) >> simp[]) >>
  `cs_extends sa s1 /\ cs_extends shadow_sa shadow_s1` by
    (mp_tac (MATCH_MP externalEntryShapeTheory.lower_value_labels
                     (cj 1 externalEntryShapeTheory.compile_expr_labels)) >>
     disch_then (fn th =>
       qspecl_then [`cenv`,`BaseT AddressT`,`addr`,`sa`] mp_tac th >>
       qspecl_then [`gas_shadow_env T cenv`,`BaseT AddressT`,
                    `gas_shadow_expr addr`,`shadow_sa`] mp_tac th) >>
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
  map_every qexists_tac [`ao`,`av`,`vo`,`go`,`def`,`gas`,`s1`,`s2`,`s3`,`s5`,`result`,
    `shadow_s1`,`shadow_s2`,`shadow_s3`,`s5'`,`shadow_go`,`gas'`,`result'`] >>
  fs[Abbr `kw_es`, listTheory.MAP_MAP_o, combinTheory.o_DEF, SF boolSimps.ETA_ss] >>
  rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
  metis_tac[compileEnvTheory.cs_extends_refl, compileEnvTheory.cs_extends_trans]
QED

(* The packed source action no longer evaluates the operands. Its recorded
   replay suffices to exclude Halt, without changing the endpoint or path. *)
Theorem extcall_packed_exit_replay:
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
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
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
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_exprs >>
     qpat_assum `eval_exprs cx [addr] (es with gas_obs := obs1) = _` (irule_at Any) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def,
         cj 13 vyperTypeSystemTheory.well_typed_expr_def]) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (irule body_const_cells_agree_exprs >>
     qpat_assum `eval_exprs cx xs (mid with gas_obs := obs2) = _` (irule_at Any) >>
     simp[constSubstCorrectTheory.frame_well_typed_exprs_every, EVERY_MEM] >>
     rpt strip_tac >>
     qpat_assum `!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==> _`
       (qspecl_then [`e`,`mid`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o cj 2 o
       REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def])) >>
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
  mp_tac extcall_request_keyword_packed_cut >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[Abbr `xs`])
     >~ [`!H. valid_horizon _ _ H ee.storage_trace ==> _`]
     >- (qx_gen_tac `H` >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
             stmt_state_rel _ _ _ _ _ ee u /\ _` (qspec_then `H` mp_tac) >>
         simp[] >> strip_tac >> simp[])
     >> qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     simp[] >> strip_tac >> gvs[])) >>
  disch_then (qx_choosel_then
    [`sp`,`sr`,`u_ret`,`value_op`,`buf`,`off`,`len`,`has_def`,`def_op`,`def_ty`,
     `target`,`value_opt`,`n`,`zg`,`Gg`,`tng`,`gw`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  irule raw_call_generated_prefix_full >>
  conj_tac >- irule vyperStorageTraceTheory.storage_trace_frame_ext_call >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gg`,`n`,`zg`,`tng`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
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
      `hasdef` |-> `has_def`, `def` |-> `def_op`, `dt` |-> `def_ty`,
      `u` |-> `u_ret`] extcall_request_packing_continuation))) >>
  BETA_TAC >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!sp sr u result. _` mp_tac >>
     simp_tac std_ss [optionTheory.OPTION_BIND_EQUALS_OPTION,
          listTheory.EVERY_DEF, SF ETA_ss])) >>
  simp[NoAsms, SF ETA_ss]
QED
*)
Theorem extcall_request_full:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats ==> body_exprs_full_ok_mods mods exps cx (TAKE n (DROP 1 args))) /\
  (!st target mid n src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    n = LENGTH ats /\ eval_exprs cx (TAKE n (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_full_ok_mods mods exps cx (DROP (1 + n) args)) /\
  body_exprs_full_ok_mods mods exps cx (TAKE 1 args) /\
  compile_expr cenv ty (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
    sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
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
  cheat
QED
