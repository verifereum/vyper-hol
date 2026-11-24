(*
 * raw_call with calldata over the finite-horizon joint judgment.
 * Its lowering emits a DALLOCA into the function.
 *
 * TOP-LEVEL:
 *   raw_call_calldata_expr_full_ok -- the raw_call-with-calldata case
 *)
Theory bodyFullRawCallCalldata
Ancestors
  bodyFullPreds bodySimFull rawCallCalldataDalloca exprSimHypsDefs exprSimHyps fragExec
  ptrDiscipline exprLowering exprSimSend builtinSystem compileEnv context emitHelper
  exprSimRawCall bodyFullWordArgs bodyFullRawCallRequestGas exprSimSource
  exprSimHash vyperTyping valueEncoding exprSimWordArgs exprSimPrecompiles exprLoweringProps loweringPosts
  vyperTypeExtCallSoundness vyperTypeSystem vyperAST vyperValue vyperInterpreter
  vyperState venomState words list option
  bodyFullRawCall bodyFullRawCallCalldataCopy bodyFullOfVV bodyFullRawCallGas
  bodyFullRawCallGeneratedPrefix bodyFullRawCallOutbuf bodyFullPathHistory
  bodyFullShadowBodyInv bodyFullRawCallHeader bodyFullHashKeccakFixed bodyPtrDefs bodyMemoryDefs
  gasOutcomeFullCompose gasExemptCert gasShadowCompileHelpers gasShadowCompileStmtHelpers
  gasShadowCompile gasShadowState gasShadow fragGasOriginPtr
  vyperStorageFootprint exprSafeOperand stateRelProj loweringStateRelDefs allocaHistory
  finite_map pred_set arithmetic bodyFullEmptyLeafData exprSimFullBundleProps
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem raw_call_calldata_compile[local]:
  compile_expr cenv ty (Call ann (RawCallCalldataTarget flags) (a::kws) dflt) sa =
    (vv,sb) ==>
  ?addr vo go ignored gas ov op dp len result s1 s2 s3 s4 s5.
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s1 =
      ((vo,go,ignored),s2) /\
    (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,op),s4) /\
    compile_msg_data_to_memory s4 = ((dp,len),s5) /\
    compile_raw_call_finish addr dp len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s5 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `flags.rcf_max_outsize = 0` >> gvs[]
QED

Theorem raw_call_calldata_pre[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es ==>
  ?a kws. args = a::kws /\ expr_type a = BaseT AddressT /\
    LENGTH kws = LENGTH flags.rcf_kws /\ raw_call_kws_ok flags kws /\
    ann = raw_call_return_type flags /\ dflt = NONE /\
    ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    flags.rcf_max_outsize < dimword (:256)
Proof
  Cases_on `args` >> simp[expr_body_pre_def, well_typed_expr_def]
QED

Theorem raw_call_calldata_word_args[local]:
  !kws sa. EVERY (\e. expr_type e = BaseT (UintT 256)) kws ==>
    lower_word_args cenv expr_type kws sa =
      lower_word_args cenv (K (BaseT (UintT 256))) kws sa
Proof
  Induct >> simp[exprSimWordArgsTheory.lower_word_args_def] >>
  rpt strip_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem raw_call_calldata_args_ready[local]:
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (a::kws) NONE) es ==>
  !e ee. MEM e (a::kws) /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)
Proof
  disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule expr_body_pre_raw_call_target_arg >> simp[] >>
      qexistsl [`ann`,`a::kws`,`NONE`,`es`,`flags`,`RawCallCalldataTarget flags`] >>
      simp[]) >>
  drule raw_call_calldata_pre >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_call_kwargs_types >> strip_tac >>
  qpat_assum `MEM e (a::kws)` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  fs[is_word_type_def, EVERY_MEM]
QED

Theorem raw_call_calldata_source_ready[local]:
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (a::kws) NONE) es /\
  eval_exprs cx (a::kws) (es with gas_obs := gs) = (INL vs,mid) /\
  typed_args_post H ctx func cenv cx es sa s0 mid (a::kws) (addr::xs) vs t ==>
  ?target av kvs amount.
    vs = av::kvs /\ dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
    expr_sim_inv cenv cx env mid /\ eval_operand addr t = SOME (w2w target) /\
    raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
                   NONE => Lit 0w | SOME p => p) t = SOME (n2w amount) /\
    amount < dimword (:256) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
    (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
      ?p w. ext_call_kwarg EKGas flags.rcf_kws xs = SOME p /\
            eval_operand p t = SOME w /\ g = w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_call_calldata_pre >> simp[] >> strip_tac >>
  drule raw_call_calldata_args_ready >> strip_tac >>
  drule raw_call_kwargs_types >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [ETA_THM]) >>
  rename1 `bind (eval_expr cx a) (read_result cx) _ = (INL av,ea)` >>
  rename1 `eval_exprs cx kws ea = (INL kvs,mid)` >>
  `expr_body_pre cenv cx env a (es with gas_obs := gs)` by
    (qpat_assum `!e ee. _ ==> expr_body_pre _ _ _ e ee /\ _`
       (qspecl_then [`a`,`es with gas_obs := gs`] mp_tac) >>
     fs[expr_body_pre_def]) >>
  `expr_sim_inv cenv cx env ea /\ value_has_type (BaseTV AddressT) av` by
    (drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_base_result) >> simp[]) >>
  `?target. dest_AddressV av = SOME target /\
    typed_val_to_w256 (BaseTV AddressT) av = w2w target` by
    (qpat_assum `value_has_type (BaseTV AddressT) av` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `av` >> simp[value_has_type_def,dest_AddressV_def] >>
     strip_tac >> simp[typed_val_to_w256_def] >>
     qspec_then `l` mp_tac
       (INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]
         venomMemPropsTheory.w2w_word_of_bytes_be_pad_left) >>
     simp[dividesTheory.compute_divides, fcpLib.INDEX_CONV ``dimindex(:160)``, EQ_SYM_EQ]) >>
  `EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws` by
    (mp_tac (Q.INST [`target` |-> `RawCallCalldataTarget flags`, `args` |-> `a::kws`,
       `ann` |-> `raw_call_return_type flags`, `dflt` |-> `NONE`]
       raw_call_keywords_pre_for_target) >> simp[]) >>
  drule_all raw_call_keyword_values >> strip_tac >>
  `eval_operand addr t = SOME (w2w target) /\
    LIST_REL (\x v. eval_operand x t = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs kvs` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`typed_args_post H ctx func cenv cx es sa s0 mid (a::kws) (addr::xs) (av::kvs) t`,
        `EVERY (\e. expr_type e = BaseT (UintT 256)) kws`,
        `expr_type a = BaseT AddressT`,
        `typed_val_to_w256 (BaseTV AddressT) av = w2w target`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[typed_args_post_def, EVERY_EL, LIST_REL_EL_EQN, LENGTH_ZIP, EL_ZIP] >>
     rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
  drule_all raw_call_value_operand >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `LIST_REL (\x v. ?w. eval_operand x t = SOME w /\ dest_NumV v = SOME (w2n w))
    xs kvs` by
    (qpat_assum `LIST_REL _ xs kvs` mp_tac >>
     qpat_assum `EVERY (value_has_type (BaseTV (UintT 256))) kvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[uint256_typed_dest]) >>
  `(flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0` by
    (strip_tac >> `~MEM EKValue flags.rcf_kws` by fs[raw_call_kws_ok_def] >>
     qpat_assum `~MEM EKValue flags.rcf_kws` (fn th =>
       qpat_assum `raw_call_value flags.rcf_kws kvs = SOME amount` mp_tac >>
       simp[NoAsms,raw_call_value_def,
            MATCH_MP (SPEC_ALL ext_call_kwarg_not_mem) th] >>
       disch_then (ACCEPT_TAC o SYM))) >>
  `!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
      ?p w. ext_call_kwarg EKGas flags.rcf_kws xs = SOME p /\
            eval_operand p t = SOME w /\ g = w2n w` by
    (Cases_on `ext_call_kwarg EKGas flags.rcf_kws kvs` >> simp[] >>
     qspecl_then [`flags.rcf_kws`,`xs`,`kvs`,`x`] mp_tac raw_call_selected_gas_word >>
     simp[] >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[optionTheory.SOME_11]) >>
  qexistsl [`target`,`amount`] >> simp[]
QED

Theorem raw_call_calldata_eval:
  eval_expr cx (Call ann (RawCallCalldataTarget flags) args NONE) =
  bind (eval_exprs cx args) (\vs. do
    type_check (LENGTH vs = 1 + LENGTH flags.rcf_kws) "raw_call calldata args";
    target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 1 vs)) "raw_call value";
    eval_raw_call cx flags target cx.txn.calldata amount
      (ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs))
  od)
Proof
  simp[Once evaluate_def]
QED

Theorem raw_call_calldata_word_schedule:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es /\
  compile_expr cenv ty (Call ann (RawCallCalldataTarget flags) args dflt) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (RawCallCalldataTarget flags) args dflt)) shadow_sa =
    (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?a kws addr xs vo go gas ov op dp len result s2 s3 s4 s5 h2 h3.
    args = a::kws /\ dflt = NONE /\ ann = raw_call_return_type flags /\
    flags.rcf_max_outsize < dimword (:256) /\
    expr_sim_inv cenv cx env es /\ type_alloc_ok cenv (raw_call_return_type flags) /\
    (!e ee. MEM e (a::kws) /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    lower_word_args cenv expr_type (a::kws) sa = (addr::xs,s2) /\
    lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr (a::kws))
      shadow_sa = (addr::xs,h2) /\
    vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
    go = ext_call_kwarg EKGas flags.rcf_kws xs /\
    (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
    (case go of SOME g => (g,h2) | NONE => emit_op GAS [] h2) = (gas,h3) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,op),s4) /\
    compile_msg_data_to_memory s4 = ((dp,len),s5) /\
    compile_raw_call_finish addr dp len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s5 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    gas_shadow_state s2 h2 /\ gas_shadow_state s3 h3 /\
    EVERY (safe_operand s2) (addr::xs) /\
    ci_mono sa s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s4 s5 /\
    ci_mono shadow_sa h2 /\ ci_mono h2 h3 /\
    cs_extends s5 sb /\ cs_extends h3 shadow_sb /\
    fn_has_code sa s2 func /\ fn_has_code s2 s3 func /\
    fn_has_code s3 s4 func /\ fn_has_code s4 s5 func /\
    fn_has_code shadow_sa h2 shadow_func /\ fn_has_code h2 h3 shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_call_calldata_pre >>
  disch_then (qx_choose_then `a` (qx_choose_then `kws`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `args = a::kws` SUBST_ALL_TAC >>
  qpat_x_assum `ann = raw_call_return_type flags` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = NONE` SUBST_ALL_TAC >>
  qpat_x_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` (K all_tac) >>
  drule raw_call_calldata_args_ready >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ type_alloc_ok cenv (raw_call_return_type flags)` by
    fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
  drule raw_call_calldata_compile >> strip_tac >>
  `?h1. lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
       (gas_shadow_expr a) shadow_sa = (addr,h1) /\ gas_shadow_state s1 h1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (BaseT AddressT) a)
        (lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
          (gas_shadow_expr a))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     metis_tac[pairTheory.PAIR]) >>
  `?h2. compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
       (MAP gas_shadow_expr kws) h1 = ((vo,go,ignored),h2) /\ gas_shadow_state s2 h2` by
    (`gas_shadow_compiles
       (compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws)
       (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
          (MAP gas_shadow_expr kws))` by
        (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`sd` |-> `T`,`sh` |-> `T`]
          gas_shadow_compiles_ext_call_kwargs_env)) >>
         simp[cj 1 gas_shadow_compile_expr_env]) >>
     qpat_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`s1`, `h1`] mp_tac) >> simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h3. (case go of SOME g => (g,h2) | NONE => emit_op GAS [] h2) = (gas,h3) /\
        gas_shadow_state s3 h3` by
    (Cases_on `go` >> gvs[] >-
     (mp_tac (Q.INST [`opc` |-> `GAS`, `opc'` |-> `GAS`, `ops` |-> `[]`]
        gas_shadow_compiles_emit_op) >>
      rewrite_tac[gas_shadow_compiles_def] >>
      disch_then (qspecl_then [`s2`, `h2`] mp_tac) >> simp[] >>
      metis_tac[pairTheory.PAIR]) >> metis_tac[]) >>
  drule raw_call_kwargs_types >> strip_tac >>
  qpat_assum `compile_ext_call_kwargs _ _ _ _ kws s1 = _`
    (mp_then (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`) mp_tac
      raw_call_kwargs_word_args) >> simp[] >> strip_tac >>
  `lower_word_args cenv expr_type (a::kws) sa = (addr::xs,s2)` by
    simp[lower_word_args_cons, raw_call_calldata_word_args] >>
  `?ys. lower_word_args (gas_shadow_env T cenv) expr_type
          (MAP gas_shadow_expr (a::kws)) shadow_sa = (addr::ys,h2)` by
    (qpat_assum `compile_ext_call_kwargs _ _ _ _ (MAP gas_shadow_expr kws) h1 = _`
       (mp_then (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`) mp_tac
         raw_call_kwargs_word_args) >>
     simp[] >> disch_then (qx_choose_then `ys` (map_every assume_tac o CONJUNCTS)) >>
     `EVERY (\e. expr_type e = BaseT (UintT 256)) (MAP gas_shadow_expr kws)` by
       simp[EVERY_MAP,combinTheory.o_DEF,gas_shadow_expr_type] >>
     qexists_tac `ys` >> simp[lower_word_args_cons,raw_call_calldata_word_args,gas_shadow_expr_type]) >>
  `lower_word_args (gas_shadow_env T cenv) expr_type
       (MAP gas_shadow_expr (a::kws)) shadow_sa = (addr::xs,h2)` by
    (`gas_shadow_compiles (lower_word_args cenv expr_type (a::kws))
       (lower_word_args (gas_shadow_env T cenv) expr_type
         (MAP gas_shadow_expr (a::kws)))` by
       (irule gas_shadow_compiles_lower_word_args >> simp[gas_shadow_expr_type]) >>
     pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     qpat_x_assum `lower_word_args _ _ (MAP gas_shadow_expr (a::kws)) _ = _`
       (assume_tac o REWRITE_RULE [MAP]) >>
     simp[]) >>
  `wb_args_shape cenv expr_type (a::kws)` by
    (rewrite_tac[wb_args_shape_def] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `lower_value _ _ (expr_type e) e _ = _`
       (mp_then (Pat `lower_value _ _ _ _ _ = _`)
         (qspecl_then [`cx`,`env`,`es`] mp_tac) expr_body_pre_lower_value_word_shape) >>
     impl_tac >- (qpat_assum `!e ee. MEM e (a::kws) /\ _ ==> _`
       (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `EVERY (safe_operand s2) (addr::xs)` by
    (qpat_assum `EVERY (\x. (!z. x = Var z ==> not_fresh_at s2 z) /\
                           (!l. x <> Label l)) (addr::xs)` mp_tac >>
     rewrite_tac[EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
     rename1 `MEM opnd (addr::xs)` >>
     first_x_assum drule >> Cases_on `opnd` >> simp[safe_operand_def]) >>
  `ci_mono sa s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s4 s5 /\
    ci_mono shadow_sa h2 /\ ci_mono h2 h3` by
    (rpt conj_tac
     >- qpat_assum `lower_word_args _ _ _ sa = (_,s2)`
          (ACCEPT_TAC o MATCH_MP (SPEC_ALL ci_mono_lower_word_args))
     >- (Cases_on `go` >> gvs[] >> metis_tac[ci_mono_emit_op,ci_mono_refl,pairTheory.SND])
     >- metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND]
     >- metis_tac[ci_mono_compile_msg_data_to_memory,pairTheory.SND]
     >- qpat_assum `lower_word_args _ _ _ shadow_sa = (_,h2)`
          (ACCEPT_TAC o MATCH_MP (SPEC_ALL ci_mono_lower_word_args))
     >- (Cases_on `go` >> gvs[] >> metis_tac[ci_mono_emit_op,ci_mono_refl,pairTheory.SND])) >>
  `cs_extends s5 sb /\ cs_extends h3 shadow_sb` by
    (conj_tac >- metis_tac[ci_mono_compile_raw_call_finish,ci_mono_def,pairTheory.SND] >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_expr_def,listTheory.MAP,optionTheory.OPTION_MAP_DEF] >>
     disch_then (strip_assume_tac o MATCH_MP raw_call_calldata_compile) >>
     gvs[gas_shadow_expr_type] >>
     mp_tac (Q.SPECL [`flags.rcf_max_outsize`,`h3`] ci_mono_compile_raw_call_outbuf) >>
     mp_tac (Q.SPEC `s4'` ci_mono_compile_msg_data_to_memory) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s5' = _`
       (fn th =>
         let val args = snd (strip_comb (lhs (concl th)))
         in mp_tac (SPECL args ci_mono_compile_raw_call_finish) end) >>
     simp[ci_mono_def] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s2 func /\ fn_has_code s2 s3 func /\
    fn_has_code s3 s4 func /\ fn_has_code s4 s5 func /\
    fn_has_code shadow_sa h2 shadow_func /\ fn_has_code h2 h3 shadow_func` by
    (fs[ci_mono_def] >> rpt conj_tac >>
     metis_tac[fn_has_code_mid,cs_extends_trans,cs_extends_refl]) >>
  qexistsl [`addr`,`xs`,`gas`,`ov`,`op`,`dp`,`len`,
            `result`,`s2`,`s3`,`s4`,`s5`,`h2`,`h3`] >>
  fs[] >>
  qpat_assum `!e ee. _ ==> expr_body_pre _ _ _ e ee /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

(* Keep the request and copy contracts at the guarded supplier sites.  Their
   input formulas are taken verbatim from the ordinary producer statements. *)
val calldata_request_full = REWRITE_RULE [post_value_type_def]
  (Q.INST [`e` |-> `Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (a::kws) NONE`,
    `bs` |-> `cx.txn.calldata`, `ib` |-> `w2n tout.vs_fmp`,
    `s6` |-> `s3`, `sout` |-> `s4`, `s7` |-> `s5`] raw_call_continuation_full);
val calldata_request_by =
  let val (pre,answer) = dest_imp (concl calldata_request_full)
      val (_, [_,_,_,_,src,init,post,exit]) = strip_comb answer
  in ``^pre ==> A (s5:compile_state) ^src ^init ^post ^exit`` end;

val calldata_copy_run = Q.INST [`sa` |-> `s4`, `sb` |-> `s5`, `s` |-> `tout`,
  `G` |-> `Gout`, `tn` |-> `tnout`, `dl` |-> `len`,
  `marks` |-> `marksK ++ REPLICATE n F`] calldata_memory_joint_run;
val calldata_copy_by =
  let val (pre,answer) = dest_imp (concl calldata_copy_run)
      val (witnesses,post) = strip_exists answer
      val (t :: _) = witnesses
      val scoped_post = ``^post /\ Seg (s4:compile_state) (s5:compile_state)
          (tout:venom_state) ([]:bool list) ^t``
      val enriched = list_mk_exists (witnesses, scoped_post)
  in ``^pre ==> ^enriched`` end;

val calldata_next = ``\vs. do
  type_check (LENGTH vs = 1 + LENGTH flags.rcf_kws) "raw_call calldata args";
  target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
  amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 1 vs)) "raw_call value";
  eval_raw_call cx flags target cx.txn.calldata amount
    (ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs))
od``;
val calldata_list_post = ``\H (rr : value list + vyperState$exception) mid G tn t.
    (?vs. rr = INL vs /\
      typed_args_post H ctx func cenv cx es sa s0 mid (a::kws) (addr::xs) vs t /\
      t.vs_current_bb = s2.cs_current_bb /\
      t.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF (H : (bool # 256 word # type_value) list # num list))
        lo dframe cenv cx mid G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      EVERY (\x. op_taint tn x = {}) (addr::xs)) /\ ~t.vs_halted /\ mid.gas_obs = []``;
val calldata_qvv = ``expr_vv_sim_full_post
  ((DF : (bool # 256 word # type_value) list # num list -> dead),lo,dframe,ctx,func) cenv cx
  (Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (a::kws) NONE)
  (es,sa,sb,s0,vv,G0,tn0) :
  (bool # 256 word # type_value) list # num list -> eval_result + vyperState$exception ->
  evaluation_state -> (string |-> num # num) -> taint -> venom_state -> bool``;
val calldata_rvv = ``\(H:(bool # 256 word # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem raw_call_calldata_vv_by:
  expr_body_pre cenv cx env
    (Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (a::kws) NONE) es /\
  expr_vv_sim_full_hypotheses (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (a::kws) NONE) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  body_inv tops ctx cenv cx /\
  type_alloc_ok cenv (raw_call_return_type flags) /\
  flags.rcf_max_outsize < dimword (:256) /\
  vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
  go = ext_call_kwarg EKGas flags.rcf_kws xs /\
  (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
  (case go of SOME g => (g,h2) | NONE => emit_op GAS [] h2) = (gas,h3) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,op),s4) /\
  compile_msg_data_to_memory s4 = ((dp,len),s5) /\
  compile_raw_call_finish addr dp len gas
    (case vo of SOME v => v | NONE => Lit 0w)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s5 = (result,sb) /\
  vv = (if flags.rcf_max_outsize = 0 then StackValue (raw_call_return_type flags) result
        else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
  gas_shadow_state s2 h2 /\ fn_has_code h2 h3 shadow_func /\
  EVERY (safe_operand s2) (addr::xs) /\
  ci_mono sa s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s4 s5 /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\ fn_has_code s4 s5 func /\
  (((!marksK vs esK GK tnK tk.
      (!tail. eval_exprs cx (a::kws)
        (es with gas_obs := gas_explicit marksK s0.vs_gas_readings ++ tail) =
        (INL vs, esK with gas_obs := tail)) /\
      storage_trace_domain cx st0 esK.storage_trace /\
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        (^calldata_list_post) H (INL vs) esK GK tnK tk) /\
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) marksK (OK tk,GK,tnK)) ==>
      A s2 ((^calldata_next) vs) (esK,tk,GK,tnK) ^calldata_qvv ^calldata_rvv) ==>
    A sa (bind (eval_exprs cx (a::kws)) ^calldata_next) (es,s0,G0,tn0)
      ^calldata_qvv ^calldata_rvv)) /\
  (!tk. ~tk.vs_halted /\ tk.vs_current_bb = s2.cs_current_bb /\
    tk.vs_inst_idx = LENGTH s2.cs_current_insts ==> Seg s2 s2 tk [] tk) /\
  (!tk tg gw. go = NONE /\ ~tk.vs_halted /\ tk.vs_current_bb = s2.cs_current_bb /\
    tk.vs_inst_idx = LENGTH s2.cs_current_insts /\
    gas_prefix 1 tk.vs_gas_readings = [gw] /\
    tg = update_var (FST (fresh_var s2)) gw
      (tk with <|vs_gas_readings := DROP 1 tk.vs_gas_readings;
                 vs_inst_idx := LENGTH s3.cs_current_insts|>) ==>
    Seg s2 s3 tk [F] tg) /\
  (!tg u. ~tg.vs_halted /\ tg.vs_current_bb = s3.cs_current_bb /\
    tg.vs_inst_idx = LENGTH s3.cs_current_insts /\
    run_inst_seq (emitted_insts s3 s4) tg = OK u ==>
    Seg s3 s4 tg [] (u with vs_inst_idx := LENGTH s4.cs_current_insts)) /\
  (!D0 explicit0 tout Gout tnout marksK n. ^calldata_copy_by) /\
  (!i j u Gu tnu v Gv tnv n esK src.
    ((i = s2 /\ j = s3) \/ (i = s3 /\ j = s4) \/ (i = s4 /\ j = s5)) /\
    storage_trace_frame src /\ storage_trace_domain cx st0 esK.storage_trace /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tnu) (REPLICATE n F) (OK v,Gv,tnv)) /\
    Seg i j u (REPLICATE n F) v /\
    A j src (esK,v,Gv,tnv) ^calldata_qvv ^calldata_rvv ==>
    A i src (esK,u,Gu,tnu) ^calldata_qvv ^calldata_rvv) /\
  (!esK t7 G7 tn7 target amount kvs gw ob tout. ^calldata_request_by) ==>
  A sa (eval_expr cx
    (Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (a::kws) NONE))
    (es,s0,G0,tn0) ^calldata_qvv ^calldata_rvv
Proof
  rewrite_tac[expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[raw_call_calldata_eval] >>
  qpat_x_assum `(_ ==> A sa _ _ _ _)` match_mp_tac >>
  simp_tac std_ss [] >> qx_genl_tac [`marksK`,`vs`,`esK`,`GK`,`tnK`,`tk`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace)
     esK.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> (typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_exprs cx (a::kws)
    (es with gas_obs := gas_explicit marksK s0.vs_gas_readings) = (INL vs,esK)` by
    (`esK with gas_obs := [] = esK` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `esK with gas_obs := [] = esK` (fn obs =>
       qpat_assum `!tail. eval_exprs cx (a::kws) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,obs])))) >>
  drule_all raw_call_calldata_source_ready >>
  disch_then (qx_choose_then `target` (qx_choose_then `av` (qx_choose_then `kvs`
    (qx_choose_then `amount` (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `vs = av::kvs` SUBST_ALL_TAC >>
  `!err. vyperState$assert T err = vyperState$return ()` by
    simp[FUN_EQ_THM,vyperStateTheory.assert_def,vyperStateTheory.return_def] >>
  qpat_assum `!err. vyperState$assert T err = vyperState$return ()` (fn pass =>
    qpat_assum `LENGTH kvs = LENGTH flags.rcf_kws` (fn len =>
      qpat_assum `dest_AddressV av = SOME target` (fn addr =>
        qpat_assum `raw_call_value flags.rcf_kws kvs = SOME amount` (fn val_eq =>
          simp[NoAsms,vyperStateTheory.type_check_def,vyperStateTheory.lift_option_type_def,
               vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_return,
               pass,len,addr,val_eq])))) >>
  suspend "buffers"
QED

Resume raw_call_calldata_vv_by[buffers]:
  qpat_assum `vv = _` SUBST_ALL_TAC >>
  qabbrev_tac `src = eval_raw_call cx flags target cx.txn.calldata amount
     (ext_call_kwarg EKGas flags.rcf_kws kvs)` >>
  `storage_trace_frame src` by simp[Abbr `src`,vyperStorageTraceTheory.storage_trace_frame_raw_call] >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esK tk /\
     storage_well_formed_on cx esK (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk` by
    (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> (typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[NoAsms,typed_args_post_def] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK tk /\
    wb_frame cenv es esK sa s0 tk` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ tk` mp_tac >>
     simp[NoAsms,typed_args_post_def]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >-
       (qpat_assum `eval_exprs cx (a::kws) _ = (INL (av::kvs),esK)`
          (mp_then (Pat `f st = (res, st')`) mp_tac valid_horizon_frame) >>
        simp[cj 6 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
     simp[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >> simp[]) >>
  `allocas_from lo tk /\ lo <= tk.vs_alloca_next` by
    (qpat_assum `ghost_inv_at (DF _) lo dframe cenv cx esK GK tnK tk`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `return_buf_frame dframe cenv sa tk` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`cenv`,`s0`,`sa`] >> simp[] >>
     rpt strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`wb_frame cenv es esK sa s0 tk`, `not_fresh_at sa x`, `lookup_var x s0 = SOME w`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `ci_mono sa s3 /\ ci_mono sa s4 /\ ci_mono sa s5 /\ ci_mono s3 s5` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ci_mono sa s2`, `ci_mono s2 s3`, `ci_mono s3 s4`, `ci_mono s4 s5`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[ci_mono_trans]) >>
  `local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\ local_ptrs_reserved cenv s4 /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s2 x /\ not_fresh_at s3 x /\ not_fresh_at s4 x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s2 x /\ not_fresh_at s3 x /\ not_fresh_at s4 x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`local_ptrs_reserved cenv sa`, `ci_mono sa s2`, `ci_mono sa s3`, `ci_mono sa s4`,
        `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`,
        `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved,
               exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  qabbrev_tac `vop = case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v` >>
  `!p. MEM p (addr::xs) ==> ?w. eval_operand p tk = SOME w /\ op_taint tnK p = {}` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `EVERY (\p. op_taint tnK p = {}) (addr::xs)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[typed_args_post_def, EVERY_MEM] >> rpt strip_tac
     >- simp[] >>
     drule_all LIST_REL_MEM_IMP >> metis_tac[]) >>
  `?tg GG tnG gw n.
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (tk,GK,tnK) (REPLICATE n F) (OK tg,GG,tnG) /\
        stmt_state_rel H ctx func cenv cx esK tg /\
        storage_well_formed_on cx esK (FST H) /\
        ghost_inv_at (DF H) lo dframe cenv cx esK GG tnG tg) /\
      eval_operand gas tg = SOME gw /\ op_taint tnG gas = {} /\
      (!p. safe_operand s2 p ==> eval_operand p tg = eval_operand p tk /\
                               op_taint tnG p = op_taint tnK p) /\
      (case go of NONE => n=1 | SOME g => gas=g /\ n=0) /\
      Seg s2 s3 tk (REPLICATE n F) tg /\
      ~tg.vs_halted /\ tg.vs_current_bb = s3.cs_current_bb /\
      tg.vs_inst_idx = LENGTH s3.cs_current_insts /\ alloca_history func tg /\
      tg.vs_memory = tk.vs_memory /\ tg.vs_allocas = tk.vs_allocas /\
      tg.vs_alloca_next = tk.vs_alloca_next /\
      tnG.t_mem = tnK.t_mem /\ tnG.t_stor = tnK.t_stor /\
      tnG.t_trans = tnK.t_trans /\ tnG.t_imm = tnK.t_imm /\
      (!x. not_fresh_at s2 x ==> lookup_var x tg = lookup_var x tk /\
        FLOOKUP GG x = FLOOKUP GK x /\ op_taint tnG (Var x) = op_taint tnK (Var x))` by
    (Cases_on `go`
     >- (mp_tac (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`,
           `sa` |-> `s2`, `sb` |-> `s3`, `shadow_sa` |-> `h2`, `shadow_sb` |-> `h3`,
           `shadow_gas` |-> `gas`, `s` |-> `tk`, `G` |-> `GK`, `tn` |-> `tnK`,
           `es` |-> `esK`, `d` |-> `dframe`] raw_call_optional_gas_joint) >>
         impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
         strip_tac >> qexistsl [`t`,`G6`,`tn6`,`gw`,`1`] >>
         simp[EVAL ``REPLICATE 1 F``] >> conj_tac
         >- (gen_tac >> disch_tac >>
             qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
               (drule_then (map_every assume_tac o CONJUNCTS o
                 REWRITE_RULE [optionTheory.option_case_def])) >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
         conj_tac
         >- (Cases >> simp[safe_operand_def,eval_operand_def,op_taint_def]) >>
         `Seg s2 s3 tk [F] t` by
           (qpat_assum `!tk tg gw. _ ==> Seg s2 s3 tk [F] tg`
              (qspecl_then [`tk`,`t`,`gw`] mp_tac) >>
            qpat_assum `(case NONE of NONE => gas_prefix 1 tk.vs_gas_readings = [gw] /\ _ | SOME _ => _)`
              (mp_tac o REWRITE_RULE [optionTheory.option_case_def]) >>
            disch_then strip_assume_tac >>
            impl_tac >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
            disch_then ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s3)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     `MEM gas (addr::xs)` by metis_tac[raw_call_kwarg_mem,MEM] >>
     qpat_assum `!p. MEM p (addr::xs) ==> _` drule >> strip_tac >>
     qexistsl [`tk`,`GK`,`tnK`,`w`] >>
     simp[EVAL ``REPLICATE 0 F``,gas_origin_ptr_path_rules] >>
     first_x_assum irule >> simp[]) >>
  qpat_assum `!i j u Gu tnu v Gv tnv n esK src. _ ==> A i _ _ _ _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`GG`,`s3`,`n`,`tnG`,`tg`] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (tk,GK,tnK) _ _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  simp_tac bool_ss [] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "output_buffer"
QED

Resume raw_call_calldata_vv_by[output_buffer]:
  `ci_mono s2 s4 /\ ci_mono s3 s5` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_var <= s3.cs_next_var /\
    sa.cs_next_var <= s4.cs_next_var /\
    s2.cs_next_var <= s3.cs_next_var /\ s2.cs_next_var <= s4.cs_next_var /\
    s3.cs_next_var <= s4.cs_next_var /\ s4.cs_next_var <= s5.cs_next_var` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ci_mono sa s2`,`ci_mono sa s3`,`ci_mono sa s4`,`ci_mono s2 s3`,
        `ci_mono s2 s4`,`ci_mono s3 s4`,`ci_mono s4 s5`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
  `wb_frame cenv es esK sa s0 tg` by
    (irule wb_frame_readonly_tail >> qexistsl [`s2`,`tk`] >>
     simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `return_buf_frame dframe cenv sa tg` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`cenv`,`tk`,`sa`] >> simp[] >>
     rpt strip_tac >> `not_fresh_at s2 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 GG tnG` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl [`GK`,`tnK`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at s2 x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK tg` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp tg /\
    tg.vs_alloca_next + pending_alloca_size func tg <= w2n tg.vs_initial_fmp` by
    (strip_tac >> qpat_assum `stmt_state_rel _ ctx func cenv cx esK tg` (fn rel =>
       conj_tac >- (match_mp_tac (MATCH_MP stmt_state_rel_allocas_below_fmp rel) >> simp[]) >>
       mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room rel)) >>
     qpat_assum `ctx_has_dalloca ctx` (fn has => simp[NoAsms,fmp_room_def,has]) >>
     decide_tac) >>
  `allocas_from lo tg /\ lo <= tg.vs_alloca_next` by
    (qpat_assum `allocas_from lo tk` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[allocas_from_def]) >>
  qabbrev_tac `cap = flags.rcf_max_outsize` >>
  qabbrev_tac `payload = if cap = 0 then 0 else ((cap+31) DIV 32)*32+32` >>
  `payload < dimword (:256)` by
    (Cases_on `flags.rcf_max_outsize = 0` >- simp[Abbr `payload`, Abbr `cap`] >>
     simp[Abbr `payload`, Abbr `cap`] >>
     qpat_assum `type_alloc_ok cenv (raw_call_return_type flags)` mp_tac >>
     qpat_assum `flags.rcf_max_outsize <> 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `flags.rcf_revert_on_failure` >>
     simp[raw_call_return_type_def, allocLimitsTheory.type_alloc_ok_def,
          compileEnvTheory.is_word_type_def, compileEnvTheory.type_memory_bytes_def] >>
     qabbrev_tac `rounded = 32 * ((flags.rcf_max_outsize + 31) DIV 32)` >>
     rpt strip_tac >> irule arithmeticTheory.LESS_TRANS >>
     qexists_tac `2 ** 64` >> conj_tac
     >- (simp[] >> decide_tac) >>
     simp[wordsTheory.dimword_def]) >>
  `?u. run_inst_seq (emitted_insts s3 s4) tg = OK u` by
    (Cases_on `cap = 0`
     >- (qpat_x_assum `cap = 0` SUBST_ALL_TAC >>
         drule_all raw_call_outbuf_zero_run >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     `0 < cap` by decide_tac >>
     `((cap+31) DIV 32)*32 + 32 < dimword (:256)` by
       (qpat_assum `payload < dimword (:256)` mp_tac >> simp[Abbr `payload`]) >>
     drule_all raw_call_outbuf_positive_run >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
       off + sz <= tg.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_tac o MATCH_MP (cj 2 stmt_state_rel_local_ptrs_alloca)) >>
     qpat_assum `s0.vs_alloca_next <= tk.vs_alloca_next` mp_tac >>
     qpat_assum `tg.vs_alloca_next = tk.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name lb sz. local_region cenv es.scopes s0 name lb sz ==>
       lb + sz <= tg.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier,arithmeticTheory.LESS_EQ_TRANS] >>
  qabbrev_tac `tout = u with vs_inst_idx := LENGTH s4.cs_current_insts` >>
  `Seg s3 s4 tg [] tout` by
    (simp[Abbr `tout`] >> first_x_assum irule >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `s3`, `sb` |-> `s4`, `sk` |-> `sa`,
    `es0` |-> `es`, `es` |-> `esK`, `s` |-> `tg`, `d` |-> `dframe`,
    `G` |-> `GG`, `tn` |-> `tnG`, `M` |-> `cap`, `n` |-> `payload`,
    `t7` |-> `tout`] raw_call_outbuf_joint) >>
  impl_tac >-
    (simp[Abbr `payload`, Abbr `tout`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  disch_then (qx_choose_then `Gout` (qx_choose_then `tnout`
    (qx_choose_then `ob` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "input_buffer"
QED

Resume raw_call_calldata_vv_by[input_buffer]:
  `ctx_has_dalloca ctx` by
    (qpat_assum `compile_expr cenv ty (Call _ (RawCallCalldataTarget flags) _ _) sa = _`
       (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac compile_expr_raw_call_calldata_dalloca) >>
     qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  qabbrev_tac `H0 = storage_trace_horizon esK.storage_trace` >>
  `stmt_state_rel H0 ctx func cenv cx esK tout /\
    ghost_inv_at (DF H0) lo dframe cenv cx esK Gout tnout tout` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ tout /\ _`
       (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
  `allocas_below_fmp tout /\
    w2n tout.vs_initial_fmp <= w2n tout.vs_fmp /\ lo <= tout.vs_alloca_next` by
    (`allocas_below_fmp tout` by
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx esK tout`
          (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- qpat_assum `allocas_below_fmp tout`
          (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [allocas_below_fmp_def]) >>
     qpat_assum `ghost_inv_at (DF H0) lo dframe cenv cx esK Gout tnout tout`
       (fn th => FIRST (map ACCEPT_TAC (CONJUNCTS (REWRITE_RULE [ghost_inv_at_def] th))))) >>
  `tout.vs_call_ctx.cc_calldata = cx.txn.calldata /\
    LENGTH tout.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx esK tout`
       (mp_tac o MATCH_MP state_rel_call_ctx_rel o MATCH_MP stmt_state_rel_state_rel) >>
     qpat_assum `expr_sim_inv cenv cx env esK` mp_tac >>
     simp[NoAsms, expr_sim_inv_def, call_ctx_rel_def, vyperTypeInvariantsTheory.context_well_typed_def, dimword_def]) >>
  `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) (marksK ++ REPLICATE n F) (OK tout,Gout,tnout)` by
    (`gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marksK (OK tk,GK,tnK)` by
       (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ (s0,G0,tn0) _ _`
         (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
     `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (tk,GK,tnK) (REPLICATE n F) (OK tg,GG,tnG)` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (tk,GK,tnK) _ _ /\ _`
         (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
     `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) (marksK ++ REPLICATE n F) (OK tg,GG,tnG)` by
        metis_tac[gas_origin_ptr_path_append] >>
     dxrule gas_origin_ptr_path_append >>
     disch_then (qspecl_then [`tg`,`GG`,`tnG`,`[]`,`OK tout`,`Gout`,`tnout`] mp_tac) >> simp[]) >>
  qpat_x_assum `!D0 explicit0 tout Gout tnout marksK n. _ ==> ?t G tn p. _ /\ _`
    (qspecl_then [`DF (H0 : (bool # 256 word # type_value) list # num list)`,
      `gas_explicit_sites ctx shadow_ctx`,`tout`,`Gout`,`tnout`,`marksK`,`n`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t7` (qx_choose_then `G7` (qx_choose_then `tn7`
    (qx_choose_then `p` (map_every assume_tac o CONJUNCTS))))) >>
  `s0.vs_alloca_next <= tout.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esK t7 /\
     storage_well_formed_on cx esK (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
     wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
     return_buf_frame dframe cenv sa t7` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ tout /\ _`
       (qspec_then `H` (fn frame =>
         qpat_assum `valid_horizon cx st0 H esK.storage_trace`
           (map_every assume_tac o CONJUNCTS o MATCH_MP frame))) >>
     let
       val frames = Q.INST [`t` |-> `t7`,`sm` |-> `s4`,
         `G'` |-> `G7`,`tn'` |-> `tn7`] calldata_memory_frames
     in
       qpat_assum `ghost_inv_at (DF H) lo dframe cenv cx esK Gout tnout tout`
         (mp_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
           (qspecl_then [`tn7`,`tn0`,`t7`,`sa`,`s4`,`s0`,`func`,`es`,
             `ctx`,`H0`,`H`,`G7`,`G0`] mp_tac) frames)
     end >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt gen_tac >> disch_tac >> first_x_assum drule >> simp[])) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i j u Gu tnu v Gv tnv n esK src. _ ==> A i _ _ _ _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gout`,`s4`,`0`,`tnout`,`tout`] >>
  simp_tac bool_ss [EVAL ``REPLICATE 0 F``] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!i j u Gu tnu v Gv tnv n esK src. _ ==> A i _ _ _ _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G7`,`s5`,`0`,`tn7`,`t7`] >>
  simp_tac bool_ss [EVAL ``REPLICATE 0 F``] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (tout,Gout,tnout) [] (OK t7,G7,tn7)`
        MATCH_ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!i j u Gu tnu v Gv tnv n esK src. _ ==> A i _ _ _ _` kall_tac >>
  suspend "call"
QED

Resume raw_call_calldata_vv_by[call]:
  `t7.vs_alloca_next = tout.vs_alloca_next /\ t7.vs_allocas = tout.vs_allocas /\
    t7.vs_initial_fmp = tout.vs_initial_fmp` by
    (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = _`
      (fn th => map_every (mp_tac o C AP_TERM th)
        [``venom_state_vs_alloca_next``,``venom_state_vs_allocas``,``venom_state_vs_initial_fmp``]) >>
     simp[]) >>
  `alloca_inv tout` by
    qpat_assum `stmt_state_rel H0 ctx func cenv cx esK tout`
      (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `alloca_history func t7` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (tout,Gout,tnout) [] (OK t7,G7,tn7)`
       (mp_tac o Q.SPECL [`DF H0`,`gas_explicit_sites ctx shadow_ctx`]) >>
     disch_then
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac body_full_path_alloca_history) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t7 /\ _`
    (qspec_then `H0` (fn frame =>
      qpat_assum `valid_horizon cx st0 H0 esK.storage_trace`
        (map_every assume_tac o CONJUNCTS o MATCH_MP frame))) >>
  `allocas_from lo t7 /\ s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next` by
    (rpt conj_tac
     >- (rewrite_tac[allocas_from_def] >>
         qpat_assum `t7.vs_allocas = tout.vs_allocas` (fn th => rewrite_tac[th]) >>
         qpat_assum `allocas_from lo tout` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     qpat_assum `t7.vs_alloca_next = tout.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!p. safe_operand s4 p ==> eval_operand p t7 = eval_operand p tout /\
      op_prov G7 p = op_prov Gout p /\ op_taint tn7 p = op_taint tnout p` by
    (qpat_assum `!x. not_fresh_at s4 x ==> _ /\ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> Cases >>
     simp[safe_operand_def,eval_operand_def,op_prov_def,op_taint_def]) >>
  `!p. safe_operand s3 p ==> eval_operand p tout = eval_operand p tg /\
      op_taint tnout p = op_taint tnG p` by
    (qpat_assum `!x. not_fresh_at s3 x ==> _ /\ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> Cases >>
     simp[safe_operand_def,eval_operand_def,op_taint_def]) >>
  `safe_operand s3 gas` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`(case go of NONE => _ | SOME g => _) = (gas,s3)`,
        `go = ext_call_kwarg EKGas flags.rcf_kws xs`, `EVERY (safe_operand s2) (addr::xs)`] >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >>
     metis_tac[emit_op_safe_operand,raw_call_kwarg_mem,EVERY_MEM]) >>
  `safe_operand s2 vop` by
    (Cases_on `ext_call_kwarg EKValue flags.rcf_kws xs` >> simp[Abbr `vop`] >>
     qpat_assum `ext_call_kwarg EKValue flags.rcf_kws xs = SOME _`
       (mp_tac o MATCH_MP (SPEC_ALL raw_call_kwarg_mem)) >>
     qpat_assum `EVERY (safe_operand s2) (addr::xs)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  `safe_operand s4 ov /\ safe_operand s4 op` by
    (qpat_assum `!x. ov = Var x \/ op = Var x ==> _` mp_tac >>
     qpat_assum `op_prov Gout ov = _` mp_tac >>
     qpat_assum `op_prov Gout op = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `ov` >> Cases_on `op` >>
     simp[safe_operand_def,op_prov_def]) >>
  `safe_operand s5 len /\ safe_operand s5 dp` by
    (qpat_assum `compile_msg_data_to_memory s4 = ((dp,len),s5)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     drule dallocaCalldataTheory.calldata_memory_insts >> strip_tac >>
     drule calldata_memory_placement >> strip_tac >>
     simp[not_fresh_at_def,safe_operand_def,ASCIInumbersTheory.toString_11] >>
     decide_tac) >>
  `safe_operand s2 addr` by
    qpat_assum `EVERY (safe_operand s2) (addr::xs)`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [EVERY_DEF]) >>
  `EVERY (safe_operand s5) [addr;len;dp;gas;vop;ov;op]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`safe_operand s2 addr`,`safe_operand s2 vop`,`safe_operand s3 gas`,
        `safe_operand s4 ov`,`safe_operand s4 op`,`safe_operand s5 dp`,`safe_operand s5 len`,
        `s2.cs_next_var <= s4.cs_next_var`,`s3.cs_next_var <= s4.cs_next_var`,
        `s4.cs_next_var <= s5.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[] >> metis_tac[safe_operand_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  `!p. safe_operand s2 p ==> eval_operand p t7 = eval_operand p tk /\
     op_taint tn7 p = op_taint tnK p` by
    (qx_gen_tac `arg_op` >> disch_tac >>
     `safe_operand s3 arg_op /\ safe_operand s4 arg_op` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`safe_operand s2 arg_op`,`s2.cs_next_var <= s3.cs_next_var`,`s2.cs_next_var <= s4.cs_next_var`] >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[safe_operand_mono]) >>
     map_every (fn (frame, safe) => qpat_assum frame (fn th =>
       qpat_assum safe (mp_tac o MATCH_MP th)))
       [(`!p. safe_operand s4 p ==> _`,`safe_operand s4 arg_op`),
        (`!p. safe_operand s3 p ==> _`,`safe_operand s3 arg_op`),
        (`!p. safe_operand s2 p ==> eval_operand p tg = _ /\ _`,`safe_operand s2 arg_op`)] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `safe_operand s4 gas` by (irule safe_operand_mono >> qexists_tac `s3` >> simp[]) >>
  `eval_operand gas t7 = SOME gw /\ op_taint tn7 gas = {}` by
    (map_every (fn (frame, safe) => qpat_assum frame (fn th =>
       qpat_assum safe (mp_tac o MATCH_MP th)))
       [(`!p. safe_operand s4 p ==> _`,`safe_operand s4 gas`),
        (`!p. safe_operand s3 p ==> _`,`safe_operand s3 gas`)] >>
     simp[]) >>
  `eval_operand addr t7 = SOME (w2w target) /\
    eval_operand vop t7 = SOME (n2w amount)` by
    (qpat_assum `!p. safe_operand s2 p ==> eval_operand p t7 = _ /\ _` (fn frame =>
      map_every (fn pat => qpat_assum pat (mp_tac o MATCH_MP frame))
        [`safe_operand s2 addr`,`safe_operand s2 vop`]) >>
     simp[Abbr `vop`]) >>
  `!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
      g = w2n gw` by
    (gen_tac >> disch_tac >>
     qpat_assum `!g. OPTION_BIND _ _ = _ ==> ?p w. _`
       (drule_then (qx_choose_then `gas_op` (qx_choose_then `gas_word`
         (map_every assume_tac o CONJUNCTS)))) >>
     `go = SOME gas_op` by
       (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     `gas = gas_op` by
       (qpat_assum `go = SOME gas_op` mp_tac >>
        qpat_assum `(case go of NONE => emit_op GAS [] s2 | SOME chosen => (chosen,s2)) = (gas,s3)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >> metis_tac[]) >>
     `safe_operand s2 gas_op` by
       (qpat_assum `ext_call_kwarg EKGas flags.rcf_kws xs = SOME gas_op`
          (mp_tac o MATCH_MP (SPEC_ALL raw_call_kwarg_mem)) >>
        qpat_assum `EVERY (safe_operand s2) (addr::xs)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `!p. safe_operand s2 p ==> eval_operand p t7 = _ /\ _`
       (fn frame => qpat_assum `safe_operand s2 gas_op` (mp_tac o CONJUNCT1 o MATCH_MP frame)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand gas_op tk = SOME gas_word`,`eval_operand gas t7 = SOME gw`,
        `gas = gas_op`,`g = w2n gas_word`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.SOME_11]) >>
  `cap = 0 ==> ov = op` by
    (qpat_assum `compile_raw_call_outbuf cap s3 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cap = 0` >>
     simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> metis_tac[]) >>
  `FLOOKUP t7.vs_allocas s3.cs_next_id = SOME (ob,payload)` by
    (qpat_assum `t7.vs_allocas = tout.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`H` |-> `H0`, `s` |-> `t7`, `es` |-> `esK`,
    `sa` |-> `s3`, `sb` |-> `s4`]
    (INST_TYPE [alpha |-> ``:256``] raw_call_outbuf_separated)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  `w2n tout.vs_fmp + LENGTH cx.txn.calldata <= w2n t7.vs_fmp` by
    (qpat_assum `w2n t7.vs_fmp = _` (fn th => rewrite_tac[th]) >>
     simp[venomLayoutTheory.ceil32_ge]) >>
  `!j. w2n tout.vs_fmp <= j /\ j < w2n tout.vs_fmp + LENGTH cx.txn.calldata ==>
       j NOTIN tn7.t_mem` by simp[] >>
  `op_taint tnK vop = {}` by
    (Cases_on `ext_call_kwarg EKValue flags.rcf_kws xs` >> simp[Abbr `vop`,op_taint_def] >>
     qpat_assum `ext_call_kwarg EKValue flags.rcf_kws xs = SOME _`
       (mp_tac o MATCH_MP (SPEC_ALL raw_call_kwarg_mem)) >>
     qpat_assum `EVERY (\x. op_taint tnK x = {}) (addr::xs)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM,op_taint_def] >> metis_tac[]) >>
  `op_taint tnK addr = {}` by
    (qpat_assum `EVERY (\x. op_taint tnK x = {}) (addr::xs)`
       (ACCEPT_TAC o CONJUNCT1 o SIMP_RULE bool_ss [EVERY_DEF])) >>
  `EVERY (\x. op_taint tn7 x = {}) [addr;len;dp;gas;vop]` by
    (qpat_assum `!p. safe_operand s2 p ==> eval_operand p t7 = _ /\ _` (fn frame =>
      map_every (fn pat => qpat_assum pat (mp_tac o CONJUNCT2 o MATCH_MP frame))
        [`safe_operand s2 addr`,`safe_operand s2 vop`]) >>
     simp[]) >>
  `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` by
    (qpat_assum `expr_body_pre cenv cx env (Call _ (RawCallCalldataTarget flags) _ _) es`
       (mp_tac o MATCH_MP raw_call_calldata_pre) >>
     simp[NoAsms]) >>
  qpat_assum `!p. safe_operand s4 p ==> eval_operand p t7 = _ /\ _` (fn frame =>
    map_every (fn pat => qpat_assum pat (map_every assume_tac o CONJUNCTS o MATCH_MP frame))
      [`safe_operand s4 ov`,`safe_operand s4 op`]) >>
  qunabbrev_tac `src` >>
  qunabbrev_tac `cap` >> qunabbrev_tac `payload` >> qunabbrev_tac `vop` >>
  qpat_x_assum `vo = ext_call_kwarg EKValue flags.rcf_kws xs` SUBST_ALL_TAC >>
  qpat_assum `!esK t7 G7 tn7 target amount kvs gw ob tout. _ ==> A s5 _ _ _ _`
    (qspecl_then [`esK`,`t7`,`G7`,`tn7`,`target`,`amount`,`kvs`,`gw`,`ob`,`tout`] mp_tac) >>
  (impl_tac >- suspend "continuation") >>
  qpat_assum `ctx_has_dalloca ctx` (fn has =>
    simp[NoAsms,has,expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,
         post_value_type_def,AC CONJ_ASSOC CONJ_COMM,AC ADD_ASSOC ADD_COMM])
QED

Resume raw_call_calldata_vv_by[continuation]:
  qpat_assum `flags.rcf_is_delegate \/ flags.rcf_is_static ==> amount = 0`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [DISJ_IMP_THM]) >>
  qpat_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)`
    (assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  qpat_assum `!g. OPTION_BIND (ext_call_kwarg EKGas _ _) _ = SOME g ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `EVERY (\x. op_taint tn7 x = {}) [addr;len;dp;gas;_]`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [EVERY_DEF]) >>
  qpat_assum `EVERY (safe_operand s5) [addr;len;dp;gas;_;ov;op]`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [EVERY_DEF]) >>
  `!x. MEM (Var x) [addr;len;dp;gas;
       (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v);ov;op] ==>
       not_fresh_at s5 x` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `EVERY (safe_operand s5) [addr;len;dp;gas;_;ov;op]` (fn every =>
       qpat_assum `MEM (Var x) _`
         (mp_tac o CONJUNCT1 o REWRITE_RULE [safe_operand_def] o
          MATCH_MP (REWRITE_RULE [EVERY_MEM] every))) >>
     simp[]) >>
  qpat_assum `!x. MEM (Var x) _ ==> not_fresh_at s5 x`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esK t7 /\
    storage_well_formed_on cx esK (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t7 /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n t7.vs_initial_fmp <= w2n tout.vs_fmp` by
    (qpat_assum `t7.vs_initial_fmp = tout.vs_initial_fmp` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `cx.txn.calldata <> [] ==> ?x. dp = Var x /\ ptr_covers G7 tn7 x t7 (LENGTH cx.txn.calldata)` by
    (disch_tac >> qexists_tac `p` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM th])))
    [`eval_operand ov t7 = eval_operand ov tout`,`eval_operand op t7 = eval_operand op tout`,
     `op_prov G7 ov = op_prov Gout ov`,`op_prov G7 op = op_prov Gout op`,
     `op_taint tn7 ov = op_taint tnout ov`,`op_taint tn7 op = op_taint tnout op`] >>
  simp[NoAsms,expr_has_effect_thm,lowered_value_type_def,vyperASTTheory.expr_type_def,w2n_lt] >>
  PURE_ONCE_REWRITE_TAC
    [Q.SPECL [`32`,`(flags.rcf_max_outsize + 31) DIV 32`] MULT_COMM,
     Q.SPECL [`LENGTH cx.txn.calldata`,`w2n tout.vs_fmp`] ADD_COMM] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_call_calldata_vv_by

Theorem raw_call_calldata_vv_full[local]:
  body_exprs_full_ok cx args /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es ==>
  expr_vv_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (RawCallCalldataTarget flags) args dflt) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_via_bundle] >> rpt gen_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE
    [expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def]) >>
  drule_all raw_call_calldata_word_schedule >>
  disch_then (qx_choosel_then [`a`,`kws`,`addr`,`xs`,`vo`,`go`,`gas`,`ov`,`op`,
    `dp`,`len`,`result`,`s2`,`s3`,`s4`,`s5`,`h2`,`h3`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `args = a::kws` SUBST_ALL_TAC >>
  qpat_x_assum `ann = raw_call_return_type flags` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = NONE` SUBST_ALL_TAC >>
  let
    val sim = Q.SPECL [`a::kws`,`DF`,`lo`,`dframe`,`ctx`,`shadow_ctx`,`PG`,`tops`,
      `func`,`shadow_func`,`cenv`,`env`,`cx`,`expr_type`,`es`,`st0`,
      `sa`,`s2`,`sha`,`h2`,`addr::xs`,`s0`,`G0`,`tn0`]
        lower_word_args_by_type_sim_full
  in
    SUBGOAL_THEN (fst (dest_imp (concl sim))) (assume_tac o MATCH_MP sim)
  end
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       gen_tac >> MATCH_ACCEPT_TAC gas_shadow_expr_type]) >>
  irule (BETA_RULE (Q.INST [`A` |-> `\i. gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0`,
    `Seg` |-> `\i j t m u. T`] raw_call_calldata_vv_by)) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`addr`,`dp`,`env`,`gas`,`go`,`h2`,`h3`,`len`,`op`,`ov`,
    `result`,`s2`,`s3`,`s4`,`s5`,`shadow_func`,`sha`,`shb`,`tops`,`ty`,`vo`,`xs`] >>
  simp_tac bool_ss [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt gen_tac >> MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [] calldata_copy_run)) >>
  TRY (rpt gen_tac >> MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [] calldata_request_full))
  >- (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> strip_tac >>
      metis_tac[raw_call_generated_prefix_full])
  >~ [`expr_vv_sim_full_hypotheses _ _ _ _ _ _ _`]
  >- (rewrite_tac[expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >> irule gas_outcome_full_bind_all_path >> BETA_TAC >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[cj 6 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (rpt gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
      simp[vyperStorageTraceTheory.storage_trace_frame_checks] >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts] >> gen_tac >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts,vyperStorageTraceTheory.storage_trace_frame_raw_call]) >>
  qexists_tac `^calldata_list_post` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx (a::kws)) _ _ _` (irule_at Any) >>
      simp[NoAsms] >> rpt strip_tac >> Cases_on `res` >>
      gvs[wb_args_exit_def,stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?vs. res = INL vs` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> (\H rr mid G tn t. _) _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >>
     BETA_TAC >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `value_list` strip_assume_tac) (K all_tac)) >>
     qexists_tac `value_list` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp_tac bool_ss [] >>
  first_x_assum irule >> conj_tac
  >- (first_assum (ACCEPT_TAC o BETA_RULE)) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `marks` >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_call_calldata_expr_full_ok:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`flags`,`args`,`dflt`] >>
  disch_tac >> simp[Once body_expr_full_ok_def] >>
  map_every qx_gen_tac
    [`DF`,`lo`,`dframe`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
     `cenv`,`env`,`ty`,`es`] >> strip_tac >>
  reverse conj_asm2_tac
  >- (qpat_assum `body_exprs_full_ok cx args` (fn args_ok =>
      qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
      qpat_assum `shadow_body_inv tops ctx shadow_ctx` (fn shadow =>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (fn cells =>
      qpat_assum `expr_body_pre cenv cx env _ es` (fn pre =>
        MATCH_ACCEPT_TAC (MATCH_MP raw_call_calldata_vv_full
          (LIST_CONJ [args_ok,inv,shadow,cells,pre])))))))) >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
