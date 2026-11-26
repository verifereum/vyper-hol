(* Matching frontiers for the byte-expression raw call. *)
Theory bodyRawBytesRequestCutsMods
Ancestors
  bodyRawRequestInputsMods exprSimRawCall exprSimFullBundleProps
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompileBuiltinSystem
  gasShadowCompileContext gasShadowCompile gasShadowState gasShadow bodyFullWordArgs
  exprLoweringProps exprLowering compileEnv fragExec vyperInterpreter vyperState vyperAST pair
Libs monadsyntax

Triviality cut_transport:
  gas_shadow_compiles f g /\ f s = (v,t) /\ gas_shadow_state s h ==>
  ?j. g h = (v,j) /\ gas_shadow_state t j
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `g h` >> simp[]
QED

Triviality cut_shadow_keywords:
  gas_shadow_compiles (compile_ext_call_kwargs compile_expr cenv NoneT ks es)
    (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT ks
      (MAP gas_shadow_expr es))
Proof
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwargs_env)) >>
  simp[gas_shadow_compile_expr_env]
QED

Triviality cut_shadow_optional_gas:
  (case go of SOME g => (g,s) | NONE => emit_op GAS [] s) = (gas,t) /\
  gas_shadow_state s h ==>
  ?j. (case go of SOME g => (g,h) | NONE => emit_op GAS [] h) = (gas,j) /\
      gas_shadow_state t j
Proof
  Cases_on `go` >> simp[]
  >- (strip_tac >> irule cut_transport >> qexistsl_tac [`emit_op GAS []`,`s`] >> simp[]) >>
  strip_tac >> gvs[]
QED

val cut_mono = ``\sa s1 s2 s3 s4 s5 s6 s7 sb.
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\ ci_mono s7 sb``;

val cut_placed = ``\sa s1 s2 s3 s4 s5 s6 s7 sb f.
  fn_has_code sa s1 f /\ fn_has_code s1 s2 f /\
  fn_has_code s2 s3 f /\ fn_has_code s3 s4 f /\ fn_has_code s2 s4 f /\
  fn_has_code s4 s5 f /\ fn_has_code s5 s6 f /\ fn_has_code s6 s7 f /\
  fn_has_code s7 sb f``;

Triviality cut_optional_gas_mono:
  (case go of SOME g => (g,s) | NONE => emit_op GAS [] s) = (gas,t) ==>
  ci_mono s t
Proof
  Cases_on `go` >> simp[ci_mono_refl] >> strip_tac >>
  mp_tac (Q.SPECL [`GAS`, `[]`, `s`] ci_mono_emit_op) >> simp[]
QED

Triviality cut_mono_chain:
  lower_value compile_expr ce (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr ce (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\ emit_op ADD [data;Lit 32w] s3 = (dp,s4) /\
  lower_word_args ce (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  compile_raw_call_outbuf m s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas valop ct m revert_fail ov op s7 = (result,sb) ==>
  (^cut_mono) sa s1 s2 s3 s4 s5 s6 s7 sb
Proof
  BETA_TAC >> strip_tac >> rpt conj_tac
  >- (mp_tac (Q.SPECL [`ce`, `BaseT AddressT`, `a`, `sa`]
                 ci_mono_lower_value_compile_expr) >> simp[])
  >- (mp_tac (Q.SPECL [`ce`, `expr_type d`, `d`, `s1`]
                 ci_mono_lower_value_compile_expr) >> simp[])
  >- (mp_tac (Q.SPECL [`MLOAD`, `[data]`, `s2`] ci_mono_emit_op) >> simp[])
  >- (mp_tac (Q.SPECL [`ADD`, `[data;Lit 32w]`, `s3`] ci_mono_emit_op) >> simp[])
  >- (drule ci_mono_lower_word_args >> simp[])
  >- (drule cut_optional_gas_mono >> simp[])
  >- (mp_tac (Q.SPECL [`m`, `s6`] ci_mono_compile_raw_call_outbuf) >> simp[]) >>
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  metis_tac[ci_mono_compile_raw_call_finish,SND]
QED

Triviality cut_place_chain:
  (^cut_mono) sa s1 s2 s3 s4 s5 s6 s7 sb /\ fn_has_code sa sb f ==>
  (^cut_placed) sa s1 s2 s3 s4 s5 s6 s7 sb f
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends s6 sb` by (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  `cs_extends s5 sb` by (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `cs_extends s4 sb` by (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends s2 s4` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  mp_tac (Q.SPECL [`sa`,`s1`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s1`,`s2`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s2`,`s3`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s2`,`s4`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s3`,`s4`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s4`,`s5`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s5`,`s6`,`sb`,`f`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`s6`,`s7`,`sb`,`f`] fn_has_code_split) >> simp[]
QED

Theorem raw_bytes_request_cuts_mods:
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  compile_expr cenv ty (Call ann (RawCallTarget flags) args dflt) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (RawCallTarget flags) args dflt)) hsa = (vv,hsb) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sb,hsa,hsb) ==>
  ?a d kws cap addr data len dp vo go xs gas ov op result
      s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7.
    args = a::d::kws /\ dflt = NONE /\ ann = raw_call_return_type flags /\
    expr_type a = BaseT AddressT /\ expr_type d = BaseT (BytesT (Dynamic cap)) /\
    LENGTH kws = LENGTH flags.rcf_kws /\ raw_call_kws_ok flags kws /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr a) hsa = (addr,h1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
      (gas_shadow_expr d) h1 = (data,h2) /\
    emit_op MLOAD [data] s2 = (len,s3) /\ emit_op MLOAD [data] h2 = (len,h3) /\
    emit_op ADD [data;Lit 32w] s3 = (dp,s4) /\ emit_op ADD [data;Lit 32w] h3 = (dp,h4) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 = ((vo,go,NONE),s5) /\
    compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
      (MAP gas_shadow_expr kws) h4 = ((vo,go,NONE),h5) /\
    lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
    lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
      (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
    vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
    go = ext_call_kwarg EKGas flags.rcf_kws xs /\
    (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
    (case go of SOME g => (g,h5) | NONE => emit_op GAS [] h5) = (gas,h6) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
    compile_raw_call_outbuf flags.rcf_max_outsize h6 = ((ov,op),h7) /\
    compile_raw_call_finish addr dp len gas (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    compile_raw_call_finish addr dp len gas (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op h7 = (result,hsb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (sa,s1,hsa,h1) /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (s1,s2,h1,h2) /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (s4,s5,h4,h5) /\
    gas_shadow_state s3 h3 /\ gas_shadow_state s6 h6 /\ gas_shadow_state s7 h7 /\
    (^cut_mono) sa s1 s2 s3 s4 s5 s6 s7 sb /\
    (^cut_mono) hsa h1 h2 h3 h4 h5 h6 h7 hsb /\
    (^cut_placed) sa s1 s2 s3 s4 s5 s6 s7 sb func /\
    (^cut_placed) hsa h1 h2 h3 h4 h5 h6 h7 hsb hfunc /\
    eval_expr cx (Call ann (RawCallTarget flags) args dflt) =
      bind (bind (eval_expr cx a) (read_result cx)) (\av.
        bind (bind (eval_expr cx d) (read_result cx)) (\dv.
          bind (eval_exprs cx kws) (\kvs. do
            type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
            target <- lift_option_type (dest_AddressV av) "raw_call target";
            data <- lift_option_type (dest_BytesV dv) "raw_call data";
            amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
            eval_raw_call cx flags target data amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
          od)))
Proof
  strip_tac >> drule_then (map_every assume_tac o CONJUNCTS)
    raw_call_pre_operands_flags_mods >>
  qpat_x_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` kall_tac >>
  qpat_x_assum `?a d kws n. _` strip_assume_tac >> gvs[] >>
  qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_raw_call) >>
  drule_then strip_assume_tac raw_call_kwargs_types >>
  drule_all_then strip_assume_tac raw_call_kwargs_word_args >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  `?h1. lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
          (gas_shadow_expr a) hsa = (addr,h1) /\ gas_shadow_state s1 h1` by
    (irule cut_transport >> qexistsl_tac [`lower_value compile_expr cenv (BaseT AddressT) a`,`sa`] >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `?h2. lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
          (gas_shadow_expr d) h1 = (data,h2) /\ gas_shadow_state s2 h2` by
    (irule cut_transport >> qexistsl_tac [`lower_value compile_expr cenv (expr_type d) d`,`s1`] >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `?h3. emit_op MLOAD [data] h2 = (len,h3) /\ gas_shadow_state s3 h3` by
    (irule cut_transport >> qexistsl_tac [`emit_op MLOAD [data]`,`s2`] >> simp[]) >>
  `?h4. emit_op ADD [data;Lit 32w] h3 = (dp,h4) /\ gas_shadow_state s4 h4` by
    (irule cut_transport >> qexistsl_tac [`emit_op ADD [data;Lit 32w]`,`s3`] >> simp[]) >>
  `?h5. compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
          (MAP gas_shadow_expr kws) h4 = ((vo,go,NONE),h5) /\ gas_shadow_state s5 h5` by
    (irule cut_transport >>
     qexistsl_tac [`compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws`,`s4`] >>
     simp[cut_shadow_keywords]) >>
  `lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
      (MAP gas_shadow_expr kws) h4 = (xs,h5)` by
    (qpat_x_assum `compile_ext_call_kwargs _ cenv _ _ _ _ = _` kall_tac >>
     `LENGTH (MAP gas_shadow_expr kws) = LENGTH flags.rcf_kws` by simp[] >>
     drule_all_then strip_assume_tac raw_call_kwargs_word_args >>
     `?j. lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
            (MAP gas_shadow_expr kws) h4 = (xs,j) /\ gas_shadow_state s5 j` by
       (irule cut_transport >>
        qexistsl_tac [`lower_word_args cenv (K (BaseT (UintT 256))) kws`,`s4`] >>
        simp[gas_shadow_compiles_lower_word_args]) >>
     qpat_x_assum `lower_word_args _ _ _ h4 = (xs,j)` mp_tac >> simp[]) >>
  `?h6. (case go of SOME g => (g,h5) | NONE => emit_op GAS [] h5) = (gas,h6) /\
        gas_shadow_state s6 h6` by (irule cut_shadow_optional_gas >> qexists_tac `s5` >> simp[]) >>
  `?h7. compile_raw_call_outbuf flags.rcf_max_outsize h6 = ((ov,op),h7) /\
        gas_shadow_state s7 h7` by
    (irule cut_transport >> qexistsl_tac [`compile_raw_call_outbuf flags.rcf_max_outsize`,`s6`] >>
     simp[gas_shadow_compiles_raw_call_outbuf]) >>
  qabbrev_tac `raw_finish_f = compile_raw_call_finish addr dp len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op` >>
  `?h8. raw_finish_f h7 = (result,h8) /\ gas_shadow_state sb h8` by
    (irule cut_transport >> qexistsl_tac [`raw_finish_f`,`s7`] >>
     asm_rewrite_tac[] >> simp[Abbr `raw_finish_f`,gas_shadow_compiles_raw_call_finish]) >>
  qunabbrev_tac `raw_finish_f` >>
  `h8 = hsb` by
    (qpat_x_assum `expr_type d = _` kall_tac >>
     qpat_x_assum `vo = ext_call_kwarg _ _ _` kall_tac >>
     qpat_x_assum `go = ext_call_kwarg _ _ _` kall_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[Once gas_shadow_expr_def, exprSimSendTheory.compile_expr_call,
          Once compile_call_def, gas_shadow_expr_type] >>
     Cases_on `flags.rcf_max_outsize = 0` >> simp[]) >>
  qpat_x_assum `h8 = hsb` SUBST_ALL_TAC >>
  `lower_value compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr d))
     (gas_shadow_expr d) h1 = (data,h2)` by
    (pure_rewrite_tac[gas_shadow_expr_type] >> first_assum ACCEPT_TAC) >>
  `(^cut_mono) sa s1 s2 s3 s4 s5 s6 s7 sb` by
    (BETA_TAC >> irule (BETA_RULE cut_mono_chain) >>
     qpat_assum `lower_value _ cenv _ a sa = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s7 = _` (irule_at Any) >>
     qexistsl_tac [`xs`,`kws`,`go`,`data`,`d`] >> asm_rewrite_tac[]) >>
  `(^cut_mono) hsa h1 h2 h3 h4 h5 h6 h7 hsb` by
    (BETA_TAC >> irule (BETA_RULE cut_mono_chain) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr a) hsa = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ h7 = _` (irule_at Any) >>
     qexistsl_tac [`xs`,`MAP gas_shadow_expr kws`,`go`,`data`,`gas_shadow_expr d`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `(^cut_mono) sa s1 s2 s3 s4 s5 s6 s7 sb`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `(^cut_mono) hsa h1 h2 h3 h4 h5 h6 h7 hsb`
    (strip_assume_tac o BETA_RULE) >>
  `(^cut_placed) sa s1 s2 s3 s4 s5 s6 s7 sb func` by
    (BETA_TAC >> irule (BETA_RULE cut_place_chain) >> asm_rewrite_tac[]) >>
  `(^cut_placed) hsa h1 h2 h3 h4 h5 h6 h7 hsb hfunc` by
    (BETA_TAC >> irule (BETA_RULE cut_place_chain) >> asm_rewrite_tac[]) >>
  qpat_x_assum `(^cut_placed) sa s1 s2 s3 s4 s5 s6 s7 sb func`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `(^cut_placed) hsa h1 h2 h3 h4 h5 h6 h7 hsb hfunc`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `go = ext_call_kwarg _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `vo = ext_call_kwarg _ _ _` SUBST_ALL_TAC >>
  qpat_assum `expr_type d = _` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  qexistsl_tac [`addr`,`data`,`len`,`dp`,`xs`,`gas`,`ov`,`op`,`result`,
    `s1`,`s2`,`s3`,`s4`,`s5`,`s6`,`s7`,`h1`,`h2`,`h3`,`h4`,`h5`,`h6`,`h7`] >>
  simp[expr_sim_full_code_def, raw_call_eval_action]
QED
