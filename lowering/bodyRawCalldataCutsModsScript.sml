(* Source and compiler cuts for a linked raw call using transaction calldata. *)
Theory bodyRawCalldataCutsMods
Ancestors
  bodyRawRequestInputsMods bodyFullWordArgs exprSimFullBundleProps
  exprSimRawCall exprSimSend exprSimWordArgs exprLoweringProps
  gasShadowCompileBuiltinSystem gasShadowCompileStmtHelpers gasShadowState
  gasShadow exprLowering compileEnv emitHelper builtinSystem fragExec
  vyperAST vyperInterpreter list option pair
Libs monadsyntax

Theorem raw_calldata_source_bind:
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

Theorem raw_calldata_compile_parts[local]:
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

Theorem raw_calldata_keyword_types[local]:
  !kws sa. EVERY (\e. expr_type e = BaseT (UintT 256)) kws ==>
    lower_word_args cenv expr_type kws sa =
      lower_word_args cenv (K (BaseT (UintT 256))) kws sa
Proof
  Induct >> simp[lower_word_args_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Use the checked keyword lowering rule to name the actual word operands. *)
Theorem raw_calldata_word_compile[local]:
  expr_type a = BaseT AddressT /\ LENGTH kws = LENGTH flags.rcf_kws /\
  EVERY (\k. k = EKValue \/ k = EKGas) flags.rcf_kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  compile_expr cenv ty (Call ann (RawCallCalldataTarget flags) (a::kws) dflt) sa =
    (vv,sb) ==>
  ?addr xs gas ov op dp len result s2 s3 s4 s5.
    lower_word_args cenv expr_type (a::kws) sa = (addr::xs,s2) /\
    (case ext_call_kwarg EKGas flags.rcf_kws xs of
     SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,op),s4) /\
    compile_msg_data_to_memory s4 = ((dp,len),s5) /\
    compile_raw_call_finish addr dp len gas
      (case ext_call_kwarg EKValue flags.rcf_kws xs of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s5 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  strip_tac >> drule_then strip_assume_tac raw_calldata_compile_parts >>
  drule_all_then strip_assume_tac raw_call_kwargs_word_args >>
  `lower_word_args cenv expr_type (a::kws) sa = (addr::xs,s2)` by
    simp[lower_word_args_cons, raw_calldata_keyword_types] >>
  gvs[] >> rpt (goal_assum (drule_at Any) >> simp[])
QED

Theorem raw_calldata_shadow_pair[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a h /\
  f a = (v,b) /\ g h = (w,j) ==>
  v = w /\ gas_shadow_state b j
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem raw_calldata_gas_pair[local]:
  gas_shadow_state s h /\
  (case go of SOME g => (g,s) | NONE => emit_op GAS [] s) = (gas,t) /\
  (case go of SOME g => (g,h) | NONE => emit_op GAS [] h) = (hgas,j) ==>
  gas = hgas /\ gas_shadow_state t j
Proof
  Cases_on `go` >> simp[]
  >- (strip_tac >> irule raw_calldata_shadow_pair >>
      qexistsl_tac [`s`,`emit_op GAS []`,`emit_op GAS []`,`h`] >>
      simp[gas_shadow_compiles_emit_op]) >>
  strip_tac >> gvs[]
QED

Theorem raw_calldata_gas_mono[local]:
  (case go of SOME g => (g,s) | NONE => emit_op GAS [] s) = (gas,t) ==>
  ci_mono s t
Proof
  Cases_on `go` >> simp[ci_mono_refl] >> strip_tac >>
  qspecl_then [`GAS`,`[]`,`s`] mp_tac ci_mono_emit_op >> simp[]
QED

val calldata_mono = ``\sa s2 s3 s4 s5 sb.
  ci_mono sa s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 s5 /\ ci_mono s5 sb``;

val calldata_placed = ``\sa s2 s3 s4 s5 sb f.
  fn_has_code sa s2 f /\ fn_has_code s2 s3 f /\
  fn_has_code s3 s4 f /\ fn_has_code s4 s5 f /\ fn_has_code s5 sb f``;

Theorem raw_calldata_mono_chain[local]:
  lower_word_args ce expr_type ws sa = (ops,s2) /\
  (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
  compile_raw_call_outbuf m s3 = ((ov,op),s4) /\
  compile_msg_data_to_memory s4 = ((dp,len),s5) /\
  compile_raw_call_finish addr dp len gas valop ct m rof ov op s5 = (result,sb) ==>
  (^calldata_mono) sa s2 s3 s4 s5 sb
Proof
  BETA_TAC >> strip_tac >> rpt conj_tac
  >- (drule ci_mono_lower_word_args >> simp[])
  >- (drule raw_calldata_gas_mono >> simp[])
  >- (qspecl_then [`m`,`s3`] mp_tac ci_mono_compile_raw_call_outbuf >> simp[])
  >- (qspec_then `s4` mp_tac ci_mono_compile_msg_data_to_memory >> simp[]) >>
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  metis_tac[ci_mono_compile_raw_call_finish,SND]
QED

Theorem raw_calldata_place_chain[local]:
  (^calldata_mono) sa s2 s3 s4 s5 sb /\ fn_has_code sa sb f ==>
  (^calldata_placed) sa s2 s3 s4 s5 sb f
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends s4 sb` by (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  qspecl_then [`sa`,`s2`,`sb`,`f`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`s2`,`s3`,`sb`,`f`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`s3`,`s4`,`sb`,`f`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
  qspecl_then [`s4`,`s5`,`sb`,`f`] mp_tac fn_has_code_split >> simp[]
QED

Theorem raw_calldata_request_cuts_mods:
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es /\
  compile_expr cenv ty (Call ann (RawCallCalldataTarget flags) args dflt) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (RawCallCalldataTarget flags) args dflt)) hsa = (vv,hsb) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sb,hsa,hsb) ==>
  ?a kws addr xs vo go gas ov op dp len result s2 s3 s4 s5 h2 h3 h4 h5.
    args = a::kws /\ dflt = NONE /\ ann = raw_call_return_type flags /\
    expr_type a = BaseT AddressT /\ LENGTH kws = LENGTH flags.rcf_kws /\
    raw_call_kws_ok flags kws /\ EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
    ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\ flags.rcf_max_outsize < dimword (:256) /\
    lower_word_args cenv expr_type (a::kws) sa = (addr::xs,s2) /\
    lower_word_args (gas_shadow_env T cenv) expr_type
      (MAP gas_shadow_expr (a::kws)) hsa = (addr::xs,h2) /\
    vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
    go = ext_call_kwarg EKGas flags.rcf_kws xs /\
    (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
    (case go of SOME g => (g,h2) | NONE => emit_op GAS [] h2) = (gas,h3) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,op),s4) /\
    compile_raw_call_outbuf flags.rcf_max_outsize h3 = ((ov,op),h4) /\
    compile_msg_data_to_memory s4 = ((dp,len),s5) /\
    compile_msg_data_to_memory h4 = ((dp,len),h5) /\
    compile_raw_call_finish addr dp len gas (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s5 = (result,sb) /\
    compile_raw_call_finish addr dp len gas (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op h5 = (result,hsb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory)) /\
    gas_shadow_state s3 h3 /\ gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (sa,s2,hsa,h2) /\
    (^calldata_mono) sa s2 s3 s4 s5 sb /\ (^calldata_mono) hsa h2 h3 h4 h5 hsb /\
    (^calldata_placed) sa s2 s3 s4 s5 sb func /\ (^calldata_placed) hsa h2 h3 h4 h5 hsb hfunc
Proof
  BETA_TAC >> strip_tac >> drule raw_calldata_pre_operands_flags_mods >>
  disch_then (qx_choose_then `a` (qx_choose_then `kws`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` kall_tac >>
  gvs[] >> drule_then strip_assume_tac raw_call_kwargs_types >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  drule_all_then strip_assume_tac raw_calldata_word_compile >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  pure_rewrite_tac[gas_shadow_expr_def, MAP, OPTION_MAP_DEF] >> strip_tac >>
  `expr_type (gas_shadow_expr a) = BaseT AddressT /\
   LENGTH (MAP gas_shadow_expr kws) = LENGTH flags.rcf_kws /\
   EVERY (\e. expr_type e = BaseT (UintT 256)) (MAP gas_shadow_expr kws)` by
    simp[EVERY_MAP,combinTheory.o_DEF,gas_shadow_expr_type] >>
  qpat_assum `compile_expr _ _ (Call _ _ (gas_shadow_expr _::_) _) hsa = _`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac raw_calldata_word_compile) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `ha` (qx_choose_then `ys` (qx_choose_then `hg`
    (qx_choose_then `hov` (qx_choose_then `hop` (qx_choose_then `hdp`
      (qx_choose_then `hlen` (qx_choose_then `hres` (qx_choose_then `h2`
        (qx_choose_then `h3` (qx_choose_then `h4` (qx_choose_then `h5` strip_assume_tac)))))))))))) >>
  `(addr::xs = ha::ys) /\ gas_shadow_state s2 h2` by
    (irule raw_calldata_shadow_pair >>
     qpat_assum `lower_word_args _ _ (a::kws) sa = _` (irule_at Any) >>
     qpat_assum `lower_word_args _ _ (gas_shadow_expr _::_) hsa = _` (irule_at Any) >>
     pure_rewrite_tac[GSYM MAP] >> simp[gas_shadow_compiles_lower_word_args,gas_shadow_expr_type]) >>
  fs[] >>
  `gas = hg /\ gas_shadow_state s3 h3` by
    (irule raw_calldata_gas_pair >>
     qpat_assum `(case _ of NONE => _ | SOME _ => _) = (gas,s3)` (irule_at Any) >>
     qpat_assum `(case _ of NONE => _ | SOME _ => _) = (hg,h3)` (irule_at Any) >> simp[]) >>
  `((ov,op) = (hov,hop)) /\ gas_shadow_state s4 h4` by
    (irule raw_calldata_shadow_pair >>
     qpat_assum `compile_raw_call_outbuf _ s3 = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_outbuf _ h3 = _` (irule_at Any) >>
     simp[gas_shadow_compiles_raw_call_outbuf]) >>
  `((dp,len) = (hdp,hlen)) /\ gas_shadow_state s5 h5` by
    (irule raw_calldata_shadow_pair >>
     qpat_assum `compile_msg_data_to_memory s4 = _` (irule_at Any) >>
     qpat_assum `compile_msg_data_to_memory h4 = _` (irule_at Any) >>
     simp[gas_shadow_compiles_msg_data_to_memory]) >>
  gvs[] >> conj_tac
  >- (drule raw_calldata_pre_operands_flags_mods >> simp[]) >>
  `result = hres /\ gas_shadow_state sb hsb` by
    (irule raw_calldata_shadow_pair >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ h5 = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s5 = _` (irule_at Any) >>
     simp[gas_shadow_compiles_raw_call_finish]) >>
  `(^calldata_mono) sa s2 s3 s4 s5 sb` by
    (BETA_TAC >> irule (BETA_RULE raw_calldata_mono_chain) >>
     qpat_assum `lower_word_args _ _ _ sa = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s5 = _` (irule_at Any) >>
     qexists_tac `ext_call_kwarg EKGas flags.rcf_kws xs` >> simp[]) >>
  `(^calldata_mono) hsa h2 h3 h4 h5 hsb` by
    (BETA_TAC >> irule (BETA_RULE raw_calldata_mono_chain) >>
     qpat_assum `lower_word_args _ _ _ hsa = _` (irule_at Any) >>
     qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ h5 = _` (irule_at Any) >>
     qexists_tac `ext_call_kwarg EKGas flags.rcf_kws xs` >> simp[]) >>
  `(^calldata_placed) sa s2 s3 s4 s5 sb func` by
    (irule raw_calldata_place_chain >> simp[]) >>
  `(^calldata_placed) hsa h2 h3 h4 h5 hsb hfunc` by
    (irule raw_calldata_place_chain >> simp[]) >>
  fs[expr_sim_full_code_def]
QED
