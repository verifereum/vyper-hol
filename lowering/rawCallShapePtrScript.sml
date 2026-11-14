(* Current-source raw_call shape interfaces shared by pointer simulations. *)
Theory rawCallShapePtr
Ancestors
  exprSimHypsDefs exprLowering exprLoweringProps builtinSystem
  vyperTyping vyperTypeSystem vyperInterpreter vyperState vyperValue
  supportedExprTraverse allocLimits list pair exprSimSend context emitHelper
  exprSimSource vyperTypeCallGraph exprSimWordArgs compileEnv
  exprSimPrecompiles exprSimHash vyperTypeExtCallSoundness
Libs
  pairLib monadsyntax

Theorem raw_call_nonrevert_finish_code:
  compile_raw_call_finish addr dp dl gas value ct n F ov op sa = (result,sb) ==>
  ?ok sc. (case ct of
      DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
    | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sc = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`success`, `s'`] >>
  gvs[comp_ignore_bind_def, comp_bind_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem raw_call_reverting_finish_steps:
  compile_raw_call_finish addr dp dl gas value ct n T ov op sa = (result,sb) ==>
  ?ok sc fail s1 pass s2 s3 fblock s4 rds s5 buf s6 s7 s8 pblock s9.
    (case ct of
       DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w n)]
     | RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    fresh_label "call_failed" sc = (fail,s1) /\
    fresh_label "call_ok" s1 = (pass,s2) /\
    emit_inst JNZ [ok;Label pass;Label fail] [] s2 = ((),s3) /\
    new_block fail s3 = (fblock,s4) /\
    emit_op RETURNDATASIZE [] s4 = (rds,s5) /\
    compile_alloc_buffer 0 s5 = (buf,s6) /\
    emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] s6 = ((),s7) /\
    emit_inst REVERT [buf.buf_operand;rds] [] s7 = ((),s8) /\
    new_block pass s8 = (pblock,s9) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap]; return ov od
     else return (Lit 0w)) s9 = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_call_typed_data_dynamic:
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) ==>
  ?n. expr_type (EL 1 args) = BaseT (BytesT (Dynamic n))
Proof
  pure_rewrite_tac [well_typed_expr_def] >> strip_tac >>
  `1 < LENGTH args` by decide_tac >>
  fs[listTheory.EL_MAP]
QED

Theorem raw_call_pre_flags:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  ~flags.rcf_is_delegate /\
  flags.rcf_max_outsize < dimword (:256) /\
  LENGTH args = 2 + LENGTH flags.rcf_kws /\
  raw_call_kws_ok flags (DROP 2 args) /\
  ann = raw_call_return_type flags /\ dflt = NONE
Proof
  simp[expr_body_pre_def, well_typed_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  strip_tac >> gvs[supportedExprTraverseTheory.expr_evm_run_root_def]
QED

Theorem raw_call_pre_operands:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  ?a d kws n. args = a::d::kws /\
    expr_type a = BaseT AddressT /\
    expr_type d = BaseT (BytesT (Dynamic n)) /\
    LENGTH kws = LENGTH flags.rcf_kws
Proof
  strip_tac >>
  `well_typed_expr env (Call ann (RawCallTarget flags) args dflt)` by
    fs[expr_body_pre_def] >>
  drule raw_call_typed_data_dynamic >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[well_typed_expr_def] >> strip_tac >>
  namedCases_on `args` ["", "a rest"] >> gvs[] >>
  Cases_on `rest` >> gvs[]
QED

Theorem eval_expr_raw_call_operand_exit:
  eval_exprs cx args es = (INR exc, es') ==>
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) es = (INR exc, es')
Proof
  strip_tac >> simp[Once evaluate_def, bind_def]
QED

Theorem eval_expr_raw_call_operands:
  eval_exprs cx args es = (INL (addr_v::data_v::kvs), es1) /\
  dest_AddressV addr_v = SOME target /\ dest_BytesV data_v = SOME data /\
  LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) es =
    eval_raw_call cx flags target data amount
      (forwarded_gas default_evm_gas_limit
         (ext_call_kwarg EKGas flags.rcf_kws kvs)) es1
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_option_type_def,
       check_def, dest_AddressV_def, dest_BytesV_def]
QED

Theorem compile_expr_raw_call_steps:
  compile_expr cenv ty (Call ann (RawCallTarget flags) (a::d::kws) dflt) sa =
    (vv,sb) ==>
  ?addr data len ptr vo go ignored gas ov op result s1 s2 s3 s4 s5 s6 s7.
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    emit_op MLOAD [data] s2 = (len,s3) /\
    emit_op ADD [data; Lit 32w] s3 = (ptr,s4) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
      ((vo,go,ignored),s5) /\
    (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
    compile_raw_call_finish addr ptr len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  Cases_on `flags.rcf_max_outsize = 0` >> gvs[]
QED

Theorem expr_body_pre_raw_call_arg:
  !cenv cx env ann flags args dflt e es es'.
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem raw_call_kwargs_types:
  raw_call_kws_ok flags es ==>
  EVERY (\k. k = EKValue \/ k = EKGas) flags.rcf_kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) es
Proof
  simp[raw_call_kws_ok_def] >> strip_tac >>
  `EVERY (\k. k = EKValue \/ k = EKGas) flags.rcf_kws` by
    (simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `k` >> gvs[]) >>
  simp[] >>
  `EVERY (\t. t = BaseT (UintT 256)) (MAP expr_type es)` suffices_by
    simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM k flags.rcf_kws` >>
  `k = EKValue \/ k = EKGas` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM]) >>
  gvs[ext_call_kw_type_def]
QED

Theorem raw_call_kwargs_word_args:
  !ks es sa vo go d sb.
    EVERY (\k. k = EKValue \/ k = EKGas) ks /\
    LENGTH es = LENGTH ks /\
    compile_ext_call_kwargs compile_expr cenv NoneT ks es sa = ((vo,go,d),sb) ==>
    ?xs. lower_word_args cenv (K (BaseT (UintT 256))) es sa = (xs,sb) /\
         vo = ext_call_kwarg EKValue ks xs /\
         go = ext_call_kwarg EKGas ks xs /\ d = NONE
Proof
  Induct >- simp[compile_ext_call_kwargs_def, lower_word_args_def,
                comp_return_def, ext_call_kwarg_def] >>
  rpt gen_tac >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def, lower_word_args_def, comp_return_def] >>
  strip_tac >>
  gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  first_x_assum drule_all >> strip_tac >>
  gvs[ext_call_kwarg_def]
QED

Theorem ext_call_kwarg_member:
  !ks xs op. ext_call_kwarg kw ks xs = SOME op ==> MEM op xs
Proof
  Induct_on `ks` >> Cases_on `xs` >> simp[ext_call_kwarg_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem raw_call_keywords_post:
  !ks xs vs.
    typed_args_post H ctx func cenv cx es sa s0 es' ks xs vs s /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) ks ==>
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs
Proof
  simp[exprSimPrecompilesTheory.typed_args_post_def] >> rpt strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_x_assum `LENGTH ks = LENGTH vs` mp_tac >>
  qpat_x_assum `EVERY _ ks` mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac [`xs`, `vs`, `ks`] >>
  Induct >> rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[vyperValueTheory.evaluate_type_def] >>
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  first_x_assum irule >> simp[]
QED

Theorem raw_call_value_operand:
  !ks xs vs.
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs /\
    EVERY (value_has_type (BaseTV (UintT 256))) vs ==>
    ?amount. raw_call_value ks vs = SOME amount /\
      eval_operand (case ext_call_kwarg EKValue ks xs of
        NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
      amount < dimword (:256)
Proof
  Induct >- simp[raw_call_value_def, ext_call_kwarg_def, venomStateTheory.eval_operand_def] >>
  rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[raw_call_value_def, ext_call_kwarg_def, venomStateTheory.eval_operand_def] >>
  strip_tac >> gvs[] >> Cases_on `h = EKValue` >> gvs[]
  >- (drule uint256_typed_dest >> simp[wordsTheory.w2n_lt] >>
      qspec_then `(typed_val_to_w256 (BaseTV (UintT 256)) h''):bytes32`
        mp_tac wordsTheory.w2n_lt >> simp[]) >>
  first_x_assum drule_all >> simp[raw_call_value_def]
QED

Theorem raw_call_keyword_values:
  !ks es vs es'.
    EVERY (\e. expr_type e = BaseT (UintT 256) /\
      !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) ks /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx ks es = (INL vs,es') ==>
    EVERY (value_has_type (BaseTV (UintT 256))) vs /\
    LENGTH vs = LENGTH ks /\ expr_sim_inv cenv cx env es'
Proof
  Induct >- simp[eval_exprs_nil] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  qpat_x_assum `!es vs es'. _` drule_all >> simp[]
QED

Theorem raw_call_keywords_decode:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  expr_sim_inv cenv cx env es2 /\
  eval_exprs cx kws es2 = (INL kvs,es') /\
  typed_args_post H ctx func cenv cx es0 sa s0 es' kws xs kvs s ==>
  ?amount. raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
    amount < dimword (:256) /\
    (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws /\ expr_sim_inv cenv cx env es'
Proof
  strip_tac >> drule raw_call_pre_flags >> simp[] >> strip_tac >>
  drule raw_call_kwargs_types >> strip_tac >>
  `EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws` by
    (simp[listTheory.EVERY_MEM] >> rpt gen_tac >> strip_tac >> conj_tac
     >- fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all raw_call_keyword_values >> strip_tac >>
  drule_all raw_call_keywords_post >> strip_tac >>
  drule_all raw_call_value_operand >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `LENGTH kvs = LENGTH flags.rcf_kws` by decide_tac >>
  qexists_tac `amount` >> fs[] >> strip_tac >>
  `~MEM EKValue flags.rcf_kws` by fs[vyperTypeSystemTheory.raw_call_kws_ok_def] >>
  gvs[raw_call_value_def, ext_call_kwarg_not_mem]
QED

Theorem raw_call_outbuf_steps:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (((cap + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
    ov = buf.buf_operand /\ emit_op ADD [ov; Lit 32w] sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_zero_steps:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) ==>
  ?buf. compile_alloc_buffer 0 sa = (buf,sb) /\
    ov = buf.buf_operand /\ op = buf.buf_operand
Proof
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_positive_code:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (((cap+31) DIV 32)*32+32))]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (SUC sa.cs_next_id) ADD [ov; Lit 32w]
       [STRING #"%" (toString (SUC sa.cs_next_var))]] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[arithmeticTheory.ADD1, listTheory.APPEND_ASSOC]
QED
