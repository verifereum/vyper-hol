Theory bodyFullExtCallCompose
Ancestors
  bodyFullExtCallRequest bodyFullExtCallStep bodyFullExtCallReturn
  bodySimFull bodyFullPreds vyperInterpreter vyperAST list

val _ = Parse.hide "body";

Theorem extcall_vv_full_ok:
  !cx ann is_static skip sig opts args dflt
   DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 args)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) args)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 args) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 args))) /\
    body_exprs_full_ok cx (TAKE 1 args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Call ann (ExtCall is_static skip sig opts) args dflt) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann (ExtCall is_static skip sig opts) args dflt) es
Proof
  rpt gen_tac >> PairCases_on `sig` >> strip_tac >> gvs[] >>
  rw[expr_vv_sim_full_def] >>
  irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
    extcall_request_full) >>
  simp[] >> conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`cenv`, `d`, `env`, `sa`, `sb`, `shadow_func`,
    `shadow_sa`, `shadow_sb`, `tops`, `ty`, `vv`] >>
  simp[] >> rpt strip_tac >>
  simp[eval_ext_call_def, vyperStateTheory.type_check_def,
       vyperStateTheory.lift_option_type_def] >>
  simp[vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_return] >>
  `!err. vyperState$assert T err = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  simp[vyperStateTheory.bind_return] >>
  `is_static' <=>
    (if is_static' then NONE else
      case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
        NONE => SOME 0 | SOME v => dest_NumV v) = NONE` by
    metis_tac[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
  `(if is_static' then return NONE else
     case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
       NONE => return (SOME 0)
     | SOME v => bind (case dest_NumV v of
          NONE => raise (Error (TypeError "ExtCall value not int"))
        | SOME n => return n) (\n. return (SOME n))) =
    return (if is_static' then NONE else
     case ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest) of
       NONE => SOME 0 | SOME v => dest_NumV v)` by
    (Cases_on `is_static'` >- simp[] >>
     Cases_on `ext_call_kwarg EKValue opts (DROP (LENGTH sig1) rest)`
     >- simp[] >> rename1 `SOME v` >>
     Cases_on `dest_NumV v` >> gvs[vyperStateTheory.bind_return]) >>
  simp[vyperStateTheory.bind_return] >>
  qmatch_goalsub_abbrev_tac `bind (eval_ext_call_effects cx target calldata _ _ _) kont` >>
  qabbrev_tac `callgas = forwarded_gas default_evm_gas_limit
    (ext_call_kwarg EKGas opts (DROP (LENGTH sig1) rest))` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ post _` >>
  simp[ETA_THM] >>
  irule (SIMP_RULE (srw_ss()) [vyperStateTheory.ignore_bind_def, ETA_THM]
    (Q.INST [`k` |-> `kont`, `gas` |-> `callgas`, `Q` |-> `post`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
       (SPEC_ALL extcall_call_full))) >>
  simp[] >>
  qexistsl [`G0`, `addr_op`, `buf_op`, `call_len`, `call_offset`,
    `abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap sig2 then TupleT [sig2] else sig2)`,
    `cenv`, `d`, `default_op`,
    `ext_call_kwarg EKDefault opts (DROP (LENGTH sig1) rest)`, `default_ty`,
    `es`, `gas_op`, `has_default`, `is_static'`, `s0`, `sa`, `sp`, `sr`,
    `tn0`, `u`, `value_op`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  unabbrev_all_tac >> rpt strip_tac >> simp[] >>
  irule (SIMP_RULE (srw_ss()) [vyperStateTheory.ignore_bind_def,
    loweringPostsTheory.post_value_type_def, arithmeticTheory.ADD_COMM, ETA_THM]
    extcall_return_full) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qexistsl [`addr_op`, `buf_op`, `default_op`, `default_ty`, `has_default`, `sr`] >>
  simp[]
QED
