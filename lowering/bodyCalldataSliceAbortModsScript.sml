(* The reached calldata slice offset fails before buffer allocation. *)
Theory bodyCalldataSliceAbortMods
Ancestors
  bodyFullBuiltinBytestringCalldataAbort exprSimCalldataSlice
  gasOutcomeFullPostMods gasShadowCompileStmtHelpers
  exprLoweringProps loweringStateRelDefs vyperTypeInvariants
  exprSimDefs exprSimWordArgs fragExec haltExitProj vyperContext words

Theorem calldata_slice_abort_outcome_mods:
  compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes cenv ann) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  eval_operand x t = SOME (n2w a) /\ op_prov G x = NONE /\ op_taint tn x = {} /\
  (!y. x = Var y ==> not_fresh_at sm y) /\
  a < dimword (:256) /\ n < dimword (:256) /\ 0 < n /\
  context_well_typed cx /\ stmt_state_rel H0 ctx func cenv cx mid t /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~(a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (\m. ((case builtin_result cx m.accounts ann (CalldataSlice n)
                  [BaseT (UintT 256)] [IntV (&a)] of
              INL r => INL (Value r) | INR ex => INR ex),m))
    (mid,t,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `alloca_inv t /\ t.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[context_well_typed_def,dimword_def] >>
  `?u HG tm. !D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G,tn) [] (Abort Revert_abort u,HG,tm)` by
    (irule bytestring_calldata_full_abort >>
     qpat_assum `compile_slice_calldata _ _ _ _ = _` (irule_at Any) >>
     simp[] >> qexists_tac `a` >> simp[] >> decide_tac) >>
  `?msg. !acc. builtin_result cx acc ann (CalldataSlice n)
    [BaseT (UintT 256)] [IntV (&a)] = INR (Error (RuntimeError msg))` by
    (Cases_on `2 ** 256 <= a+n`
     >- (qexists_tac `"calldata slice overflow"` >>
         simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
              evaluate_calldata_slice_uint]) >>
     `~(a+n <= LENGTH cx.txn.calldata)` by fs[dimword_def] >>
     qexists_tac `"evaluate_slice range"` >>
     simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
          evaluate_calldata_slice_uint]) >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  qexistsl_tac [`HG`,`mid`,`INR (Error (RuntimeError msg))`,`tm`,`u`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_not_halt]
QED
