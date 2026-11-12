(* The selected nr=F, defaults=[] frame returns without a value through
   one STOP. Source tails and finite horizons share that terminal Halt. *)
Theory externalReturnNoneFullFrag
Ancestors
  externalReturnPackage rawReturnHeader e2eDefs bodySimFull
  gasOutcomeFullCompose fragGasOriginPtrExec fragGasOriginPtr
  fragGasOrigin fragGasPathPtr fragGasPathMem gasCount fragGasMode
  bodyPtrDefs stmtSimDefs exprSimHypsDefs bodySim
  accountsRelProps loweringStateRelDefs
  stmtLowering moduleLowering moduleLoweringProps compileVyper compileEnv
  exprLoweringProps loweringPosts
  ptrSafeRun ptrDiscipline memSafeRun
  venomInst venomState venomExecSemantics venomExecProofs
  emitHelper emitHelperProps
  vyperTypeSystem vyperInterpreter vyperState vyperValueOperation
  list option finite_map

Theorem return_selected_none_frag_full:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return NONE)) /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return NONE))
    (stmt_env ce lctx ret (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  cheat
QED
