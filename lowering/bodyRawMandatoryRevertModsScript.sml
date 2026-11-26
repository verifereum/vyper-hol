(* The mandatory-failure finish forwards the whole reply from the fetched
   CALL endpoint. It does not inspect or read the bounded output buffer. *)
Theory bodyRawMandatoryRevertMods
Ancestors
  bodyFullRawCallRevertExit exprSimDefs exprLoweringProps emitHelper
  fragGasOriginPtr ptrDiscipline venomState venomInst compileEnv context
  vyperCallOutcome vyperState words

Theorem raw_call_mandatory_revert_path_mods:
  compile_raw_call_finish to_op dp dl gas_op val_op call_ty n T ov op sa =
    (result,sb) /\
  (case call_ty of
     RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
   | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
   | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)])
    sa = (status,sc) /\
  ~outcome.co_success /\
  eval_operand status q = SOME 0w /\ op_taint tn status = {} /\
  op_prov G status = NONE /\ fn_has_code sc sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp q /\
     q.vs_alloca_next + pending_alloca_size func q <= w2n q.vs_initial_fmp) /\
  allocas_from lo q /\ lo <= q.vs_alloca_next /\ ~q.vs_halted /\
  q.vs_current_bb = sc.cs_current_bb /\ q.vs_inst_idx = LENGTH sc.cs_current_insts /\
  q.vs_returndata = outcome.co_returnData /\
  LENGTH outcome.co_returnData < dimword (:256) /\
  res = INR (Error (RevertData outcome.co_returnData)) ==>
  ?u Gf tnf.
    u.vs_returndata = outcome.co_returnData /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (q,G,tn) [] (Abort Revert_abort u,Gf,tnf)) /\
    (!H cx ee. expr_exit res (Abort Revert_abort u) /\
       halt_exit H cx ee res (Abort Revert_abort u) /\
       (ctx_has_dalloca ctx ==>
          !t. Abort Revert_abort u = Halt t ==> allocas_below_fmp t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH q.vs_returndata < dimword (:256)` by simp[] >>
  drule_all raw_call_revert_suffix_full_exit >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> simp[expr_exit_def,halt_exit_def]
QED
