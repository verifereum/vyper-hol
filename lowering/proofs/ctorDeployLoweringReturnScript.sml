(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringReturn
Ancestors
  ctorDeployLoweringDefs o1PassContract ctorReturnFrame

(* A constructor that finishes normally (falls off its end or returns)
   halts returning the runtime code and the immutables section, with the
   source's accounts, transient storage and logs. *)
Theorem deploy_ctor_return:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut am_c es0 gs res st final.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs
      (entry_venom_state prog cplan es with vs_alloca_next := ctor_imm_len tops) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gs; outcomes := SOME vs.vs_outcomes |>) =
      (res, st) /\
    (res = INL () \/ res = INR (ReturnException NoneV)) /\
    constructor_return_q func cenv (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
      (ctor_imm_len tops) nr nkey NoneV (st with scopes := []) (Halt final) /\
    final.vs_code = vs.vs_code /\ final.vs_labels = vs.vs_labels ==>
    deploy_venom_result_rel tops runtime_bc tx
      (deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st) (Halt final)
Proof
  cheat
QED
