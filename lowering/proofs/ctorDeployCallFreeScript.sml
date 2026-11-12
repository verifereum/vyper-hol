(* A call-free constructor lowers to a deployment entry function that makes
 * no internal or external calls: no INVOKE and no RETURNDATACOPY.
 * TOP-LEVEL: lower_vyper_deploy_unit_call_free_entry (used by
 * deploy_frame_gas_sufficient; admitted until proved).
 *)
Theory ctorDeployCallFree
Ancestors
  compileVyper vyperCompiler e2eDeployDefs venomInst ctorCallFreeEntry
  ctorCallFreeBodies ctorCallFreeExpr ctorCallFreeStmtReturns ctorCallFreeStmtStorage
  ctorCallFreeStmtLogs

(* The lowering emits INVOKE only for an internal call and RETURNDATACOPY
   only on the external-call, raw_call and create paths, all of which
   constructor_call_free excludes from __init__'s body; typing fixes each
   builtin's argument count, so no lowering reads past its arguments.
   Without a constructor the entry is the fixed CODECOPY/RETURN stub. *)
Theorem lower_vyper_deploy_unit_call_free_entry:
  !tops rpolicy runtime_bc dunit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    constructor_call_free tops /\ deploy_typing_ok tops am tx
    ==>
    ?efn.
      dunit.cu_context.ctx_entry = SOME efn.fn_name /\
      lookup_function efn.fn_name dunit.cu_context.ctx_functions = SOME efn /\
      !inst. MEM inst (fn_insts efn) ==>
             inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> INVOKE
Proof
  cheat
QED
