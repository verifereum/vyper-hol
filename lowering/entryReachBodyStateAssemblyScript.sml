(* Body-entry state relation at the end of positional argument registration. *)
Theory entryReachBodyStateAssembly
Ancestors
  entryReachBodyRegistrationIteration entryReachBodyRuntimeState
  entryReachBodyAllocationRoom entryReachBodyFmp
  exprLoweringProps compileEnv compileVyper moduleLowering
  e2eDefs supportedProgram vyperInterpreter vyperState venomState

(* At the state t where registration of every positional argument ends,
   the full stmt_state_rel holds against the source state es0 where the
   body starts.  The premises are the frozen external_entry_reaches_body
   premises plus what entry_registration_full_run concludes about t. *)
Theorem entry_body_state_assembly:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\
  source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
    (INL (), es0) /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
       (mut, F, lookup_raw_return_or_F (NONE : num option)
                   tx.function_name External tops,
        tx.function_name, args, ([] : expr list), ret, fbody)) =
    (lbl, ce, pos, cds, pay, F, key, ut, view, fbody, rt) /\
  compile_register_positional_args ce pos 4 start = (cef, registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((), final) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  MEM fn unit.cu_context.ctx_functions /\ fn_inst_ids_distinct fn /\
  fn_has_code start final fn /\
  entry_prefix_witness fn (type_env tops) args tx.args (LENGTH args)
    cef registered t /\
  alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
  abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
  (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < registered.cs_next_id) /\
  entry_loop_fields vs t /\ cef.ce_is_ctor = F ==>
  stmt_state_rel unit.cu_context fn cef
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 t
Proof
  cheat
QED
