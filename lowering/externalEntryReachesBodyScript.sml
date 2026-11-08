(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalEntryReachesBody
Ancestors
  entryReachBodyStateAssembly entryReachBodyRootChecks entryReachBodySelectedCode
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* ADMITTED (#639): the run from __entry reaches the start sa of the
   selected function's guarded body (after the selector dispatch, the
   entry checks and compile_register_positional_args), in a state s0
   related by stmt_state_rel, in the body's compile env cenv, to es0, the
   source state where the body starts, with the GAS readings still
   unread; and every result from s0 is a
   result of run_context.  The code from sa on is compile_guarded_body's
   in cenv, in the function func that runs it; cenv0 is the compile env
   lower_vyper_runtime_unit packages for the function (supported_program
   rules out raw returns). *)
(* Notes for the proof (read, not built):
   - alloca_room at s0: run_lowering checks lowering_context_ok, whose
     alloca budget bounds the unit's static allocations;
     allocaFrontierBound's alloca_frontier_inv_entry gives the bound at
     __entry's entry (vs_alloca_next = 0, no allocas), and
     step_inst_alloca_budget keeps it along the INVOKE-free dispatch,
     checks and decode.
   - fmp_room at s0: initial_venom_state_rel says nothing about vs_fmp, so
     it must hold vacuously: DALLOCA is emitted only by
     compile_alloc_dynamic (builtinCreate, and builtinSystem's raw_call of
     msg.data), and supported_program excludes raw calls and every create
     form (supported_raw_call_forms_excluded), so no function reachable from
     __entry has a DALLOCA.
   - The calldata decode passes hi_op = Lit 0w, so a canonical encoding
     (valid_vyper_call) meets only the clamps: basetype clamps, bytestring
     length <= max, dynamic array count <= max, which bind_arguments'
     well-typed values satisfy.
   - local_ptrs_reserved: entryLocals' external_entry_locals. *)
Theorem external_entry_reaches_body:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      stmt_state_rel unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
Proof
  cheat
QED

