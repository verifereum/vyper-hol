(* The selected external frame's return continuation on finite horizons,
   for loweringRuntimeCorrect's lower_vyper_runtime_unit_body_joint. *)
Theory externalFrameRetOk
Ancestors
  e2eDefs bodySimFull supportedProgram compileVyper moduleLowering
  vyperInterpreter

val _ = Parse.hide "body";

(* The selected frame's two Return producers, NONE and valued, discharge
   the frame's return continuation at every valid horizon.
   STAGED HEADER: the proof is the Cases_on `eo` composition of
   return_selected_none_frag_full and return_selected_valued_frag_full,
   added once those producers land. *)
Theorem external_frame_ret_ok_full:
  !DF lo d shadow_ctx PG func shadow_func tops rpolicy unit am tx ret vs
   mut args fbody env lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt
   st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_full (DF, lo, d, unit.cu_context, shadow_ctx, PG, func,
                       shadow_func)
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\H v ee gt r. ?tv v'.
         evaluate_type (type_env tops) ret = SOME tv /\
         safe_cast tv v = SOME v' /\
         external_call_result_rel H tops ret tx
           (INL v', finalize_pending_deletions
                      (abstract_machine_from_state am.sources am.exports
                         am.layouts ee),
            ee.requests) r)
      cenv ret
Proof
  cheat
QED
