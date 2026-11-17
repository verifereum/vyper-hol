(* The selected external frame's return continuation on finite horizons,
   for loweringRuntimeCorrect's lower_vyper_runtime_unit_body_joint. *)
Theory externalFrameRetOk
Ancestors
  e2eDefs bodySimFull supportedProgram compileVyper moduleLowering
  vyperInterpreter externalReturnNoneFullFrag externalReturnValuedFull
  externalReturnPackage exprSimHypsDefs vyperState vyperContext vyperTypeCallGraph
  entryReachBodyFmp

val _ = Parse.hide "body";

(* The selected frame's two Return producers, NONE and valued, discharge
   the frame's return continuation at every valid horizon.
   Both producers share the selected package and actual return endpoint. *)
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
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[entry_runtime_no_dalloca] >>
  drule source_deployment_context >> strip_tac >>
  simp_tac std_ss [frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  `ut' = T` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >> gvs[] >>
  `cenv'.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
      tx.function_name External tops` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> strip_tac >>
     drule return_register_metadata >> strip_tac >>
     drule return_same_frame_metadata >> simp[]) >>
  Cases_on `eo` >> simp[]
  >- (mp_tac (Q.INST [`DF` |-> `DF`, `lo` |-> `lo`, `d` |-> `d`,
      `ctx` |-> `unit.cu_context`, `shadow_ctx` |-> `shadow_ctx`,
      `PG` |-> `PG`, `func` |-> `func`, `shadow_func` |-> `shadow_func`,
      `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
      `target` |-> `rpolicy.rpol_target`, `ut` |-> `T`,
      `nkey_map` |-> `K global_nonreentrant_slot`,
      `rr` |-> `lookup_raw_return_or_F (NONE:num option)
                  tx.function_name External tops`,
      `lbl` |-> `lbl`, `cenv0` |-> `cenv0`, `pos_args` |-> `pos_args`,
      `min_cds` |-> `min_cds`, `is_payable` |-> `is_payable`,
      `nkey` |-> `nkey`, `iv` |-> `iv`, `rt` |-> `rt`,
      `off` |-> `4`, `st` |-> `st`, `cenv` |-> `cenv`, `sinit` |-> `sa`,
      `ce` |-> `cenv'`, `env` |-> `env'`, `lctx` |-> `lctx`, `es` |-> `es`,
      `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`] return_selected_none_frag_full) >>
      impl_tac
      >- (simp[initial_evaluation_context_def] >>
          fs[initial_evaluation_context_def]) >> simp[]) >>
  rename1 `stmt_exprs_ok cenv' (Return (SOME e))` >>
  mp_tac (Q.INST [`DF` |-> `DF`, `lo` |-> `lo`, `d` |-> `d`,
      `ctx` |-> `unit.cu_context`, `shadow_ctx` |-> `shadow_ctx`,
      `PG` |-> `PG`, `func` |-> `func`, `shadow_func` |-> `shadow_func`,
      `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
      `target` |-> `rpolicy.rpol_target`, `ut` |-> `T`,
      `nkey_map` |-> `K global_nonreentrant_slot`,
      `rr` |-> `lookup_raw_return_or_F (NONE:num option)
                  tx.function_name External tops`,
      `lbl` |-> `lbl`, `cenv0` |-> `cenv0`, `pos_args` |-> `pos_args`,
      `min_cds` |-> `min_cds`, `is_payable` |-> `is_payable`,
      `nkey` |-> `nkey`, `iv` |-> `iv`, `rt` |-> `rt`,
      `off` |-> `4`, `st` |-> `st`, `cenv` |-> `cenv`, `sinit` |-> `sa`,
      `ce` |-> `cenv'`, `env` |-> `env'`, `lctx` |-> `lctx`, `es` |-> `es`,
      `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`] return_selected_valued_frag_full) >>
  impl_tac
  >- (simp[initial_evaluation_context_def, get_tenv_def] >>
      fs[initial_evaluation_context_def, get_tenv_def,
         int_calls_stmt_def, int_calls_expr_def]) >> simp[]
QED
