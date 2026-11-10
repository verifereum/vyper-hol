(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalFrameRetOk
Ancestors
  externalReturnNoneFrag externalReturnValuedFrag bodySimFull
  externalReturnSelectedResources vyperTypeCallGraph
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

(* The selected frame's two counted return fragments discharge the return
   continuation. Valued returns retain the successful producer's physical
   layout facts and use actual value footprints through normalization. *)
Theorem external_frame_ret_ok:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
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
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok unit.cu_context func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es r. ?tv v'.
         evaluate_type (type_env tops) ret = SOME tv /\
         safe_cast tv v = SOME v' /\
         external_call_result_rel tops ret tx
           (INL v', finalize_pending_deletions
                      (abstract_machine_from_state am.sources am.exports
                         am.layouts es),
            es.requests) r)
      cenv ret
Proof
  rpt gen_tac >> strip_tac >>
  simp[frame_ret_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (irule return_selected_none_frag >>
      qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
      qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
      qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
      simp[initial_evaluation_context_def]) >>
  irule return_selected_valued_frag >>
  qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
  qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  drule_all return_selected_consumer_resources >> strip_tac >>
  drule source_deployment_context >> strip_tac >>
  fs[initial_evaluation_context_def, int_calls_stmt_def, int_calls_expr_def]
QED

Theorem external_frame_ret_word_full:
 !D lo d ctx shadow_ctx PG func shadow_func cx cenv ret tops am tx nkey ut iv.
  cenv.ce_return_pc = NONE /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  cenv.ce_raw_return = lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  ~cenv.ce_raw_return /\ is_word_type ret /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops ==>
  frame_ret_ok_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx
   (\v ee gt r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
     safe_cast tv v = SOME v' /\
     external_call_result_rel tops ret tx
       (INL v', finalize_pending_deletions
         (abstract_machine_from_state am.sources am.exports am.layouts ee),ee.requests) r)

   cenv ret

Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- gvs[type_stmt_def, is_word_type_def] >>
  rename1 `Return (SOME e)` >>
  `cenv'.ce_return_pc = NONE /\
   cenv'.ce_nonreentrant = (F,nkey,ut,iv) /\
   cenv'.ce_raw_return = cenv.ce_raw_return` by
    fs[same_frame_def, compile_env_component_equality] >>
  mp_tac (Q.SPECL
    [`D`, `lo`, `d`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `cx`, `cenv'`, `lctx`, `ret`, `e`, `env`, `es`, `tops`, `am`, `tx`,
     `nkey`, `ut`, `iv`] compile_return_word_external_frag_full) >>
  gvs[]
QED

