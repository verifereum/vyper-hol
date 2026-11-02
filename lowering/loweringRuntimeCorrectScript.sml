(*
 * S1, lower_vyper_runtime_unit_correct, composed from its three pieces
 * (#642)
 *
 * The source runs the external function valid_vyper_call selects: it
 * binds the arguments, moves the call value (send_call_value) and runs the
 * body; call_external_body then turns the body's outcome into the call's
 * result.  The lowered code runs the same three steps:
 *   - the entry (#639): from the initial state, run_context reaches the
 *     start of the selected function's guarded body in a state related
 *     by stmt_state_rel to the source state where the body starts, or,
 *     when the source cannot move the value, ends in a matching abort;
 *   - the body (#636-#638): bodySimMain's body_stmts_sim, in the
 *     external function's frame;
 *   - the halt (#640): a return statement exits as the frame's RetQ
 *     accepts (external_frame_ret_ok, from the return sequences of
 *     vyperLoweringCorrect), and falling off the end of a function
 *     without a return type stops (external_fallthrough_result_rel_any).
 *
 * The pieces still to prove are stated as the composition uses them, each
 * with the issue it belongs to.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_correct -- S1
 *   external_fallthrough_result_rel_any -- the fall-through halt, with
 *     state_rel at any compile env
 *   call_external_selected_body -- the source runs the selected body
 *   type_stmts_none_valued_return -- a body typed at NoneT has no valued
 *     return
 *
 * Named admissions (cheats), each a piece S1 rests on:
 *   external_body_source_ok -- the source side (typing soundness)
 *   external_entry_value_revert, external_entry_reaches_body -- the entry
 *     bridge (#639)
 *   external_body_frame -- the body judgment's premises at the body's
 *     start (#637)
 *   external_frame_ret_ok -- the frame's returns (#640)
 *   external_body_revert_data_reverts -- a failed external call reverts:
 *     expr_exit allows any Abort for RevertData, external_call_result_rel
 *     asks a revert
 *   stmts_env_ret_ty -- a supported body without a valued return
 *     compiles the same at every return type
 *)

Theory loweringRuntimeCorrect
Ancestors
  list pair fragExec stmtSim bodySim bodySimMain loweringHalt stmtLoweringMono exprSim exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  entryStateRel supportedDecls vyperTypeContractFunction vyperTypeContractSoundness
  vyperTypeContractContext vyperTypeContract
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* ===== The source side (#639) ===== *)

(* The call valid_vyper_call selects runs call_external_body from the
   bound arguments, with pending deletions finalised on success. *)
Theorem call_external_selected_body:
  !tops am tx ret mut args fbody env orc.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env ==>
    call_external orc [] am tx =
      case call_external_body orc [] am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             F mut (type_env tops) env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rw[source_deployment_rel_def] >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function orc [] am cx` >>
  `call_external_function orc [] am cx F mut tops [(NONE, tops)] args []
     tx.args fbody ret =
   call_external_body orc [] am cx F mut (type_env tops) env fbody ret` by
    (qpat_assum `_ = type_env tops` (SUBST1_TAC o SYM) >>
     irule call_external_function_body >>
     simp[evaluate_defaults_def, Abbr `cx`]) >>
  simp[]
QED

Theorem external_selected_body_typing:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) ==>
  ?art env_t env'.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    checked_contract_runtime_ready art [(NONE,tops)] am tx /\
    env_t.current_src = NONE /\
    env_t.type_defs = get_tenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    env_t.fn_sigs = art.cta_fn_sigs /\
    env_t.bare_globals = art.cta_bare_globals /\
    env_t.bare_global_assignable = art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_t.flag_members = art.cta_flag_members /\
    type_stmts env_t ret fbody = SOME env' /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_t.var_types id = SOME ty /\
      FLOOKUP env_t.var_assignable id = SOME T) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      MEM (n,ty) args) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?ty. MEM (n,ty) args /\ b = T) /\
    stmts_no_control_escape fbody /\
    (ret <> NoneT ==> stmts_no_fallthrough fbody) /\
    call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (int_calls_stmts fbody)
Proof
  strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw tx.function_name args [] ret fbody) tops` by
    (irule lookup_function_external_decl >> simp[] >>
     qexists `tops` >> gvs[supported_program_def, supported_declaration_headers_def]) >>
  gvs[source_typing_ok_def, source_deployment_rel_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `External <> Deploy` by simp[] >>
  `ALOOKUP [(NONE,tops)] NONE = SOME tops` by simp[] >>
  drule checked_function_body_typing_package >>
  simp[] >> disch_then drule >> simp[] >>
  strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     mut F args [] ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl [`tx.function_name`, `raw`, `External`] >> simp[]) >>
  conj_tac >- gvs[check_function_body_def] >>
  conj_tac >- gvs[check_function_body_def] >>
  drule checked_explicit_external_body_call_evaluation_safe >>
  simp[] >> disch_then drule >> simp[]
QED

(* ADMITTED (typing soundness): the body of a checked external function
   ends in an outcome the statement judgment speaks of (no type error, no
   break or continue outside a loop), and it falls off its end only when
   the function has no return type (the type checker's
   stmts_no_fallthrough).  Most of it should follow from
   checked_selected_entry_no_static_error and
   callable_body_typing_from_env_consistent. *)
Theorem external_body_source_ok:
  !tops am tx ret vs mut args fbody env es0 res es'.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es0 = (res, es') ==>
    stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)
Proof
  cheat
QED

(* ===== The entry (#639) ===== *)

(* ADMITTED (#639): when the source cannot move the call value (a
   nonpayable function called with value), the run from __entry aborts as
   external_call_result_rel asks (entryChecksProps's
   entry_checks_nonpayable_value, after the selector dispatch). *)
Theorem external_entry_value_revert:
  !tops rpolicy unit am tx ret vs mut args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  cheat
QED

(* ADMITTED (#639): the run from __entry reaches the start sa of the
   selected function's guarded body (after the selector dispatch, the
   entry checks and compile_register_positional_args), in a state s0
   related by stmt_state_rel, in the body's compile env cenv, to es0, the
   source state where the body starts; and every result from s0 is a
   result of run_context.  The code from sa on is compile_guarded_body's
   in cenv, in the function func that runs it; cenv0 is the compile env
   lower_vyper_runtime_unit packages for the function (supported_program
   rules out raw returns). *)
Theorem external_entry_reaches_body:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
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
           (mut, F, F, tx.function_name, args, [], ret, fbody)) =
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
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
Proof
  cheat
QED

(* ===== The body's frame (#637) ===== *)

(* ADMITTED (#637): at the start of the selected function's body, the
   premises of body_stmts_sim other than the frame's returns: the frame is
   the lowered program's (body_inv), the body is supported and typed at
   the return type in a type environment env_t of the parameters, which
   the compile env and the source state agree with and whose locals fit
   the allocation limit, and the external frame has no return PC and no
   lock. *)
Theorem external_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
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
         (mut, F, F, tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      EVERY (stmt_exprs_ok cenv) fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
Proof
  cheat
QED

(* ===== The frame's returns (#640) ===== *)

(* ADMITTED (#640): in the selected external function's frame, a return
   statement exits as S1 asks of the call: the returned value casts to the
   return type, and the run halts in external_call_result_rel's success
   case for it, at the source state after the return.  Its cases are the
   return sequences of vyperLoweringCorrect (external_return_none_result_rel,
   external_return_word_result_rel, external_return_static_cenv_result_rel,
   external_return_abi_cenv_result_rel), after the returned expression's
   simulation; dynamic returns and returns whose value widens to the
   return type (frame_ret_ok's comment) are not covered by them yet. *)
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
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, F, tx.function_name, args, [], ret, fbody)) =
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
  cheat
QED

(* ADMITTED (mismatch between the body judgment and S1's result relation):
   when the body ends in a failed external call's RevertData, the run from
   the body's start aborts with a revert.  stmt_frag's expr_exit allows any
   Abort for RevertData, while external_call_result_rel asks a revert. *)
Theorem external_body_revert_data_reverts:
  !tops bindings ctx func cenv cx env_t env' ret_ty RetQ fbody es0 d es' sa
   sb cenv' s0 fuel a t.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings fbody /\
    expr_sim_inv cenv cx env_t es0 /\ ce_locals_declared cenv env_t /\
    locals_alloc_ok cenv env_t /\
    type_stmts env_t ret_ty fbody = SOME env' /\
    EVERY (stmt_exprs_ok cenv) fbody /\
    call_evaluation_safe cx (int_calls_stmts fbody) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx fbody es0 = (INR (Error (RevertData d)), es') /\
    stmts_env cenv NoLoop ret_ty fbody sa = (cenv', sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    ~block_is_terminated sa /\ stmt_state_rel ctx func cenv cx es0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_from fuel ctx func s0 = Abort a t ==>
    a = Revert_abort
Proof
  cheat
QED

(* ===== The fall-through halt (#640) ===== *)

(* external_fallthrough_result_rel with state_rel at any compile env cenv'
   rather than the guarded body's: the body simulation ends at the compile
   env after the body's declarations. *)
Theorem external_fallthrough_result_rel_any:
  !ctx cenv cenv' nkey ut iv stmts st x st' sb func cx es tops tx srcs exps
     layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_guarded_body cenv F nkey ut iv stmts NONE st = (x, st') /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb ==>
    frag_exec ctx sb st'
      (\s. state_rel func cenv' cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `F`, `nkey`, `ut`, `iv`, `stmts`, `st`, `x`,
               `st'`, `st`, `sb`] mp_tac compile_guarded_body_stop_unlock_frag >>
  simp[comp_return_def] >> disch_then irule >> rpt strip_tac >>
  qspecl_then [`func`, `cenv'`, `cx`, `es`, `es`, `s`, `ss`, `F`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[vyperStateTheory.return_def] >>
  strip_tac >> gvs[external_call_result_rel_def, return_bytes_def,
                  abstract_machine_from_state_def]
QED

(* ===== The return type of a body without a valued return ===== *)

(* ADMITTED (lowering): compile_stmt reads the return type only to compile
   a valued return and as the element type of an Append whose target root
   has no array type.  A supported Append targets a storage dynamic array,
   whose type body_inv's compile env gives (ce_module_var_type), and no
   declaration changes that. *)
Theorem stmts_env_ret_ty:
  !ss tops bindings ctx cenv cx lctx ty ty'.
    supported_stmts tops bindings ss /\ body_inv tops ctx cenv cx /\
    ~stmts_valued_return ss ==>
    stmts_env cenv lctx ty ss = stmts_env cenv lctx ty' ss
Proof
  cheat
QED

(* type_stmt rejects Return (SOME e) at NoneT. *)
Theorem type_stmt_none_valued_return[local]:
  (!env ret_ty s.
     ret_ty = NoneT /\ IS_SOME (type_stmt env ret_ty s) ==>
     ~stmt_valued_return s) /\
  (!env ret_ty ss.
     ret_ty = NoneT /\ IS_SOME (type_stmts env ret_ty ss) ==>
     ~stmts_valued_return ss)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, stmt_valued_return_def] >>
  gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> metis_tac[]
QED

(* A body typed at NoneT has no valued return. *)
Theorem type_stmts_none_valued_return:
  !env ss env'.
    type_stmts env NoneT ss = SOME env' ==> ~stmts_valued_return ss
Proof
  metis_tac[type_stmt_none_valued_return, optionTheory.IS_SOME_DEF]
QED

(* ===== The source's result ===== *)

(* call_external_body without a lock, after the value moved to es0 and the
   body ran from es0 to es'. *)
Theorem call_external_body_run[local]:
  !orc am cx mut tenv env fbody ret es0 res es'.
    send_call_value mut cx
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts cx fbody es0 = (res, es') ==>
    (res = INL () ==>
     call_external_body orc [] am cx F mut tenv env fbody ret =
       (INL NoneV,
        abstract_machine_from_state am.sources am.exports am.layouts es',
        es'.requests)) /\
    (!v. res = INR (ReturnException v) ==>
     call_external_body orc [] am cx F mut tenv env fbody ret =
       case evaluate_type tenv ret of
         NONE => (INR (Error (TypeError "eval ret")), am, es'.requests)
       | SOME tv =>
           case safe_cast tv v of
             NONE => (INR (Error (TypeError "ext cast ret")), am,
                      es'.requests)
           | SOME v' =>
               (INL v',
                abstract_machine_from_state am.sources am.exports am.layouts
                  es', es'.requests)) /\
    (!e. res = INR e /\ (!v. e <> ReturnException v) ==>
     call_external_body orc [] am cx F mut tenv env fbody ret =
       (INR e, am, es'.requests))
Proof
  rpt gen_tac >> strip_tac >>
  `initial_state am [env] with
     <| outcomes := orc; requests := []; gas_obs := [] |> =
   initial_state am [env] with <| outcomes := orc; requests := [] |>` by
    simp[initial_state_def] >>
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[]
  >- (BasicProvers.EVERY_CASE_TAC >> gvs[])
  >> Cases_on `e` >> gvs[]
QED

(* ===== The body's run ===== *)

(* The guarded body's code from sa: the body's statements to sb, then (if
   the block is still open) the end, to st'. *)
Theorem guarded_body_code[local]:
  !cenv nkey ut iv fbody rt sa st'.
    compile_guarded_body cenv F nkey ut iv fbody rt sa = ((), st') ==>
    ?sb. compile_stmts cenv NoLoop
           (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa =
           ((), sb) /\
         cs_extends sa sb /\ cs_extends sb st'
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
       comp_get_def, comp_return_def] >>
  Cases_on `compile_stmts cenv NoLoop
              (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  rename1 `_ = (u, sb)` >> Cases_on `u` >> simp[] >>
  `cs_extends sa sb` by
    (qspecl_then [`cenv`, `NoLoop`,
                  `case rt of SOME t => t | NONE => BaseT BoolT`, `fbody`]
       mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  rw[] >>
  gvs[comp_return_def, comp_ignore_bind_def, comp_bind_def,
      cs_extends_refl] >>
  Cases_on `rt` >> gvs[] >>
  drule (SIMP_RULE std_ss [cs_appends_def] (cj 1 cs_appends_emit_helpers)) >>
  simp[]
QED

(* The body's code at the typing's return type: body_stmts_sim compiles at
   the return type the typing checks the body against, while
   compile_guarded_body compiles a function without a return type at
   BaseT BoolT. *)
Theorem guarded_body_stmts_env[local]:
  !tops bindings ctx cx cenv fbody ret rt env_t env' sa sb.
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env_t ret fbody = SOME env' /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa = ((), sb) ==>
    ?cenv'. stmts_env cenv NoLoop ret fbody sa = (cenv', sb)
Proof
  rpt strip_tac >> qpat_x_assum `rt = _` SUBST_ALL_TAC >>
  `stmts_env cenv NoLoop ret fbody sa =
   stmts_env cenv NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        SOME t => t | NONE => BaseT BoolT) fbody sa` by
    (Cases_on `ret = NoneT` >> gvs[] >>
     drule type_stmts_none_valued_return >> strip_tac >>
     drule_all stmts_env_ret_ty >>
     disch_then (qspecl_then [`NoLoop`, `NoneT`, `BaseT BoolT`]
                   SUBST1_TAC) >> simp[]) >>
  gvs[compile_stmts_env] >>
  Cases_on `stmts_env cenv NoLoop
              (case (if ret = NoneT then NONE else SOME ret) of
                 SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  gvs[]
QED

(* A body outcome other than a return exits as external_call_result_rel
   asks of the call's failure, given that a RevertData exit reverts. *)
Theorem expr_exit_external_result[local]:
  !e r tops ret tx am rqs.
    expr_exit (INR e : unit + exception) r /\
    (!d a t. e = Error (RevertData d) /\ r = Abort a t ==> a = Revert_abort) ==>
    external_call_result_rel tops ret tx (INR e, am, rqs) r
Proof
  rpt strip_tac >>
  Cases_on `r` >> gvs[expr_exit_def] >>
  Cases_on `e` >> gvs[expr_exit_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  gvs[external_call_result_rel_def]
QED

(* ===== S1 ===== *)

(* S1 when the value moves and the body starts. *)
Theorem lower_vyper_runtime_unit_body[local]:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  drule_all external_entry_reaches_body >> strip_tac >>
  drule_all external_body_frame >> strip_tac >>
  drule_all external_frame_ret_ok >>
  disch_then (qspec_then `func` assume_tac) >>
  Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx
                          NONE) fbody es0` >> rename1 `_ = (res, es')` >>
  drule_all external_body_source_ok >> strip_tac >>
  drule_all call_external_selected_body >>
  disch_then (qspec_then `SOME vs.vs_outcomes` assume_tac) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `rt = if ret = NoneT then NONE else SOME ret` by
    gvs[package_external_fn_def, set_external_package_target_def] >>
  drule guarded_body_code >> strip_tac >>
  drule_all guarded_body_stmts_env >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frame_ret_ok _ _ _ RetQ _ _` >>
  `stmt_frag unit.cu_context func cx NoLoop RetQ cenv
     (stmts_env cenv NoLoop ret fbody) es0 res es'` by
    (qspecl_then [`tops`, `bindings`, `unit.cu_context`, `func`, `cenv`,
                  `cx`, `env_t`, `env'`, `ret`, `NoLoop`, `RetQ`, `fbody`,
                  `es0`, `res`, `es'`] mp_tac body_stmts_sim >>
     asm_rewrite_tac[]) >>
  `fn_has_code sa sb func /\ fn_has_code sb st' func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  impl_tac >- gvs[ret_pc_ok_def] >>
  drule_all call_external_body_run >>
  disch_then (qspecl_then [`type_env tops`, `ret`]
                strip_assume_tac) >>
  simp[source_unit_execution_correct_def] >> strip_tac
  >- ((* the body falls off its end *)
      `res = INL ()` by gvs[stmt_lands_def] >> gvs[] >>
      `state_rel func cenv' cx es' s` by fs[stmt_state_rel_def] >>
      qspecl_then [`unit.cu_context`, `cenv`, `cenv'`, `nkey`, `ut'`, `iv`,
                   `fbody`, `sa`, `()`, `st'`, `sb`, `func`, `cx`, `es'`,
                   `tops`, `tx`, `am.sources`, `am.exports`, `am.layouts`,
                   `\s:venom_state. F`] mp_tac
        external_fallthrough_result_rel_any >>
      impl_tac >- gvs[Abbr`cx`, initial_evaluation_context_def] >>
      simp[frag_exec_def] >>
      disch_then (qspecl_then [`func`, `s`] mp_tac) >>
      impl_tac >- gvs[stmt_lands_def] >> simp[] >> strip_tac >>
      `!e. run_from fuel unit.cu_context func s <> Error e` by
        (gen_tac >> irule exit_result_not_error >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' _ _ s0 = _`
        (qspec_then `fuel` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (qx_choose_then `fuel1` assume_tac) >>
      qpat_x_assum `!fuel. _ ==> ?fuel'. run_context _ _ _ = _`
        (qspec_then `fuel1` mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choose_then `fuel2`
                    (fn th => qexists_tac `fuel2` >> SUBST1_TAC th)) >>
      gvs[Abbr`cx`, initial_evaluation_context_def]) >>
  (* the body exits *)
  `!e. run_from fuel unit.cu_context func s0 <> Error e` by
    (gen_tac >> irule exit_result_not_error >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_context _ _ _ = _`
    (qspecl_then [`fuel`, `run_from fuel unit.cu_context func s0`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `fuel2`
                (fn th => qexists_tac `fuel2` >> SUBST1_TAC th)) >>
  qpat_x_assum `stmt_exit _ _ _ _` mp_tac >> simp[stmt_exit_def] >>
  strip_tac
  >- ((* an error or an assertion *)
      Cases_on `res` >> gvs[] >> rename1 `expr_exit (INR e) _` >>
      `!v. e <> ReturnException v` by
        (rpt strip_tac >> gvs[expr_exit_def] >>
         Cases_on `run_from fuel unit.cu_context func s0` >>
         gvs[expr_exit_def]) >>
      gvs[] >>
      qspecl_then [`e`, `run_from fuel unit.cu_context func s0`, `tops`,
                   `ret`, `tx`, `am`, `es'.requests`] mp_tac
        expr_exit_external_result >>
      impl_tac
      >- (conj_tac >- first_assum ACCEPT_TAC >>
          rpt strip_tac >> gvs[] >>
          qspecl_then [`tops`, `bindings`, `unit.cu_context`, `func`, `cenv`,
                       `cx`, `env_t`, `env'`, `ret`, `RetQ`, `fbody`, `es0`,
                       `d`, `es'`, `sa`, `sb`, `cenv'`, `s0`, `fuel`, `a`, `t`]
            mp_tac external_body_revert_data_reverts >>
          impl_tac >- gvs[ret_pc_ok_def] >> simp[]) >>
      simp[]) >>
  (* a return *)
  gvs[Abbr`RetQ`, abstract_machine_from_state_def]
QED

(* S1, the lowering of an external call the source selects: the call's
   result and the lowered unit's run are related by
   external_call_result_rel. *)
Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     LENGTH tx.args = LENGTH args /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am [env] with
                 <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >> irule lower_vyper_runtime_unit_body >> metis_tac[]) >>
  irule external_entry_value_revert >> metis_tac[]
QED
