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
  e2eDefs supportedProgram vyperLoweringCorrect entryChecksProps moduleLoweringProps
  entryDispatchProps supportedNames abiDecoderCounters context
  supportedDecls supportedExprForms supportedStmts
  vyperTypeSelectedEntrySoundness vyperTypeSystem
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

Theorem supported_entry_no_getters[local]:
  supported_program tops ==>
  (!mut ty x name. ~MEM (VariableDecl Public mut name ty x) tops) /\
  (!b kt vt x name. ~MEM (HashMapDecl Public b name kt vt x) tops)
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e tops ==> supported_declaration_header tops e`
    drule >> simp[supported_declaration_header_def]
QED

Theorem selected_external_dispatch[local]:
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) ==>
  (?rr. MEM (mut, F, rr, tx.function_name, args, [], ret, fbody)
          (FST (classify_functions tops))) /\
  (!fb. linear_dispatch_target cd
    (MAP (\(sel, lbl, _). (sel, lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ tx.function_name)
Proof
  strip_tac >>
  drule supported_entry_no_getters >> strip_tac >>
  gvs[valid_vyper_call_def] >> conj_tac
  >- (irule lookup_function_external_mem >> simp[] >>
      qexists_tac `NONE` >> simp[]) >>
  gen_tac >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
     (FST (classify_functions tops))))` by
    gvs[supported_program_def, supported_declaration_names_def,
        supported_selectors_distinct_def] >>
  drule linear_dispatch_selects_function >> simp[] >>
  disch_then (qspec_then `tx.args` mp_tac) >> simp[]
QED

Theorem compile_decode_args_vars_mono[local]:
  !args cenv offset opc hi base.
    abi_decoder_vars_mono (compile_decode_args cenv args offset opc hi base)
Proof
  Induct >> simp[compile_decode_args_def, abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1`
  >- (simp[compile_decode_args_def, LET_THM] >>
      ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >>
      gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >>
      gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_abi_clamp] >>
      ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP cenv.ce_vars h0` >>
          simp[abi_decoder_vars_mono_return] >>
          Cases_on `var_location_decode_operand x` >>
          simp[abi_decoder_vars_mono_return, abi_decoder_vars_mono_prims]) >>
      simp[]) >>
  Cases_on `h2` >> simp[compile_decode_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[]
  >- (ntac 3 (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
              >- simp[abi_decoder_vars_mono_prims] >> gen_tac) >>
      ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
      simp[abi_decoder_vars_mono_mutual]) >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_prims] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
  simp[abi_decoder_vars_mono_mutual]
QED

Theorem compile_register_positional_args_vars_mono[local]:
  !args cenv offset.
    abi_decoder_vars_mono (compile_register_positional_args cenv args offset)
Proof
  Induct >> simp[compile_register_positional_args_def,
                 abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_abi_alloc_buffer] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_return] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
  simp[compile_decode_args_vars_mono]
QED

Theorem compile_register_positional_args_next_var[local]:
  compile_register_positional_args cenv args offset sa = (ce, sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`args`, `cenv`, `offset`]
    compile_register_positional_args_vars_mono) >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem compile_stmts_vars_mono[local]:
  abi_decoder_vars_mono (compile_stmts ce lc ty ss)
Proof
  mp_tac compile_stmt_cs_mono >>
  simp[cs_mono_def, abi_decoder_vars_mono_def] >>
  rpt strip_tac >>
  Cases_on `compile_stmts ce lc ty ss st` >>
  rename1 `_ = (u, sb)` >> Cases_on `u` >>
  first_x_assum drule >> simp[]
QED

Theorem compile_entry_checks_vars_mono[local]:
  abi_decoder_vars_mono (compile_entry_checks min_cds payable)
Proof
  Cases_on `payable` >> Cases_on `min_cds > 4` >>
  simp[compile_entry_checks_def, abi_decoder_vars_mono_return] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac])
QED

Theorem compile_nonreentrant_vars_mono[local]:
  abi_decoder_vars_mono (compile_nonreentrant_lock key transient view) /\
  abi_decoder_vars_mono (compile_nonreentrant_unlock key transient view)
Proof
  Cases_on `transient` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def,
    abi_decoder_vars_mono_prims, abi_decoder_vars_mono_return] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac])
QED

Theorem comp_get_vars_mono[local]:
  abi_decoder_vars_mono comp_get
Proof
  simp[abi_decoder_vars_mono_def, comp_get_def]
QED

Theorem compile_guarded_body_vars_mono[local]:
  abi_decoder_vars_mono (compile_guarded_body ce nr key transient view body rt)
Proof
  Cases_on `nr` >> Cases_on `rt` >>
  simp[compile_guarded_body_def] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return, compile_nonreentrant_vars_mono,
      compile_stmts_vars_mono, comp_get_vars_mono]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac,
    (IF_CASES_TAC >> simp[])])
QED

Theorem compile_external_function_body_vars_mono[local]:
  abi_decoder_vars_mono
    (compile_external_function_body ce args nr key transient view body rt)
Proof
  rewrite_tac[compile_external_function_body_def] >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >>
  simp[compile_register_positional_args_vars_mono,
       compile_guarded_body_vars_mono]
QED

Theorem compile_entry_checks_next_var[local]:
  compile_entry_checks min_cds payable sa = ((), sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac compile_entry_checks_vars_mono >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem compile_external_function_body_next_var[local]:
  compile_external_function_body ce args nr key transient view body rt sa =
    ((), sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac compile_external_function_body_vars_mono >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem external_checks_occurrence[local]:
  !packages lbl ce args min_cds pay nr key ut iv body rt sd sf.
    MEM (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt) packages /\
    compile_external_fn_bodies packages sd = ((),sf) ==>
    ?pre post sa st st' sb.
      packages = pre ++ (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt)::post /\
      compile_external_fn_bodies pre sd = ((),sa) /\
      new_block lbl sa = (sa.cs_current_bb,st) /\
      compile_entry_checks min_cds pay st = ((),st') /\
      compile_external_function_body ce args nr key ut iv body rt st' = ((),sb) /\
      compile_external_fn_bodies post sb = ((),sf) /\
      st.cs_current_bb = lbl /\ st.cs_current_insts = [] /\
      sd.cs_next_var <= st.cs_next_var
Proof
  Induct >> simp[MEM] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp_tac std_ss [compile_external_fn_bodies_def, comp_ignore_bind_def,
                   comp_bind_def] >>
  Cases_on `new_block h0 sd` >>
  rename1 `new_block h0 sd = (old,s1)` >> simp[] >>
  Cases_on `compile_entry_checks h3 h4 s1` >>
  rename1 `compile_entry_checks h3 h4 s1 = (u,s2)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `compile_external_function_body h1 h2 h5 h6 h7 h8 h9 h10 s2` >>
  rename1 `compile_external_function_body _ _ _ _ _ _ _ _ _ = (u,s3)` >>
  Cases_on `u` >> simp[] >> strip_tac
  >- (gvs[] >>
      qexistsl_tac [`[]`, `packages`, `sd`, `s1`, `s2`, `s3`] >>
      gvs[compile_external_fn_bodies_def, comp_return_def, new_block_def,
          LET_THM]) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  `sd.cs_next_var = s1.cs_next_var` by gvs[new_block_def, LET_THM] >>
  `s1.cs_next_var <= s2.cs_next_var` by
    (rev_drule compile_entry_checks_next_var >> simp[]) >>
  `s2.cs_next_var <= s3.cs_next_var` by
    (rev_drule compile_external_function_body_next_var >> simp[]) >>
  qexistsl_tac [`(h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10)::pre`,
                 `post`, `sa`, `st`, `st'`, `sb`] >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  decide_tac
QED

Theorem selected_external_package[local]:
  !tops target mut rr name args ret fbody.
  ?cenv pos_args min_cds is_payable nkey ut iv rt.
    set_external_package_target target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut, F, rr, name, args, ([] : expr list), ret, fbody)) =
    ("fn_" ++ name, cenv, pos_args, min_cds, is_payable, F,
     nkey, ut, iv, fbody, rt)
Proof
  rpt gen_tac >>
  simp[package_external_fn_def, set_external_package_target_def, LET_THM]
QED

(* ADMITTED (#639): the run from __entry reaches the start st of the entry
   checks of the function the source selects: run_context starts the entry
   function func at its first block, compile_selector_dispatch_linear_correct
   brings it to "fn_" ++ tx.function_name (linear_dispatch_selects_function,
   supported_program giving distinct selectors), and
   compile_external_fn_bodies opens that label's block with the entry
   checks.  Only variables and the position change
   on the way, and every result from s0 is a result of run_context. *)
Theorem linear_dispatch_prefix_code[local]:
  !selectors fallback sa sd se func.
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback, sa) /\
    compile_selector_dispatch_linear selectors fallback sa = ((), sd) /\
    cs_extends sd se /\ func.fn_blocks = all_blocks se ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
    (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l) /\
    fn_has_code sa sd func
Proof
  rpt gen_tac >> strip_tac >>
  `compile_state_ok (initial_compile_state "__entry")` by
    (irule compile_state_ok_initial >>
     simp[compiler_labels_future_def, fresh_label_output_def]) >>
  drule_all emitHelperPropsTheory.fresh_label_produces_external >> strip_tac >>
  `compile_state_ok sd` by
    (drule_all compile_selector_dispatch_linear_state_ok >> simp[]) >>
  conj_tac
  >- (irule loweringShapeRulesTheory.compile_state_ok_all_blocks_distinct >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      drule compile_selector_dispatch_linear_no_fn_labels >>
      disch_then irule >> simp[] >>
      simp[vyperCompilerTheory.initial_compile_state_def, bound_labels_def]) >>
  irule loweringShapeRulesTheory.cs_extends_fn_has_code >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem external_entry_reaches_checks:
  !tops rpolicy unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) ==>
    ?rr lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_entry_checks min_cds is_payable st = ((), st') /\
      fn_has_code st st' func /\
      vars_pc_only vs s0 /\ fresh_vars_wrt st s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = st.cs_current_bb /\
      s0.vs_inst_idx = LENGTH st.cs_current_insts /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
Proof
  cheat
QED

(* The source fails to move the call value only for a nonpayable function
   called with value: value_transfer_ok rules out a failed transfer. *)
Theorem send_call_value_fails[local]:
  !mut srcs layouts tx am env orc e es.
    value_transfer_ok tx am.accounts /\
    send_call_value mut (initial_evaluation_context srcs layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INR e, es) ==>
    mut <> Payable /\ tx.value <> 0
Proof
  rpt gen_tac >>
  simp[send_call_value_def, transfer_value_def, value_transfer_ok_def,
       initial_evaluation_context_def, initial_state_def] >>
  rw[] >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.assert_def,
      vyperStateTheory.check_def, get_accounts_def, update_accounts_def,
      AllCaseEqs()]
QED

(* A nonpayable function called with value: the entry checks of the
   function the source selects revert (entry_checks_nonpayable_value), as
   external_call_result_rel asks of the source's RuntimeError. *)
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
  rpt strip_tac >>
  `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all send_call_value_fails >> strip_tac >>
  drule_all external_entry_reaches_checks >> strip_tac >>
  rename1 `compile_entry_checks _ _ sc = ((), sc')` >>
  `call_tx_well_typed tx` by fs[source_typing_ok_def] >>
  `s0.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_x_assum `vars_pc_only _ _` mp_tac >> simp[vars_pc_only_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `call_ctx_rel tx s0.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx` by
    fs[initial_venom_state_rel_def, venom_env_rel_def] >>
  `?c. package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody) =
       (lbl, c, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt)` by
    (qmatch_asmsub_abbrev_tac `set_external_package_target _ pkg = _` >>
     PairCases_on `pkg` >>
     gvs[set_external_package_target_def, markerTheory.Abbrev_def]) >>
  qspecl_then [`tops`, `am`, `tx`, `SOME vs.vs_outcomes`, `ret`, `F`,
               `assign_nkeys tops 0`, `mut`, `rr`, `args`, `[] : expr list`, `fbody`,
               `lbl`, `c`, `pos_args`, `min_cds`, `is_payable`,
               `(F, nkey, ut', iv, fbody, rt)`, `sc`, `sc'`,
               `unit.cu_context`, `s0`, `vs.vs_tx_ctx`, `vs.vs_block_ctx`]
    mp_tac (Q.INST [`gobs` |-> `[]`] entry_checks_nonpayable_value) >>
  impl_tac >- simp[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  simp[source_unit_execution_correct_def] >>
  first_x_assum (qspecl_then [`fuel`, `Abort Revert_abort t`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `fuel'` >> gvs[]
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

Theorem supported_variable_decl_var_type[local]:
  !tops name vis mut ty slot.
    supported_variable_decl tops (NONE, name) = SOME (vis, mut, ty, slot) ==>
    build_var_type_map tops (NONE, name) = SOME ty
Proof
  Induct >> simp[supported_variable_decl_def, build_var_type_map_def] >>
  Cases >> rw[supported_variable_decl_def, build_var_type_map_def]
QED

Theorem body_inv_dynarrays_typed[local]:
  !tops ctx cenv cx id.
    body_inv tops ctx cenv cx /\ supported_storage_dynamic_array tops id ==>
    ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)
Proof
  cheat
QED

Theorem declare_local_module_var_type[local]:
  !cenv id ty st c st'.
    declare_local cenv id ty st = (c, st') ==>
    c.ce_module_var_type = cenv.ce_module_var_type
Proof
  cheat
QED

Theorem declare_stmt_local_module_var_type[local]:
  !cenv s st c st'.
    declare_stmt_local cenv s st = (c, st') ==>
    c.ce_module_var_type = cenv.ce_module_var_type
Proof
  cheat
QED

val ret_ty_simple_tac =
  rpt strip_tac >> ONCE_REWRITE_TAC [compile_stmt_def] >>
  gvs[supported_stmt_def, stmt_valued_return_def];

val ret_ty_loop_tac =
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  ONCE_REWRITE_TAC [compile_stmt_def] >>
  gvs[supported_stmt_def, stmt_valued_return_def] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[] >>
       imp_res_tac declare_local_module_var_type >>
       gvs[]);

val ret_ty_cons_tac =
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  ONCE_REWRITE_TAC [compile_stmt_def] >>
  gvs[supported_stmt_def, stmt_valued_return_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[] >>
       imp_res_tac declare_stmt_local_module_var_type >>
       gvs[]);

(* compile_stmt reads the return type only to compile a valued return and
   as the element type of an Append whose target root has no array type; a
   supported Append targets a storage dynamic array, which
   has an array type in the compile env, and no declaration changes module types. *)
Theorem compile_stmt_ret_ty[local]:
  (!cenv lctx ty s.
     (!id. supported_storage_dynamic_array tops id ==>
          ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)) /\
     supported_stmt tops bindings s /\
     ~stmt_valued_return s ==>
     compile_stmt cenv lctx ty s = compile_stmt cenv lctx ty' s) /\
  (!cenv lctx ty ss.
     (!id. supported_storage_dynamic_array tops id ==>
          ?t b. cenv.ce_module_var_type id = SOME (ArrayT t b)) /\
     supported_stmts tops bindings ss /\
     ~stmts_valued_return ss ==>
     compile_stmts cenv lctx ty ss = compile_stmts cenv lctx ty' ss)
Proof
  cheat
QED

(* A supported body without a valued return compiles the same at every
   return type. *)
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
