(* Value rejection on the real selected-default dispatch path. *)
Theory groupedDefaultValueRejection
Ancestors
  groupedDispatchPath groupedEntryResources groupedEntryExit entryValueRejectFacts
  selectedAcceptedFold fragGasOriginPtr fragGasOriginPtrLoop compileEnv moduleLowering
  vyperABIEntries vyperLoweringCorrect loweringStateRelDefs e2eDefs entryDispatchPtr
  sourceUnitExecution vyperCall vyperState vyperInterpreter gasSummary
  venomState venomInst ptrDiscipline finite_map words list arithmetic

(* Retain the concrete check cursor before projecting ordinary correctness. *)
val _ = Parse.hide "body";
val (check_inputs, legacy_result) = dest_imp (concl (Q.INST
  [`defaults` |-> `dflts`, `body` |-> `fbody`]
  (SPEC_ALL grouped_entry_value_rejected)));
val reject_result = ``reject_result:bool``;
val selected_parameters = ["tops","am","tx","mut","nr","args","dflts","ret","fbody",
                           "unit","vs","shadow_ctx","reject_result"];
fun check_handler result =
  let val body = ``^check_inputs ==> ^result`` in
    list_mk_forall
      (filter (fn v => not (mem (fst (dest_var v)) selected_parameters))
        (free_vars body), body)
  end;
val reject_handler = check_handler reject_result;
val legacy_handler = check_handler legacy_result;

val selected_reject_inputs = ``
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  MEM (prefix,k) (abi_entries args dflts) /\ LENGTH tx.args = LENGTH prefix /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\ lookup_block "__entry" fn.fn_blocks = SOME bb /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  gas_shadow_function fn shadow_fn /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  fn_has_code sf sd fn /\ EVERY group_entry_labels_ok groups /\
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  EVERY (\group. case group of
    ExternalSingle (sel,lbl,tz) pkg =>
      calldata_method_id vs.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults comp ens sp _ =>
      FIND (\(sel,_,_,_). calldata_method_id vs.vs_call_ctx.cc_calldata = n2w sel)
        ens = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
  FIND (\(n,_,_,_). calldata_method_id vs.vs_call_ctx.cc_calldata = n2w n) entries =
    SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  common.ec_payable = (mut = Payable) /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INR e,ev)``;

Theorem grouped_selected_default_value_rejection_cases:
  ^reject_handler ==> ^selected_reject_inputs ==> ^reject_result
Proof
  disch_then (mk_asm "on_check") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>` by simp[Abbr `s`] >>
  `s.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  `4 <= LENGTH s.vs_call_ctx.cc_calldata` by
    (qpat_assum `s.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all (Q.INST [`st` |-> `sf`] (SPEC_ALL grouped_dispatch_initial_resources)) >>
  disch_then (qspec_then `ARB:instruction` (map_every assume_tac o CONJUNCTS)) >>
  drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
    (qx_choosel_then [`mid`,`prelude`,`disp`,`br`,`u`,`Gu`,`tnu`]
      (map_every assume_tac o CONJUNCTS))) >>
  `eval_operand (Var mid) u = SOME (calldata_method_id vs.vs_call_ctx.cc_calldata)` by
    (qpat_assum `eval_operand _ _ = _` mp_tac >> simp[]) >>
  qpat_x_assum `groups = _` SUBST_ALL_TAC >>
  drule_all (Q.INST [`PG` |-> `[]`]
    (SPEC_ALL compile_external_groups_selected_default_origin_with_frame)) >>
  disch_then (qspec_then `Gu`
    (qx_choosel_then [`vars`,`checks`,`init`,`last`,`hit`,`Gh`,`tnh`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "reject"
QED

Resume grouped_selected_default_value_rejection_cases[reject]:
  `value_transfer_ok tx am.accounts` by
    (qpat_assum `initial_venom_state_rel _ _ _ _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [initial_venom_state_rel_def])) >>
  drule_all send_call_value_rejects_only_nonpayable >> strip_tac >>
  drule_all entry_value_reject_callvalue >> strip_tac >>
  `hit.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame u _ hit _`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `selected_registration_frame s _ u _`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     simp[]) >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts` by
    (qpat_assum `LENGTH tx.args = LENGTH prefix` mp_tac >>
     qpat_assum `MEM (prefix,k) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_entries_member, LENGTH_TAKE_EQ] >> decide_tac) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK hit,Gh,tnh)` by
    (rpt gen_tac >>
     qpat_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` (fn th => pure_rewrite_tac [SYM th]) >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tnu`] >>
     asm_rewrite_tac[]) >>
  `compile_entry_checks mincd F checks = ((),init)` by
    (qpat_assum `compile_entry_checks mincd common.ec_payable checks = _` mp_tac >>
     qpat_assum `common.ec_payable = _` (fn th => pure_rewrite_tac [th]) >>
     asm_rewrite_tac[]) >>
  `~block_is_terminated checks` by
    (rewrite_tac [block_is_terminated_def] >> asm_rewrite_tac[list_case_def]) >>
  `fresh_vars_wrt checks hit /\ ~hit.vs_halted /\ hit.vs_current_bb = checks.cs_current_bb /\
   hit.vs_inst_idx = 0 /\ allocas_from 0 hit` by
    (qpat_assum `selected_registration_resources _ _ _ _ checks hit`
       (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) []) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit` by
    (qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp hit /\ _` mp_tac >>
     DISCH_THEN (fn th => disch_then (ACCEPT_TAC o CONJUNCT1 o MATCH_MP th))) >>
  `hit.vs_call_ctx.cc_callvalue <> 0w` by
    (qpat_assum `hit.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `!name bb. lookup_block name _ = SOME bb ==> _` (drule_then ACCEPT_TAC)) >>
  qpat_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` (fn eq =>
    asm "on_check" (drule_all o PURE_REWRITE_RULE [eq])) >>
  disch_then ACCEPT_TAC
QED

Finalise grouped_selected_default_value_rejection_cases

Theorem grouped_default_legacy_rejection_handler[local]:
  ^legacy_handler
Proof
  rpt gen_tac >> disch_then (ACCEPT_TAC o MATCH_MP grouped_entry_value_rejected)
QED

Theorem grouped_selected_default_value_rejection:
  ^selected_reject_inputs ==> ^legacy_result
Proof
  ACCEPT_TAC (MATCH_MP grouped_selected_default_value_rejection_cases
    grouped_default_legacy_rejection_handler)
QED
