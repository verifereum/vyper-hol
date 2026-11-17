(* Terminating raw instructions never push a result.  Resumption of a
   suspended caller belongs to the handle_step proof, not this theory. *)
Theory stackBoundTerminal
Ancestors
  stackBoundInterface vfmSameFrame vfmExecution
  list pair option
Libs
  BasicProvers

Theorem sb_terminal_return_result[local]:
  !b s. FST (step_return b s) <> INL () /\
        FST (step_return b s) <> INR (SOME StackOverflow)
Proof
  rpt gen_tac >>
  simp[step_return_def, pop_stack_def, memory_expansion_info_def,
       consume_gas_def, expand_memory_def, read_memory_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, fail_def, assert_def,
       finish_def, revert_def] >>
  rpt (TOP_CASE_TAC >> gvs[finish_def, revert_def, AllCaseEqs()])
QED

Theorem sb_terminal_self_destruct_result[local]:
  !s. FST (step_self_destruct s) <> INL () /\
      FST (step_self_destruct s) <> INR (SOME StackOverflow)
Proof
  gen_tac >>
  simp[step_self_destruct_def, pop_stack_def, access_address_def,
       domain_check_def, set_domain_def, get_callee_def, set_return_data_def,
       get_accounts_def, consume_gas_def, assert_not_static_def, get_static_def,
       update_accounts_def, get_original_def, add_to_delete_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, fail_def, assert_def, finish_def] >>
  rpt (TOP_CASE_TAC >> gvs[finish_def, AllCaseEqs()]) >>
  gvs[COND_RATOR, update_accounts_def, add_to_delete_def, return_def,
      bind_def, AllCaseEqs()]
QED

Theorem sb_terminal_result[local]:
  !op s. MEM op [Stop; Return; Revert; Invalid; SelfDestruct] ==>
    FST (step_inst op s) <> INL () /\
    FST (step_inst op s) <> INR (SOME StackOverflow)
Proof
  rpt gen_tac >> simp[MEM] >> strip_tac >> gvs[]
  >- (simp[step_inst_def, set_return_data_def, get_current_context_def,
           set_current_context_def, bind_def, ignore_bind_def, return_def,
           fail_def, finish_def] >>
      rpt (TOP_CASE_TAC >> gvs[AllCaseEqs()]))
  >- simp[step_inst_def, sb_terminal_return_result]
  >- simp[step_inst_def, sb_terminal_return_result]
  >- simp[step_inst_def, fail_def]
  >> simp[step_inst_def, sb_terminal_self_destruct_result]
QED

(* The contract does not require a successful parsed lookup.  Thus it also
   covers sb_decoded's NONE fallback, which selects Stop or Invalid. *)
Theorem sb_terminal_contracts:
  !op. MEM op [Stop; Return; Revert; Invalid; SelfDestruct] ==>
       sb_opcode_contract op
Proof
  rpt strip_tac >>
  `preserves_same_frame (step_inst op)` by
    (gvs[MEM] >> simp[]) >>
  simp[sb_opcode_contract_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (strip_tac >> gen_tac >>
      drule sb_terminal_result >> disch_then (qspec_then `s` mp_tac) >>
      metis_tac[FST]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `sb_inner _ _ = _` mp_tac >>
  simp[sb_inner_def, bind_def] >>
  Cases_on `step_inst op s` >> rename1 `step_inst op s = (res,u)` >>
  `res <> INL ()` by
    (drule sb_terminal_result >> disch_then (qspec_then `s` mp_tac) >> simp[]) >>
  Cases_on `res` >> gvs[] >> strip_tac >> gvs[] >>
  drule_at (Pat `m s = (r,t)`) psf_imp_length_contexts_preserved >> simp[]
QED
