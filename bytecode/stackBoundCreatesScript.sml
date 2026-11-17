(* CREATE and CREATE2 preserve the checked caller's promised continuation. *)
Theory stackBoundCreates
Ancestors
  stackBoundInterface stackBoundDefs vfmExecution vfmExecutionProp
  vfmContext vfmState vfmOperation vfmConstants vfmStepLength
  list rich_list pair option finite_map words

Theorem sb_create_finish_view[local]:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  (if abort then abort_unuse gas else do
     access_address address; ensure_storage_in_domain address;
     if collision then abort_create_exists sender
     else proceed_create sender address value code gas
   od) s = (r,t) ==>
  r <> INR (SOME StackOverflow) /\
  (r = INL () ==>
    ((?p. t.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
          p.jumpDest = c.jumpDest /\ p.pc = c.pc + 1 /\
          p.stack = 0w::c.stack) \/
     (?child crb. t.contexts = (child,crb)::(c,rb)::rest)))
Proof
  strip_tac >> Cases_on `abort`
  >- (gvs[abort_unuse_def, unuse_gas_def, push_stack_def, inc_pc_def,
          get_current_context_def, set_current_context_def, bind_def,
          ignore_bind_def, return_def, assert_def, fail_def,
          AllCaseEqs()] >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[access_address_def, ensure_storage_in_domain_def,
       domain_check_def, set_domain_def, bind_def, ignore_bind_def,
       return_def, assert_def, fail_def] >>
  Cases_on `s.msdomain` >> simp[] >>
  Cases_on `collision` >>
  simp[abort_create_exists_def, proceed_create_def, update_accounts_def,
       get_rollback_def, get_original_def, set_original_def, push_context_def,
       push_stack_def, inc_pc_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> simp[]
QED

Theorem sb_create_raw_view[local]:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack <= stack_limit /\
  step_create two s = (r,t) ==>
  r <> INR (SOME StackOverflow) /\
  (r = INL () ==>
    (if two then 4 else 3) <= LENGTH c.stack /\
    ((?p. t.contexts = (p,rb)::rest /\
          p.msgParams = c.msgParams /\ p.jumpDest = c.jumpDest /\
          p.pc = c.pc + 1 /\
          p.stack = 0w::DROP (if two then 4 else 3) c.stack) \/
     (?child crb p. t.contexts = (child,crb)::(p,rb)::rest /\
          p.msgParams = c.msgParams /\ p.jumpDest = c.jumpDest /\
          p.pc = c.pc /\
          p.stack = DROP (if two then 4 else 3) c.stack)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_create _ _ = _` mp_tac >>
  simp[step_create_def, pop_stack_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       return_def, assert_def, fail_def] >>
  Cases_on `(if two then 4 else 3) <= LENGTH c.stack` >> simp[] >>
  simp[memory_expansion_info_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas charge _` >>
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, fail_def, return_def] >>
  qmatch_goalsub_abbrev_tac `if paid then _ else _` >>
  Cases_on `paid` >> simp[] >>
  simp[expand_memory_def, read_memory_def, get_callee_def, get_accounts_def,
       get_gas_left_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `if size_ok then _ else _` >>
  Cases_on `size_ok` >> simp[] >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `if paid2 then _ else _` >>
  Cases_on `paid2` >> simp[] >>
  Cases_on `c.msgParams.static` >> simp[] >>
  qmatch_goalsub_abbrev_tac `(if abort then _ else _) prepared = _` >>
  `LENGTH (DROP (if two then 4 else 3) c.stack) < stack_limit` by
    (Cases_on `two` >> simp[] >> gvs[]) >>
  strip_tac >>
  drule_at (Pat `(if _ then _ else _) _ = _`)
    (SRULE [ignore_bind_def] sb_create_finish_view) >>
  simp[Abbr `prepared`] >>
  (impl_tac >- gvs[]) >>
  strip_tac >> gvs[] >> strip_tac >> gvs[] >> simp[]
QED
Theorem sb_create_inner[local]:
  sb_inner (if two then Create2 else Create) s = step_create two s
Proof
  Cases_on `step_create two s` >> Cases_on `q` >>
  Cases_on `two` >>
  gvs[sb_inner_def, step_inst_def, inc_pc_or_jump_def, is_call_def,
      bind_def, return_def]
QED

Theorem sb_create_contracts:
  sb_opcode_contract Create /\ sb_opcode_contract Create2
Proof
  `(!two. sb_opcode_contract (if two then Create2 else Create))`
    suffices_by metis_tac[] >>
  gen_tac >> simp[sb_opcode_contract_def] >>
  map_every qx_gen_tac [`s`,`a`] >> strip_tac >>
  Cases_on `s.contexts` >- gvs[] >> PairCases_on `h` >>
  rename1 `s.contexts = (c,rb)::rest` >>
  `LENGTH c.stack <= stack_limit /\
   c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code` by
    gvs[wf_state_def, wf_context_def] >>
  `bytecode_stack_describes a c.stack /\ c.jumpDest = NONE` by gvs[] >>
  `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc =
     SOME (if two then Create2 else Create)` by
    (Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
     Cases_on `two` >> gvs[sb_decoded_def] >>
     Cases_on `LENGTH c.msgParams.code <= c.pc` >> gvs[]) >>
  `LENGTH a = LENGTH c.stack` by metis_tac[bytecode_stack_describes_length] >>
  conj_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      `step_create two s = (INR (SOME StackOverflow),t)` by
        (Cases_on `two` >> gvs[step_inst_def]) >>
      drule_all sb_create_raw_view >> simp[]) >>
  map_every qx_gen_tac [`r`,`t`] >>
  simp[sb_create_inner] >> strip_tac >>
  `r = INL ()` by
    (Cases_on `r` >> gvs[] >>
     drule_at (Pat `step_create _ _ = _`) step_create_inr_no_grow >>
     simp[] >> gvs[]) >>
  drule_all sb_create_raw_view >> strip_tac >> gvs[] >>
  qexists_tac `(c.pc + 1, NONE::DROP (if two then 4 else 3) a)` >>
  Cases_on `two` >>
  gvs[sb_successors_def, bytecode_stack_successors_def, bytecode_stack_io_def,
      opcode_def, sb_at_def, bytecode_stack_describes_def, LIST_REL_DROP]
  >>> NTH_GOAL (simp[rich_listTheory.REPLICATE_compute]) 1
  >>> NTH_GOAL (simp[rich_listTheory.REPLICATE_compute]) 1
  >>> NTH_GOAL (simp[rich_listTheory.REPLICATE_compute]) 1
  >>> NTH_GOAL (simp[rich_listTheory.REPLICATE_compute]) 1
  >>> NTH_GOAL (simp[rich_listTheory.REPLICATE_compute]) 1
  >> (simp[rich_listTheory.REPLICATE_compute])
QED
