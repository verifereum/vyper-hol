(* Outcome suffixes follow the active frame through explicit calls and returns. *)
Theory guardedFrameOutcomes
Ancestors
  guardedFrameReachable calleeTransport venomExecProofs opcodeClass
  venomExecSemantics venomCallOracleDefs venomState venomInst
  contextCodegenRel extCallOracle rich_list list arithmetic
  oracleExecProps

Theorem pack_dret_dynamic_outcomes:
  !pairs cursor s ptrs final_cursor t.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) ==>
    t.vs_outcomes = s.vs_outcomes
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once pack_dret_dynamic_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem enters_block_outcomes:
  enters_block fn s t ==> t.vs_outcomes = s.vs_outcomes
Proof
  rw[enters_block_def] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\st. st.vs_outcomes`) >> simp[]
QED

(* take_outcome_rest covers computed precompiles and unsuccessful outcomes
   as well as ordinary external calls; none can replenish the list. *)
val external_outcomes_tac =
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  qpat_assum `inst.inst_opcode = _`
    (fn eq => PURE_ONCE_REWRITE_TAC
      [SIMP_RULE (srw_ss()) [eq]
        (Q.SPECL [`inst`, `s`] step_inst_base_def)]) >>
  strip_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
      consume_call_outcome_eq, consume_create_outcome_eq,
      take_outcome_rest, AllCaseEqs(), update_var_def] >>
  simp[IS_SUFFIX_EQ_DROP'] >> qexists_tac `1` >> simp[];

Theorem step_inst_non_invoke_outcomes:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  IS_SUFFIX s.vs_outcomes t.vs_outcomes
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (`step_inst_base inst s = OK t` by metis_tac[step_inst_non_invoke] >>
      qpat_x_assum `step_inst fuel ctx inst s = OK t` kall_tac >>
      Cases_on `inst.inst_opcode` >> gvs[MEM]
      >- external_outcomes_tac
      >- external_outcomes_tac
      >- external_outcomes_tac
      >- external_outcomes_tac
      >> external_outcomes_tac) >>
  fs[MEM] >> drule_all step_inst_noninvoke_oracle >> simp[]
QED

Theorem step_inst_IntRet_outcomes:
  step_inst fuel ctx inst s = IntRet ret t ==>
  t.vs_outcomes = s.vs_outcomes
Proof
  simp[Once step_inst_def] >> IF_CASES_TAC
  >- simp[AllCaseEqs()] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_outcomes >> simp[]
QED

Theorem guarded_frame_outcomes:
  !vs ctx stk PG G tn fn inst s K.
    LENGTH vs.vs_outcomes <= K /\
    guarded_frame_reachable vs ctx stk PG G tn fn inst s ==>
    ?j. j <= K /\
        LENGTH vs.vs_outcomes = j + LENGTH s.vs_outcomes /\
        s.vs_outcomes = DROP j vs.vs_outcomes
Proof
  qsuff_tac
    `!vs ctx stk PG G tn fn inst s.
       guarded_frame_reachable vs ctx stk PG G tn fn inst s ==>
       IS_SUFFIX vs.vs_outcomes s.vs_outcomes`
  >- (rpt strip_tac >> res_tac >> fs[IS_SUFFIX_APPEND] >>
      rename1 `vs.vs_outcomes = prefix ++ s.vs_outcomes` >>
      gvs[DROP_LENGTH_APPEND] >> decide_tac) >>
  ho_match_mp_tac guarded_frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule enters_block_outcomes >> simp[])
  >- (rpt strip_tac >> drule_all step_inst_non_invoke_outcomes >>
      simp[] >> metis_tac[IS_SUFFIX_TRANS])
  >- (rpt strip_tac >>
      `inst.inst_opcode <> INVOKE` by
        metis_tac[is_terminator_not_invoke] >>
      drule_all step_inst_non_invoke_outcomes >>
      drule enters_block_outcomes >> simp[] >>
      metis_tac[IS_SUFFIX_TRANS])
  >- (rpt strip_tac >> drule setup_callee_oracle >>
      drule enters_block_outcomes >> simp[]) >>
  rpt strip_tac >> drule step_inst_IntRet_outcomes >>
  drule bind_outputs_oracle >> simp[] >> metis_tac[]
QED
