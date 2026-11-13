Theory decoratedClearing
Ancestors
  decoratedExecution passSharedProps passSharedDefs venomExecSemantics
  venomExecProps venomInstProps venomInst venomState stateEquiv stateEquivProps list venomWf

(* A final instruction needs no recursive certificate. *)
Theorem decorated_block_finish:
  get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
  (is_terminator inst.inst_opcode \/ ~(?v. step_inst fuel ctx inst s = OK v)) /\
  ~(?e. exec_block fuel ctx bb s = Error e) ==>
  decorated_block Q fuel ctx bb s (exec_block fuel ctx bb s)
Proof
  strip_tac >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[Once exec_block_def] >> simp[Once exec_block_def]
  >>~- ([`decorated_block _ _ _ _ _ (if _ then _ else _)`],
      irule (cj 2 decorated_block_rules) >> metis_tac[])
  >>~- ([`decorated_block _ _ _ _ _ (Halt _)`],
      irule (cj 3 decorated_block_rules) >> metis_tac[])
  >>~- ([`decorated_block _ _ _ _ _ (Abort _ _)`],
      irule (cj 4 decorated_block_rules) >> metis_tac[])
  >> irule (cj 5 decorated_block_rules) >> metis_tac[]
QED

Theorem decorated_clear_finish:
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> NOP /\
  Q inst (s with vs_inst_idx := j) /\
  get_instruction (clear_nops_block bb) j = SOME inst /\
  (is_terminator inst.inst_opcode \/ ~(?v. step_inst fuel ctx inst s = OK v)) /\
  ~(?e. exec_block fuel ctx (clear_nops_block bb)
             (s with vs_inst_idx := j) = Error e) ==>
  decorated_block Q fuel ctx (clear_nops_block bb) (s with vs_inst_idx := j)
    (exec_block fuel ctx (clear_nops_block bb) (s with vs_inst_idx := j))
Proof
  strip_tac >>
  (irule decorated_block_finish >> conj_tac >- metis_tac[] >>
   qexists_tac `inst` >> simp[]) >>
  Cases_on `is_terminator inst.inst_opcode` >- simp[] >>
  drule step_inst_non_term_idx >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`, `j`] mp_tac) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  Cases_on `step_inst fuel ctx inst (s with vs_inst_idx := j)` >>
  gvs[result_equiv_def]
QED

Theorem decorated_clear_last:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  Q inst (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
    (TAKE s.vs_inst_idx bb.bb_instructions))) /\
  (is_terminator inst.inst_opcode \/ ~(?v. step_inst fuel ctx inst s = OK v)) /\
  ~(?e. exec_block fuel ctx bb s = Error e) ==>
  decorated_block Q fuel ctx (clear_nops_block bb)
    (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
      (TAKE s.vs_inst_idx bb.bb_instructions)))
    (exec_block fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
        (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  strip_tac >>
  `inst.inst_opcode <> NOP` by
    (strip_tac >> gvs[step_nop_identity, is_terminator_def]) >>
  (irule decorated_clear_finish >> reverse conj_tac
   >- (qexists_tac `inst` >> simp[] >>
       gvs[get_instruction_def, clear_nops_block_def] >>
       conj_tac >- (irule filter_take_lt >> simp[]) >>
       irule filter_take_el >> simp[])) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] clear_nops_block_gen) >>
  Cases_on `exec_block fuel ctx bb s` >>
  Cases_on `exec_block fuel ctx (clear_nops_block bb)
    (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
      (TAKE s.vs_inst_idx bb.bb_instructions)))` >>
  gvs[result_equiv_def]
QED

(* Filtering constructs a new decorated execution; final-result equivalence
   is used only to discharge non-Error final instruction side conditions. *)
Theorem decorated_block_clear_nops:
  !Q fuel ctx bb s r. decorated_block Q fuel ctx bb s r ==>
  !Q'. (!inst u j. Q inst u ==> Q' inst (u with vs_inst_idx := j)) ==>
    decorated_block Q' fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
        (TAKE s.vs_inst_idx bb.bb_instructions)))
      (exec_block fuel ctx (clear_nops_block bb)
        (s with vs_inst_idx := LENGTH (FILTER (\i. i.inst_opcode <> NOP)
          (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  ho_match_mp_tac decorated_block_ind >> rpt strip_tac
  >- suspend "continue"
  >- suspend "term"
  >- suspend "halt"
  >- suspend "abort"
  >> suspend "return"
QED

Resume decorated_block_clear_nops[continue]:
  fs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = inst` by gvs[get_instruction_def] >>
  Cases_on `inst.inst_opcode = NOP`
  >- ( `s1 = s` by metis_tac[step_nop_identity, exec_result_11] >> gvs[] >>
       `LENGTH (FILTER (\i. i.inst_opcode <> NOP)
         (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
        LENGTH (FILTER (\i. i.inst_opcode <> NOP)
         (TAKE s.vs_inst_idx bb.bb_instructions))` by
         (irule filter_take_nop >> simp[]) >>
       first_x_assum (qspec_then `Q'` mp_tac) >> simp[]) >>
  qabbrev_tac `j = LENGTH (FILTER (\i. i.inst_opcode <> NOP)
    (TAKE s.vs_inst_idx bb.bb_instructions))` >>
  `get_instruction (clear_nops_block bb) j = SOME inst` by
    (simp[get_instruction_def, clear_nops_block_def, Abbr `j`] >>
     conj_tac >- (irule filter_take_lt >> simp[]) >>
     qpat_assum `EL _ _ = inst` (fn th => rewrite_tac[GSYM th]) >>
     irule filter_take_el >> simp[]) >>
  `LENGTH (FILTER (\i. i.inst_opcode <> NOP)
      (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) = SUC j` by
    (simp[Abbr `j`] >> irule filter_take_keep >> simp[]) >>
  `step_inst fuel ctx inst (s with vs_inst_idx := j) =
     OK (s1 with vs_inst_idx := j)` by
    (drule step_inst_non_term_idx >>
     disch_then (qspecl_then [`fuel`, `ctx`, `s`, `j`] mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `Q'` mp_tac) >> simp[] >> strip_tac >>
  simp[Once exec_block_def] >>
  irule (cj 1 decorated_block_rules) >>
  qexistsl_tac [`inst`, `s1 with vs_inst_idx := j`] >> simp[]
QED

Resume decorated_block_clear_nops[term]:
  irule decorated_clear_last >> conj_tac
  >- (simp[Once exec_block_def] >> Cases_on `s1.vs_halted` >> simp[]) >>
  qexists_tac `inst` >> simp[]
QED
Resume decorated_block_clear_nops[halt]:
  irule decorated_clear_last >> conj_tac
  >- simp[Once exec_block_def] >>
  qexists_tac `inst` >> simp[]
QED
Resume decorated_block_clear_nops[abort]:
  irule decorated_clear_last >> conj_tac
  >- simp[Once exec_block_def] >>
  qexists_tac `inst` >> simp[]
QED
Resume decorated_block_clear_nops[return]:
  irule decorated_clear_last >> conj_tac
  >- simp[Once exec_block_def] >>
  qexists_tac `inst` >> simp[]
QED
Finalise decorated_block_clear_nops

Theorem decorated_block_clear_phis:
  bb_well_formed bb /\
  decorated_block Q fuel ctx bb
    (s with vs_inst_idx := phi_prefix_length bb.bb_instructions) r /\
  (!inst u j. Q inst u ==> Q' inst (u with vs_inst_idx := j)) ==>
  ?r'. decorated_block Q' fuel ctx (clear_nops_block bb)
         (s with vs_inst_idx := phi_prefix_length (clear_nops_block bb).bb_instructions) r' /\
       result_equiv {} r r'
Proof
  strip_tac >>
  `phi_prefix_length (clear_nops_block bb).bb_instructions =
   phi_prefix_length bb.bb_instructions` by
    (simp[clear_nops_block_def] >> irule phi_prefix_length_filter_nop >>
     fs[bb_well_formed_def]) >>
  drule decorated_block_clear_nops >>
  disch_then (qspec_then `Q'` mp_tac) >>
  simp[filter_take_phi_prefix_length] >> strip_tac >>
  goal_assum (drule_at Any) >>
  qpat_assum `decorated_block Q _ _ _ _ r`
    (mp_tac o MATCH_MP decorated_block_erase) >> strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`,
    `s with vs_inst_idx := phi_prefix_length bb.bb_instructions`] clear_nops_block_gen) >>
  simp[filter_take_phi_prefix_length]
QED

Theorem decorated_clear_entry:
  wf_function fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  decorated_block Q fuel ctx bb
    (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) r /\
  (!inst u j. Q inst u ==> Q' inst (u with vs_inst_idx := j)) ==>
  lookup_block s.vs_current_bb (clear_nops_function fn).fn_blocks =
    SOME (clear_nops_block bb) /\
  eval_phis s (clear_nops_block bb).bb_instructions = OK s_phi /\
  ?r'. decorated_block Q' fuel ctx (clear_nops_block bb)
    (s_phi with vs_inst_idx := phi_prefix_length (clear_nops_block bb).bb_instructions) r' /\
    result_equiv {} r r'
Proof
  strip_tac >>
  `bb_well_formed bb` by
    (drule lookup_block_MEM >> fs[wf_function_def]) >>
  conj_tac >- simp[clear_nops_function_def, lookup_block_clear_nops] >>
  conj_tac
  >- ( `eval_phis s (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions) =
         eval_phis s bb.bb_instructions` by
         (irule eval_phis_filter_nop_wf >> fs[bb_well_formed_def]) >>
       simp[clear_nops_block_def]) >>
  irule decorated_block_clear_phis >> metis_tac[]
QED

Theorem decorated_run_clear_nops:
  !Q fuel ctx fn s r. decorated_run Q fuel ctx fn s r ==>
  !Q'. wf_function fn /\
    (!inst u j. Q inst u ==> Q' inst (u with vs_inst_idx := j)) ==>
    ?r'. decorated_run Q' fuel ctx (clear_nops_function fn) s r' /\
         result_equiv {} r r'
Proof
  ho_match_mp_tac decorated_run_ind >> rpt strip_tac
  >- suspend "continue"
  >- suspend "halted"
  >- suspend "halt"
  >- suspend "abort"
  >> suspend "return"
QED

Resume decorated_run_clear_nops[continue]:
  drule_all decorated_clear_entry >> strip_tac >>
  rename1 `result_equiv {} (OK next) br` >>
  Cases_on `br` >> gvs[result_equiv_def] >>
  drule state_equiv_empty_eq >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `Q'` mp_tac) >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule (cj 1 decorated_run_rules) >>
  qexistsl_tac [`clear_nops_block bb`, `next`, `s_phi`] >> simp[]
QED
Resume decorated_run_clear_nops[halted]:
  drule_all decorated_clear_entry >> strip_tac >>
  rename1 `result_equiv {} (OK next) br` >>
  Cases_on `br` >> gvs[result_equiv_def] >>
  drule state_equiv_empty_eq >> strip_tac >> gvs[] >>
  qexists_tac `Halt next` >> simp[result_equiv_def, execution_equiv_refl] >>
  irule (cj 2 decorated_run_rules) >> simp[] >>
  qexistsl_tac [`clear_nops_block bb`, `s_phi`] >> simp[]
QED
Resume decorated_run_clear_nops[halt]:
  drule_all decorated_clear_entry >> strip_tac >>
  rename1 `result_equiv {} (Halt _) br` >>
  qexists_tac `br` >> conj_tac
  >- (Cases_on `br` >> gvs[result_equiv_def] >>
      irule (cj 3 decorated_run_rules) >>
      qexistsl_tac [`clear_nops_block bb`, `s_phi`] >> simp[]) >>
  first_assum ACCEPT_TAC
QED
Resume decorated_run_clear_nops[abort]:
  drule_all decorated_clear_entry >> strip_tac >>
  rename1 `result_equiv {} (Abort _ _) br` >>
  qexists_tac `br` >> conj_tac
  >- (Cases_on `br` >> gvs[result_equiv_def] >>
      irule (cj 4 decorated_run_rules) >>
      qexistsl_tac [`clear_nops_block bb`, `s_phi`] >> simp[]) >>
  first_assum ACCEPT_TAC
QED
Resume decorated_run_clear_nops[return]:
  drule_all decorated_clear_entry >> strip_tac >>
  rename1 `result_equiv {} (IntRet _ _) br` >>
  qexists_tac `br` >> conj_tac
  >- (Cases_on `br` >> gvs[result_equiv_def] >>
      irule (cj 5 decorated_run_rules) >>
      qexistsl_tac [`clear_nops_block bb`, `s_phi`] >> simp[]) >>
  first_assum ACCEPT_TAC
QED
Finalise decorated_run_clear_nops
