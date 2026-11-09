Theory concretizePtrHistoryDemand
Ancestors
  frameExecutionHistory ptrDiscipline venomExecSemantics venomInst list rich_list
  pred_set

Theorem ptr_step_writes_subset:
  range_bytes (step_writes inst s s') SUBSET
  range_bytes (source_memory_write_ranges inst s)
Proof
  simp[step_writes_def] >> IF_CASES_TAC >> simp[] >>
  rw[range_bytes_def, SUBSET_DEF, listTheory.MEM_MAP] >>
  PairCases_on `y` >> gvs[] >>
  qexistsl [`off`,`y1`] >> simp[] >>
  Cases_on `y1 <= LENGTH s'.vs_returndata` >> gvs[arithmeticTheory.MIN_DEF]
QED

Theorem ptr_step_mem_no_write:
  (x IN tn.t_mem \/ x IN new_site_bytes s s') /\
  x NOTIN range_bytes (source_memory_write_ranges inst s) ==>
  x IN (step_taint inst s s' tn).t_mem
Proof
  mp_tac ptr_step_writes_subset >>
  simp[step_taint_def, mem_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_history_saved_invokes[local]:
  !vs0 ctx stk PG G tn fn inst s hs h.
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
  EVERY (\f. f.cf_inst.inst_opcode = INVOKE) stk
Proof
  ho_match_mp_tac frame_history_ind >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_history_split_snoc:
  h ++ [p] = pre ++ [a] ++ tail /\ tail <> [] ==>
  h = pre ++ [a] ++ FRONT tail /\ LAST tail = p
Proof
  strip_tac >>
  `tail = FRONT tail ++ [LAST tail]` by metis_tac[APPEND_FRONT_LAST] >>
  qpat_x_assum `h ++ [p] = _` mp_tac >>
  once_asm_rewrite_tac[] >> simp[APPEND_ASSOC, FRONT_APPEND]
QED

Theorem ptr_every_front:
  EVERY P xs ==> EVERY P (FRONT xs)
Proof
  Cases_on `xs = []` >> simp[] >>
  metis_tac[APPEND_FRONT_LAST, EVERY_APPEND]
QED

Theorem ptr_every_last:
  xs <> [] /\ EVERY P xs ==> P (LAST xs)
Proof
  metis_tac[APPEND_FRONT_LAST, EVERY_APPEND, listTheory.EVERY_DEF]
QED

Theorem ptr_history_fresh_no_clobber:
  !vs0 ctx stk PG G tn fn inst s hs h.
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
  !pre ai sa tail fuel sa' x.
  h = pre ++ [(ai,sa)] ++ tail /\ tail <> [] /\
  ai.inst_opcode = ALLOCA /\ step_inst fuel ctx ai sa = OK sa' /\
  x IN new_site_bytes sa sa' /\
  EVERY (\p. (FST p).inst_opcode <> INVOKE /\
    x NOTIN range_bytes (source_memory_write_ranges (FST p) (SND p)))
    ((ai,sa)::FRONT tail) ==>
  x IN tn.t_mem
Proof
  ho_match_mp_tac frame_history_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ptr_history_fresh_no_clobber[entry]:
  rpt strip_tac >> Cases_on `pre` >> gvs[] >>
  Cases_on `tail` >> gvs[]
QED

Resume ptr_history_fresh_no_clobber[next]:
  rpt gen_tac >> strip_tac >>
  drule_all ptr_history_split_snoc >> strip_tac >>
  drule frame_history_current_endpoint >> strip_tac >>
  Cases_on `FRONT tail = []`
  >- (gvs[LAST_APPEND] >>
      `sa' = s'` by gvs[step_inst_non_invoke] >> gvs[] >>
      irule ptr_step_mem_no_write >> simp[]) >>
  `LAST (FRONT tail) = (inst,s)` by
    (qpat_x_assum `LAST h = _` mp_tac >>
     qpat_x_assum `h = _` (fn th => rewrite_tac[th]) >>
     Cases_on `FRONT tail` >> fs[LAST_APPEND]) >>
  `x NOTIN range_bytes (source_memory_write_ranges inst s)` by
    (gvs[] >> drule_all ptr_every_last >> simp[]) >>
  irule ptr_step_mem_no_write >> simp[] >> disj1_tac >>
  first_x_assum irule >>
  qexistsl [`ai`,`fuel'`,`pre`,`sa`,`sa'`,`FRONT tail`] >>
  gvs[] >> irule ptr_every_front >> simp[]
QED

Resume ptr_history_fresh_no_clobber[block]:
  rpt gen_tac >> strip_tac >>
  drule_all ptr_history_split_snoc >> strip_tac >>
  drule frame_history_current_endpoint >> strip_tac >>
  Cases_on `FRONT tail = []`
  >- gvs[LAST_APPEND, is_terminator_def] >>
  Cases_on `lookup_block s'.vs_current_bb fn.fn_blocks` >>
  simp[entry_taint_vars_def] >>
  first_x_assum irule >>
  qexistsl [`ai`,`fuel'`,`pre`,`sa`,`sa'`,`FRONT tail`] >>
  gvs[] >> irule ptr_every_front >> simp[]
QED

Resume ptr_history_fresh_no_clobber[call]:
  rpt strip_tac >> Cases_on `pre` >> gvs[] >>
  Cases_on `tail` >> gvs[]
QED

Resume ptr_history_fresh_no_clobber[ret]:
  rpt gen_tac >> strip_tac >>
  drule_all ptr_history_split_snoc >> strip_tac >>
  drule ptr_history_saved_invokes >> simp[] >> strip_tac >>
  drule frame_history_suspended_endpoints >> simp[] >> strip_tac >>
  Cases_on `FRONT tail = []`
  >- gvs[LAST_APPEND] >>
  `LAST (FRONT tail) = (f.cf_inst,f.cf_state)` by
    (qpat_x_assum `LAST (_ ++ _) = _` mp_tac >>
     Cases_on `FRONT tail` >> fs[LAST_APPEND]) >>
  gvs[] >> drule_all ptr_every_last >> simp[]
QED

Finalise ptr_history_fresh_no_clobber

Theorem ptr_history_fresh_untainted_witness:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  h = pre ++ [(ai,sa)] ++ tail /\ tail <> [] /\
  ai.inst_opcode = ALLOCA /\
  step_inst fuel ctx ai sa = OK sa' /\
  x IN new_site_bytes sa sa' /\ x NOTIN tn.t_mem ==>
  EXISTS (\p. (FST p).inst_opcode = INVOKE \/
    x IN range_bytes (source_memory_write_ranges (FST p) (SND p)))
    ((ai,sa)::FRONT tail)
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `EVERY (\p. (FST p).inst_opcode <> INVOKE /\
     x NOTIN range_bytes (source_memory_write_ranges (FST p) (SND p)))
     ((ai,sa)::FRONT tail)` by
    gvs[listTheory.NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[ptr_history_fresh_no_clobber]
QED
