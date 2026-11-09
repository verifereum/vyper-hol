(* Paired cutpoints at block entry and control-transfer instructions. *)
Theory ctorDeployMemoryRunPtrPrefixBlocks
Ancestors
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst relation arithmetic

Theorem prefix_blocks_entry_pair:
  !s fn bb sp r D lo f ctx PG G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    r = (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
    ((ptr_safe_blocks D lo (SUC f) ctx fn PG G tn s <=>
      ptr_safe_block D lo f ctx fn PG G tn bb r) /\
     ghost_blocks (SUC f) ctx fn PG G tn s =
      ghost_block f ctx fn PG G tn bb r)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac >- (irule ptr_safe_blocks_block >> simp[]) >>
  simp[Once ghost_blocks_def]
QED

Theorem prefix_terminator_entry:
  !bb s inst f ctx t fn G tn Gt qt D lo PG.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst f ctx inst s = OK t /\ is_terminator inst.inst_opcode /\
    ~t.vs_halted /\ Gt = entry_prov fn t G /\
    qt = entry_taint_vars fn t tn ==>
    (ptr_safe_block D lo f ctx fn PG G tn bb s <=>
     ptr_safe_step D lo f ctx fn PG G tn inst s /\
     ptr_safe_blocks D lo f ctx fn PG Gt qt t)
Proof
  rpt strip_tac >> gvs[] >>
  irule ptr_safe_block_terminator >> simp[]
QED

Theorem prefix_paired_blocks_chain_fuel:
  !n u g q.
    (!j. j < n ==> !f.
      ptr_safe_blocks D lo f ctx fn PG (g (SUC j)) (q (SUC j)) (u (SUC j)) ==>
      ptr_safe_blocks D lo (SUC f) ctx fn PG (g j) (q j) (u j)) ==>
    !f. ptr_safe_blocks D lo f ctx fn PG (g n) (q n) (u n) ==>
      ptr_safe_blocks D lo (n+f) ctx fn PG (g 0) (q 0) (u 0)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  `ptr_safe_blocks D lo (SUC f) ctx fn PG (g n) (q n) (u n)` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `n+SUC f = SUC n+f` by decide_tac >>
  first_x_assum (qspecl_then [`u`,`g`,`q`] mp_tac) >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  disch_then (qspec_then `SUC f` mp_tac) >> simp[]
QED

Theorem prefix_paired_blocks_chain_all_fuel:
  !n u g q.
    (!j. j < n ==> !f.
      ptr_safe_blocks D lo f ctx fn PG (g (SUC j)) (q (SUC j)) (u (SUC j)) ==>
      ptr_safe_blocks D lo (SUC f) ctx fn PG (g j) (q j) (u j)) ==>
    (!f. ptr_safe_blocks D lo f ctx fn PG (g n) (q n) (u n)) ==>
    !f. ptr_safe_blocks D lo f ctx fn PG (g 0) (q 0) (u 0)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum (qspecl_then [`u`,`g`,`q`] irule) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  Cases >- simp[Once ptr_safe_blocks_def] >>
  first_x_assum irule >> simp[]
QED

Theorem prefix_paired_blocks_chain_execution:
  !n u.
    (!j. j < n ==> ?bb.
      lookup_block (u j).vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis (u j) bb.bb_instructions = OK (u j) /\
      phi_prefix_length bb.bb_instructions = 0 /\ (u j).vs_inst_idx = 0 /\
      (!f. exec_block f ctx bb (u j) = OK (u (SUC j))) /\
      ~(u (SUC j)).vs_halted) ==>
    RTC (\s t. ?bb.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK s /\
      phi_prefix_length bb.bb_instructions = 0 /\ s.vs_inst_idx = 0 /\
      (!f. exec_block f ctx bb s = OK t) /\ ~t.vs_halted) (u 0) (u n)
Proof
  Induct >- simp[RTC_REFL] >> rpt gen_tac >> strip_tac >>
  irule RTC_TRANS >> qexists_tac `u n` >>
  conj_tac >-
    (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  irule RTC_SINGLE >> first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

val _ = export_theory();
