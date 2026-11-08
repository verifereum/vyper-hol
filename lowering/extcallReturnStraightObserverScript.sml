(* Equal-block, length-preserving entry-prefix sanitation. *)
Theory extcallReturnStraightObserver
Ancestors
  extcallReturnObserver extcallReturnObserverRun extcallReturnCountedTransport exprSimAbiGasBridge compileEnv fragExec exprLoweringProps abiDecoderLoop
  simplifyCfgFixupSemantics venomExecSemantics venomExecProofs
  venomInstProofs venomInstProofs1 venomInstProps venomInst list rich_list
  arithmetic venomWf mem2varBlockSimHelpers

Theorem return_straight_shape:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  emitted_blocks sa sb = []
Proof
  simp[cs_extends_def] >> strip_tac >>
  `new = []` by (qpat_x_assum `_ = new ++ _` (mp_tac o AP_TERM ``LENGTH: basic_block list -> num``) >> simp[]) >>
  gvs[emitted_blocks_def]
QED

Theorem return_straight_swap:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (start_swap sa sa.cs_current_bb ids sb).cs_current_bb = sb.cs_current_bb /\
  (start_swap sa sa.cs_current_bb ids sb).cs_blocks = sb.cs_blocks /\
  LENGTH (start_swap sa sa.cs_current_bb ids sb).cs_current_insts =
    LENGTH sb.cs_current_insts /\
  cs_extends (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb)
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  simp[start_swap_def, start_relabel_def] >>
  conj_tac >- (imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem return_straight_observer_block:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  LENGTH sa.cs_current_insts <= s.vs_inst_idx ==>
  exec_block fuel ctx
    <|bb_label := sb.cs_current_bb;
      bb_instructions :=
        (start_swap sa sa.cs_current_bb ids sb).cs_current_insts ++
          [mk_inst stop STOP [] []]|> s =
  exec_block fuel ctx
    <|bb_label := sb.cs_current_bb;
      bb_instructions := sb.cs_current_insts ++ [mk_inst stop STOP [] []]|> s
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  simp[start_swap_def] >> irule scfg_exec_block_suffix >> simp[] >>
  `LENGTH sa.cs_current_insts <= LENGTH sb.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  simp[DROP_APPEND, DROP_DROP] >>
  `s.vs_inst_idx - LENGTH sa.cs_current_insts + LENGTH sa.cs_current_insts =
     s.vs_inst_idx` by decide_tac >> simp[DROP_LENGTH_TOO_LONG, DROP_DROP_T]
QED

(* An OK zzbb result can only leave through a jump: the appended STOP
   prevents falling off the block, and the reachable suffix excludes calls. *)
Theorem return_straight_block_no_reentry:
  !n s bb fuel ctx t lbl stop.
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    LAST bb.bb_instructions = mk_inst stop STOP [] [] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label lbl) i.inst_operands)
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    ~s.vs_halted /\ exec_block fuel ctx bb s = OK t ==>
    t.vs_current_bb <> lbl
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `EL s.vs_inst_idx bb.bb_instructions <> mk_inst stop STOP [] []` by
    (strip_tac >> qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
     simp[Once exec_block_def, step_inst_non_invoke, mk_inst_def,
          step_inst_base_opcode_eqs]) >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by decide_tac >>
     gvs[LAST_EL, NOT_NIL_EQ_LENGTH_NOT_0]) >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE /\
    ~MEM (Label lbl) (EL s.vs_inst_idx bb.bb_instructions).inst_operands` by
    (fs[EVERY_MEM, MEM_DROP] >>
     first_x_assum irule >> qexists_tac `0` >> simp[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >> simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s` >> simp[] >>
  rename1 `step_inst_base _ s = OK middle` >>
  `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  IF_CASES_TAC >> simp[] >> strip_tac
  >- (`MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode [JMP; JNZ; DJMP]` by
        (Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
         fs[is_terminator_def] >>
         gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
      metis_tac[frag_observer_jump_no_reentry]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`bb`, `ctx`, `fuel`,
    `middle with vs_inst_idx := SUC s.vs_inst_idx`, `stop`] >>
  simp[] >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions =
     DROP 1 (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_DROP_T, ADD1] >>
  metis_tac[EVERY_DROP]
QED

Theorem return_straight_observer_run:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ frag_gas_free sa sb /\
  LENGTH ids = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  LENGTH sa.cs_current_insts <= s.vs_inst_idx /\
  s.vs_inst_idx <= LENGTH sb.cs_current_insts ==>
  run_from fuel ctx
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop) s =
  run_from fuel ctx (frag_observer sa sb func stop) s
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  drule_all return_straight_swap >> strip_tac >>
  `emitted_blocks (start_relabel sa.cs_current_bb ids sa)
     (start_swap sa sa.cs_current_bb ids sb) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  qabbrev_tac `bb = <|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst stop STOP [] []]|>` >>
  `exec_block fuel ctx
     <|bb_label := sb.cs_current_bb;
       bb_instructions := (start_swap sa sa.cs_current_bb ids sb).cs_current_insts ++
          [mk_inst stop STOP [] []]|> s = exec_block fuel ctx bb s` by
    (simp[Abbr `bb`] >> metis_tac[return_straight_observer_block]) >>
  once_rewrite_tac[run_from_def] >>
  fs[frag_observer_def, lookup_block_def, FIND_thm, Abbr `bb`] >>
  qpat_assum `sb.cs_current_bb = sa.cs_current_bb` (fn eq =>
    qpat_x_assum `exec_block _ _ _ _ = exec_block _ _ _ _`
      (assume_tac o REWRITE_RULE [eq])) >>
  simp[] >>
  qabbrev_tac `zzbb = <|bb_label := sa.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst stop STOP [] []]|>` >>
  Cases_on `exec_block fuel ctx zzbb s` >> simp[] >>
  rename1 `exec_block fuel ctx zzbb s = OK middle` >>
  `middle.vs_current_bb <> sb.cs_current_bb` by
    (irule return_straight_block_no_reentry >>
     qexistsl_tac [`zzbb`, `ctx`, `fuel`,
       `LENGTH zzbb.bb_instructions - s.vs_inst_idx`, `s`, `stop`] >>
     simp[Abbr `zzbb`, LAST_APPEND] >>
     `DROP s.vs_inst_idx sb.cs_current_insts =
       DROP (s.vs_inst_idx - LENGTH sa.cs_current_insts)
         (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts)` by
       simp[DROP_DROP_T] >>
     fs[frag_gas_free_def, frag_code_def, emitted_insts_def] >>
     `s.vs_inst_idx - LENGTH sb.cs_current_insts = 0` by decide_tac >>
     simp[DROP_APPEND, EVERY_APPEND, mk_inst_def] >>
     irule EVERY_DROP >> fs[EVERY_MEM] >> metis_tac[]) >>
  `middle.vs_current_bb <> sa.cs_current_bb` by metis_tac[] >>
  Cases_on `middle.vs_halted` >> simp[] >> Cases_on `fuel` >>
  once_rewrite_tac[run_blocks_def] >>
  simp[frag_observer_def, lookup_block_def, FIND_thm, Abbr `zzbb`]
QED

Theorem return_straight_observer_sim:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ frag_gas_free sa sb /\
  LENGTH ids = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  abi_decode_sim ctx
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop) s t ==>
  abi_decode_sim ctx (frag_observer sa sb func stop) s t
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sb.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  qpat_x_assum `abi_decode_sim _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decode_sim_def] >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  `run_from fuel ctx
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop) t = r` by
    simp[return_straight_observer_run] >>
  `?fuel'. run_from fuel' ctx
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop) s = r` by metis_tac[] >>
  gvs[return_straight_observer_run]
QED

Theorem return_straight_observer_code:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  fn_has_code (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb)
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop)
Proof
  strip_tac >> drule_all return_straight_swap >> strip_tac >>
  drule_all return_straight_shape >> strip_tac >>
  `emitted_blocks (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  simp[fn_has_code_def, frag_observer_def, lookup_block_def, FIND_thm,
       IS_PREFIX_APPEND]
QED

Theorem return_straight_observer_provenance:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  fn_has_code sa sb func /\ frag_gas_free sa sb /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (frag_observer (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb) func stop).fn_name = func.fn_name /\
  (!i. MEM i (fn_insts
     (frag_observer (start_relabel sa.cs_current_bb ids sa)
       (start_swap sa sa.cs_current_bb ids sb) func stop)) ==>
     i.inst_opcode <> INVOKE /\
     (i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)))
Proof
  strip_tac >> drule_all return_straight_swap >> strip_tac >>
  drule_all return_straight_shape >> strip_tac >>
  `emitted_blocks (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  simp[frag_observer_def, fn_insts_def, fn_insts_blocks_def,
       start_swap_def, MEM_MAP, MEM_APPEND, mk_inst_def] >>
  `!i. MEM i (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) ==>
       i.inst_opcode <> INVOKE` by
    (fs[frag_gas_free_def, frag_code_def, emitted_insts_def, EVERY_MEM] >>
     metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  `MEM i (fn_insts func)` suffices_by simp[fn_insts_def] >>
  fs[fn_has_code_def] >> irule lookup_block_fn_insts >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[MEM_APPEND] >>
  disj1_tac >> irule MEM_DROP_IMP >> goal_assum (drule_at Any)
QED

Theorem return_straight_observer_distinct:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  LENGTH ids = LENGTH sa.cs_current_insts /\ ALL_DISTINCT ids /\
  ~MEM stop ids /\
  (!i. MEM i (fn_insts func) ==> ~MEM i.inst_id ids /\ i.inst_id <> stop) ==>
  fn_inst_ids_distinct
    (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop)
Proof
  strip_tac >> drule_all return_straight_swap >> strip_tac >>
  drule_all return_straight_shape >> strip_tac >>
  `emitted_blocks (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sb.cs_current_insts)` by
    (fs[fn_has_code_def] >>
     `MEM bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
       (irule ALL_DISTINCT_FLAT_MAP_MEM >>
        qexists_tac `MAP (\b. b.bb_instructions) func.fn_blocks` >>
        fs[fn_inst_ids_distinct_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >>
        metis_tac[]) >>
     qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  `!i. MEM i (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) ==>
       MEM i (fn_insts func)` by
    (rpt strip_tac >> fs[fn_has_code_def] >> irule lookup_block_fn_insts >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[MEM_APPEND] >>
     disj1_tac >> irule MEM_DROP_IMP >> goal_assum (drule_at Any)) >>
  simp[fn_inst_ids_distinct_def, frag_observer_def, start_swap_def,
       MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, mk_inst_def,
       ALL_DISTINCT_APPEND, MEM_MAP] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts))` by
    (pure_rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem return_straight_observer_members:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (MEM i (fn_insts
     (frag_observer (start_relabel sa.cs_current_bb ids sa)
       (start_swap sa sa.cs_current_bb ids sb) func stop)) <=>
   (?id. MEM id ids /\ i = mk_inst id NOP [] []) \/
   MEM i (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) \/
   i = mk_inst stop STOP [] [])
Proof
  strip_tac >> drule_all return_straight_swap >> strip_tac >>
  drule_all return_straight_shape >> strip_tac >>
  `emitted_blocks (start_relabel sa.cs_current_bb ids sa)
    (start_swap sa sa.cs_current_bb ids sb) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  simp[frag_observer_def, fn_insts_def, fn_insts_blocks_def,
       start_swap_def, MEM_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem return_straight_observer_id_agreement:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  (!i. MEM i (fn_insts func) ==> ~MEM i.inst_id ids /\ i.inst_id <> stop) ==>
  !i j. MEM i (fn_insts func) /\
    MEM j (fn_insts (frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop)) /\
    i.inst_id = j.inst_id ==> i = j
Proof
  strip_tac >> simp[return_straight_observer_members] >> rpt strip_tac
  >- (gvs[mk_inst_def] >> metis_tac[])
  >- (`MEM j (fn_insts func)` by
        (fs[fn_has_code_def] >> irule lookup_block_fn_insts >>
         goal_assum (drule_at Any) >>
         qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
         simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[MEM_APPEND] >>
         disj1_tac >> irule MEM_DROP_IMP >> goal_assum (drule_at Any)) >>
      metis_tac[localPtrsPropsTheory.fn_inst_ids_distinct_inj]) >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem return_straight_completion:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ frag_gas_free sa sb /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ids stop full. LENGTH ids = LENGTH sa.cs_current_insts /\
    fn_has_code (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) full /\
    fn_inst_ids_distinct full /\ full.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts full) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
    (!i. i.inst_opcode = ALLOCA ==>
       (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
    (!fuel ctx'. run_from fuel ctx' full s =
                  run_from fuel ctx (frag_observer sa sb func stop) s) /\
    (!t ctx'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       abi_decode_sim ctx' full s t ==>
       abi_decode_sim ctx (frag_observer sa sb func stop) s t)
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sb.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  qspecl_then [`fn_insts func`, `LENGTH sa.cs_current_insts`]
    strip_assume_tac frag_relabel_fresh_ids >> rename1 `~MEM stop ids` >>
  qabbrev_tac `obs = frag_observer (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) func stop` >>
  `fn_has_code (start_relabel sa.cs_current_bb ids sa)
      (start_swap sa sa.cs_current_bb ids sb) obs /\
   fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
   (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE /\
       (i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)))` by
    (drule_all return_straight_observer_provenance >>
     disch_then (qspec_then `stop` strip_assume_tac) >>
     simp[Abbr `obs`, return_straight_observer_code,
          return_straight_observer_distinct]) >>
  qspec_then `obs` strip_assume_tac (Q.GEN `obs` return_observer_complete_fresh_label) >>
  qabbrev_tac `full = return_observer_complete func obs keep` >>
  `sa.cs_current_bb <> keep /\ sb.cs_current_bb <> keep` by
    (drule_all return_straight_swap >> strip_tac >>
     drule_all fn_has_code_start >> strip_tac >>
     fs[fn_has_code_def, start_relabel_def] >>
     imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
     fs[MEM_MAP] >> metis_tac[]) >>
  qexistsl_tac [`ids`, `stop`, `full`] >>
  simp[Abbr `full`, return_observer_complete_has_code] >>
  conj_tac
  >- (irule return_observer_complete_ids >> simp[] >>
      simp[Abbr `obs`] >> metis_tac[return_straight_observer_id_agreement]) >>
  conj_tac >- simp[return_observer_complete_def] >>
  conj_tac
  >- (simp[return_observer_complete_members] >> metis_tac[]) >>
  conj_tac
  >- (simp[return_observer_complete_members] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac >- simp[return_observer_complete_allocas] >>
  conj_tac
  >- (rpt gen_tac >>
      `run_from fuel ctx' (return_observer_complete func obs keep) s =
       run_from fuel ctx obs s` by
        (irule return_observer_complete_run_from >> fs[EVERY_MEM]) >>
      simp[Abbr `obs`] >> irule return_straight_observer_run >> simp[]) >>
  rpt strip_tac >> irule return_straight_observer_sim >> simp[] >>
  qexistsl_tac [`ids`] >> simp[] >>
  irule return_observer_complete_sim >> simp[] >>
  qexistsl_tac [`ctx'`, `func`, `keep`] >> fs[EVERY_MEM]
QED
