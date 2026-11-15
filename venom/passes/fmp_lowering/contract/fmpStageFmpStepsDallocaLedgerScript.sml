Theory fmpStageFmpStepsDallocaLedger
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLowerSequenceExec fmpLedgerProps fmpAliasProps
  fmpReclaimDefs fmpAnalysisDefs venomState finite_map words list
  allocaRemapSSA dfHelperDefs fmpAliasDefs

Theorem fmp_dalloca_analysis_suc:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  inst = EL idx bb.bb_instructions /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  df_at NONE states bb.bb_label idx = SOME st ==>
  ?st'. df_at NONE states bb.bb_label (SUC idx) = SOME st' /\
    st'.frs_stack = out :: SND (fmp_pop_at infos fn
      (liveness_analyze fn) env (bb.bb_label,idx) inst st)
Proof
  strip_tac >> drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_def, fmp_reclaim_step_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  `~fmp_clears_marks infos (EL idx bb.bb_instructions)` by
    metis_tac[fmp_dalloca_not_clear] >>
  drule_all fmp_apply_effect_dalloca_stack >> simp[]
QED

Theorem fmp_dalloca_ledger_push:
  fmp_ledger_ok insts env t lo regions /\
  lo + z < dimword (:256) /\
  fmp_dalloca_query insts env out = SOME site /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) regions))
    [plus31;mask;aligned;runner;out] /\
  t1 = (update_var runner (n2w (lo+z))
        (update_var out (n2w lo)
         (update_var aligned a (update_var mask m (update_var plus31 p t)))))
        with vs_inst_idx := idx ==>
  fmp_ledger_ok insts env t1 (lo+z)
    (<| fr_mark := out; fr_site := site; fr_lo := lo; fr_hi := lo+z |> :: regions)
Proof
  strip_tac >> gvs[] >>
  simp[Once fmp_ledger_ok_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule fmp_ledger_frame >> qexists_tac `t` >> simp[] >>
  gvs[EVERY_MEM, MEM_MAP, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem fmp_dalloca_ledger_link:
  fmp_ledger_link sm eb lo rs /\
  (!b n c id. FLOOKUP sm (b,n) = SOME (c,id) ==> 0 < n /\ c+n <= lo) /\
  eb <= b /\ (rs <> [] ==> (LAST rs).fr_lo <= lo) /\
  sm1 = (if z = 0 then sm else sm |+ ((b,z),(lo,site))) ==>
  fmp_ledger_link sm1 eb (lo+z)
    (<|fr_mark := out; fr_site := site; fr_lo := lo; fr_hi := lo+z|> :: rs)
Proof
  strip_tac >>
  `!b n c id. FLOOKUP sm (b,n) = SOME (c,id) ==> c < lo` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  Cases_on `rs = []`
  >- (gvs[fmp_ledger_link_def] >> rpt strip_tac >>
      Cases_on `z = 0` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.NOT_LESS]) >>
  gvs[fmp_ledger_link_def, LAST_CONS_cond] >> rpt strip_tac >>
  Cases_on `z = 0` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem dalloca_base_output_member[local]:
  fmp_base_output j = SOME v ==> MEM v j.inst_outputs
Proof
  simp[fmp_base_output_def, fmp_single_output_def] >>
  Cases_on `j.inst_opcode = BUMP` >> simp[] >>
  Cases_on `j.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]
QED

Theorem dalloca_base_transfer_exact[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM j (fn_insts fn) /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  (fmp_bases env out = [] \/ fmp_bases env out = [inst.inst_id]) ==>
  fmp_bases (fmp_base_transfer j env) out = [] \/
  fmp_bases (fmp_base_transfer j env) out = [inst.inst_id]
Proof
  strip_tac >>
  (Cases_on `fmp_base_output j` >> simp[fmp_base_transfer_def] >>
   rename1 `fmp_base_output j = SOME v` >>
   Cases_on `v = out`
   >- (`j = inst` by
         (drule dalloca_base_output_member >> strip_tac >>
          irule ssa_unique_output >> conj_tac
          >- (qexists_tac `fn` >> simp[]) >>
          qexists_tac `out` >> gvs[]) >>
       gvs[fmp_generated_bases_def, fmp_accumulate_bases_def,
           fmp_bases_def, FLOOKUP_UPDATE, list_union_def]) >>
   gvs[fmp_accumulate_bases_def, fmp_bases_def, FLOOKUP_UPDATE])
QED

Theorem dalloca_base_sweep_exact[local]:
  !xs env.
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  EVERY (\j. MEM j (fn_insts fn)) xs /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  (fmp_bases env out = [] \/ fmp_bases env out = [inst.inst_id]) ==>
  fmp_bases (fmp_base_sweep xs env) out = [] \/
  fmp_bases (fmp_base_sweep xs env) out = [inst.inst_id]
Proof
  Induct >> simp[fmp_base_sweep_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule dalloca_base_transfer_exact >> metis_tac[]
QED

Theorem dalloca_base_iter_exact[local]:
  !fuel env.
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  (fmp_bases env out = [] \/ fmp_bases env out = [inst.inst_id]) ==>
  fmp_bases (fmp_base_iter fuel (fn_insts fn) env) out = [] \/
  fmp_bases (fmp_base_iter fuel (fn_insts fn) env) out = [inst.inst_id]
Proof
  Induct >> simp[fmp_base_iter_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[] >>
  irule dalloca_base_sweep_exact >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_dalloca_output_query:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  fmp_base_analyze (fn_insts fn) = SOME env ==>
  fmp_dalloca_query (fn_insts fn) env out = SOME inst.inst_id
Proof
  strip_tac >>
  `MEM inst.inst_id (fmp_bases env out)` by
    (irule fmp_base_analyze_propagates >>
     qexistsl [`inst`, `fn_insts fn`] >>
     simp[fmp_base_output_def, fmp_single_output_def,
          fmp_generated_bases_def]) >>
  `fmp_bases env out = [] \/ fmp_bases env out = [inst.inst_id]` by
    (qpat_x_assum `fmp_base_analyze _ = _` mp_tac >>
     simp[fmp_base_analyze_def] >> strip_tac >>
     gvs[] >> irule dalloca_base_iter_exact >>
     simp[fmp_bases_def] >> metis_tac[]) >>
  gvs[fmp_dalloca_query_exact, EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_dalloca_ledger_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  wf_function fn /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  step_inst k C inst s = OK s1 /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
  MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
    (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
  fmp_ledger_ok (fn_insts fn) env t lo regions /\
  EVERY (\r. elo <= r.fr_lo) regions /\ elo <= lo /\
  fmp_ledger_link sm eb lo regions /\ fmp_frame_covers sm env eb lo G /\
  fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\ eb <= w2n s.vs_fmp /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) regions))
    [plus31;mask;aligned;runner;out] /\
  w2n s1.vs_fmp = w2n s.vs_fmp + z /\ lo+z < dimword (:256) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo)
     (update_var aligned a (update_var mask m (update_var plus31 p t)))))
    with vs_inst_idx := j /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
  ?st'. df_at NONE states s.vs_current_bb (SUC s.vs_inst_idx) = SOME st' /\
    st'.frs_stack = out :: MAP (\r. r.fr_mark) regions /\
    fmp_ledger_ok (fn_insts fn) env t1 (lo+z)
      (<|fr_mark := out; fr_site := inst.inst_id; fr_lo := lo; fr_hi := lo+z|>
       :: regions) /\
    EVERY (\r. elo <= r.fr_lo)
      (<|fr_mark := out; fr_site := inst.inst_id; fr_lo := lo; fr_hi := lo+z|>
       :: regions) /\
    fmp_ledger_link sm1 eb (lo+z)
      (<|fr_mark := out; fr_site := inst.inst_id; fr_lo := lo; fr_hi := lo+z|>
       :: regions) /\
    fmp_frame_covers sm1 env eb (lo+z) (step_prov PG G inst s1)
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[contextCodegenRelTheory.active_inst_def,
         venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  drule_all fmp_dalloca_output_query >> strip_tac >>
  `regions <> [] ==> (LAST regions).fr_lo <= lo` by
    (drule fmp_ledger_bounds >> simp[EVERY_MEM] >> strip_tac >>
     strip_tac >> first_x_assum (qspec_then `LAST regions` mp_tac) >>
     simp[rich_listTheory.MEM_LAST_NOT_NIL] >> decide_tac) >>
  `fmp_ledger_link sm1 eb (lo+z)
    (<|fr_mark := out; fr_site := inst.inst_id; fr_lo := lo; fr_hi := lo+z|>
     :: regions)` by
    (irule fmp_dalloca_ledger_link >> conj_tac >- simp[] >>
     qexistsl [`w2n s.vs_fmp`, `sm`] >>
     gvs[fmp_sites_ok_def] >> metis_tac[]) >>
  `df_at NONE states bb.bb_label s.vs_inst_idx = SOME st` by simp[] >>
  drule_all fmp_dalloca_analysis_suc >> strip_tac >>
  qexists_tac `st'` >> conj_tac >- metis_tac[] >>
  conj_tac >- (simp[] >> metis_tac[]) >> conj_tac
  >- (irule fmp_dalloca_ledger_push >> metis_tac[]) >>
  simp[] >>
  `!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==> b+z <= w2n s.vs_fmp` by
    (drule_all fmp_stage_frame_sites >> metis_tac[]) >>
  `!b n c id. FLOOKUP sm (b,n) = SOME (c,id) ==>
      0 < n /\ b+n <= w2n s.vs_fmp /\ c+n <= lo` by
    (gvs[fmp_sites_ok_def] >> metis_tac[]) >>
  `s1.vs_fmp = s.vs_fmp <=> z = 0` by
    (`w2n s1.vs_fmp = w2n s.vs_fmp <=> z = 0` by decide_tac >>
     metis_tac[wordsTheory.w2n_11]) >>
  drule_all fmp_stage_covers_dalloca >> simp[]
QED
