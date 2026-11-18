(* Successor ledger at a bounded DALLOCA point, after the restore pop. *)
Theory gasFocusFmpDallocaLedger
Ancestors
  fmpStageFmpStepsDallocaLedger fmpStageReclaimSound fmpStageRel
  fmpStepAnalysis fmpStepStack fmpStepSupply fmpLedgerProps
  fmpAliasDefs fmpAnalysisDefs dfHelperDefs cfgWf allocaRemapSSA
  o1PassContract venomWf venomInst venomState finite_map list rich_list words

Theorem focus_fmp_dalloca_ledger_push:
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states bb.bb_label i = SOME st /\
  MAP (\r. r.fr_mark) rs = SND (fmp_pop_at infos fn
    (liveness_analyze fn) env (bb.bb_label,i) inst st) /\
  fmp_ledger_ok (fn_insts fn) env t lo rs /\
  fmp_ledger_link sm eb lo rs /\ fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
  eb <= w2n s.vs_fmp /\ ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
  lo + z < dimword (:256) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo)
      (update_var aligned a (update_var mask m (update_var plus31 p t)))))
      with vs_inst_idx := j /\
  sm1 = (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
  let rs1 = <|fr_mark := out; fr_site := inst.inst_id;
              fr_lo := lo; fr_hi := lo+z|> :: rs in
    (?st'. df_at NONE states bb.bb_label (SUC i) = SOME st' /\
           st'.frs_stack = MAP (\r. r.fr_mark) rs1) /\
    fmp_ledger_ok (fn_insts fn) env t1 (lo+z) rs1 /\
    fmp_ledger_link sm1 eb (lo+z) rs1
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  simp[] >> conj_tac
  >- (drule_all fmp_dalloca_analysis_suc >> simp[]) >>
  conj_tac
  >- (`MEM inst (fn_insts fn)` by
        (simp[fn_insts_def, fn_insts_blocks_MEM] >>
         qexists_tac `bb` >> gvs[MEM_EL] >> metis_tac[]) >>
      drule_all fmp_dalloca_output_query >> strip_tac >>
      `~MEM out st.frs_stack` by
        metis_tac[fmp_stage_out_not_kept] >>
      drule_all fmp_reclaim_states_stack >> strip_tac >>
      `EVERY (\v. ~MEM v [plus31;mask;aligned;runner;out]) st.frs_stack` by
        (simp[EVERY_MEM] >> rpt strip_tac >>
         `fmp_dalloca_output fn v` by metis_tac[EVERY_MEM] >>
         `MEM v (fn_ir_vars fn)` by
           (fs[fmp_dalloca_output_def, fn_ir_vars_member,
               fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
         fs[] >> metis_tac[]) >>
      `EVERY (\v. ~MEM v [plus31;mask;aligned;runner;out])
        (MAP (\r. r.fr_mark) rs)` by
        (qpat_assum `MAP _ rs = _` (once_rewrite_tac o single) >>
         irule (cj 2 fmp_pop_at_every) >> simp[]) >>
      `EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) rs))
        [plus31;mask;aligned;runner;out]` by
        (pop_assum mp_tac >> simp[EVERY_MEM] >> metis_tac[]) >>
      drule_all fmp_dalloca_ledger_push >> simp[]) >>
  `rs <> [] ==> (LAST rs).fr_lo <= lo` by
    (drule fmp_ledger_bounds >> simp[EVERY_MEM] >> strip_tac >>
     strip_tac >> first_x_assum (qspec_then `LAST rs` mp_tac) >>
     simp[MEM_LAST_NOT_NIL] >> decide_tac) >>
  irule fmp_dalloca_ledger_link >> conj_tac >- simp[] >>
  qexistsl [`w2n s.vs_fmp`, `sm`] >>
  gvs[fmp_sites_ok_def] >> metis_tac[]
QED
