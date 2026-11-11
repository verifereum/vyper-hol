Theory basePtrConvergenceOrbit
Ancestors
  basePtrConvergenceTransfer basePtrConvergenceOrder basePtrDefs
  allocaRemapSSA venomWf venomInst finite_map list pred_set dfIterateProofs arithmetic venomFnInstsProofs

Theorem inst_output_member:
  inst_output i = SOME out ==> MEM out i.inst_outputs
Proof
  simp[inst_output_def, AllCaseEqs()] >> strip_tac >> simp[]
QED

Theorem ssa_unique_writers:
  ssa_form fn ==> bp_unique_writers (fn_insts fn)
Proof
  simp[bp_unique_writers_def] >>
  metis_tac[allocaRemapSSATheory.ssa_unique_output, inst_output_member]
QED

Definition bp_vars_def:
  bp_vars insts = set (FLAT (MAP (\i. i.inst_outputs) insts))
End

Definition bp_allocs_def:
  bp_allocs insts = IMAGE (\i. Allocation i.inst_id) (set insts)
End

Definition bp_inv_def:
  bp_inv insts r <=>
    bp_map_wf (bp_vars insts) (bp_allocs insts) r /\ bp_history insts r
End

Theorem bp_inv_empty[simp]:
  bp_inv insts FEMPTY
Proof
  simp[bp_inv_def]
QED

Theorem bp_inst_support:
  MEM i insts ==>
  (!out. inst_output i = SOME out ==> out IN bp_vars insts) /\
  Allocation i.inst_id IN bp_allocs insts
Proof
  simp[bp_vars_def, bp_allocs_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[inst_output_member]
QED

Theorem bp_inv_handle:
  bp_unique_writers insts /\ MEM i insts /\ bp_inv insts r ==>
  bp_inv insts (SND (bp_handle_inst r i)) /\
  bp_map_le r (SND (bp_handle_inst r i))
Proof
  simp[bp_inv_def] >> rpt strip_tac
  >- (irule bp_handle_inst_wf >> metis_tac[bp_inst_support])
  >- (irule bp_handle_inst_history >> metis_tac[])
  >> irule bp_handle_inst_growth >> metis_tac[]
QED

Theorem bp_inv_block:
  !is r. bp_unique_writers insts /\ EVERY (\i. MEM i insts) is /\ bp_inv insts r ==>
    bp_inv insts (SND (bp_process_block r is)) /\
    bp_map_le r (SND (bp_process_block r is))
Proof
  Induct >- simp[bp_process_block_def] >> rpt gen_tac >> simp[] >> strip_tac >>
  drule_all bp_inv_handle >> strip_tac >>
  first_x_assum (qspec_then `SND (bp_handle_inst r h)` mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `bp_handle_inst r h` >> rename1 `bp_handle_inst r h = (c,r1)` >>
  Cases_on `bp_process_block r1 is` >>
  gvs[bp_process_block_def] >> metis_tac[bp_map_le_trans]
QED

Theorem bp_find_some_mem:
  !ls P x. FIND P ls = SOME x ==> MEM x ls /\ P x
Proof
  Induct >> simp[FIND_thm] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem bp_inv_pass_aux:
  !order r. ssa_form fn /\ bp_inv (fn_insts fn) r ==>
    bp_inv (fn_insts fn) (SND (bp_one_pass_aux fn r order)) /\
    bp_map_le r (SND (bp_one_pass_aux fn r order))
Proof
  Induct >- simp[bp_one_pass_aux_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >>
  simp[bp_one_pass_aux_def] >>
  rename1 `FIND _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[bp_find_some_mem] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def] >> metis_tac[venomFnInstsProofsTheory.mem_fn_insts_blocks]) >>
  `bp_unique_writers (fn_insts fn)` by metis_tac[ssa_unique_writers] >>
  drule_all bp_inv_block >> strip_tac >>
  first_x_assum (qspec_then `SND (bp_process_block r bb.bb_instructions)` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `bp_process_block r bb.bb_instructions` >>
  rename1 `bp_process_block r bb.bb_instructions = (c,r1)` >>
  Cases_on `bp_one_pass_aux fn r1 order` >>
  gvs[] >> metis_tac[bp_map_le_trans]
QED

Theorem bp_one_pass_inv:
  ssa_form fn /\ bp_inv (fn_insts fn) r ==>
  bp_inv (fn_insts fn) (SND (bp_one_pass fn order r))
Proof
  simp[bp_one_pass_def] >> metis_tac[bp_inv_pass_aux]
QED

Theorem bp_one_pass_growth:
  ssa_form fn /\ bp_inv (fn_insts fn) r ==>
  bp_map_le r (SND (bp_one_pass fn order r))
Proof
  simp[bp_one_pass_def] >> metis_tac[bp_inv_pass_aux]
QED

Theorem bp_inv_rank_bound:
  bp_inv insts r ==>
  bp_map_rank r <= CARD (bp_vars insts) * (1 + 2 * CARD (bp_allocs insts))
Proof
  strip_tac >> irule bp_map_rank_bound >>
  gvs[bp_inv_def, bp_vars_def, bp_allocs_def]
QED

Theorem bp_pass_iterate_fixpoint:
  ssa_form fn ==>
  SND (bp_one_pass fn order
    (df_iterate (\r. SND (bp_one_pass fn order r)) FEMPTY)) =
    df_iterate (\r. SND (bp_one_pass fn order r)) FEMPTY
Proof
  strip_tac >> ho_match_mp_tac df_iterate_fixpoint_orbit >>
  qexistsl_tac [`bp_map_rank`,
    `CARD (bp_vars (fn_insts fn)) * (1 + 2 * CARD (bp_allocs (fn_insts fn)))`,
    `bp_inv (fn_insts fn)`] >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- (rewrite_tac[GREATER_DEF] >> irule bp_map_rank_strict >> metis_tac[bp_one_pass_growth])
  >- (drule bp_inv_rank_bound >> simp[])
  >> metis_tac[bp_one_pass_inv]
QED

Theorem bp_pass_iterate_orbit:
  ssa_form fn ==>
  ?n. df_iterate (\r. SND (bp_one_pass fn order r)) FEMPTY =
      FUNPOW (\r. SND (bp_one_pass fn order r)) n FEMPTY
Proof
  strip_tac >>
  `bp_inv (fn_insts fn)
      (df_iterate (\r. SND (bp_one_pass fn order r)) FEMPTY) /\
   ?n. df_iterate (\r. SND (bp_one_pass fn order r)) FEMPTY =
       FUNPOW (\r. SND (bp_one_pass fn order r)) n FEMPTY` suffices_by metis_tac[] >>
  qspecl_then [`\r. SND (bp_one_pass fn order r)`, `bp_map_rank`,
    `CARD (bp_vars (fn_insts fn)) * (1 + 2 * CARD (bp_allocs (fn_insts fn)))`,
    `\r. bp_inv (fn_insts fn) r /\
         ?n. r = FUNPOW (\r. SND (bp_one_pass fn order r)) n FEMPTY`]
    mp_tac df_iterate_invariant >>
  disch_then (qspec_then `FEMPTY` mp_tac) >>
  impl_tac >- (simp[] >> rpt conj_tac
  >- (rpt strip_tac >> rewrite_tac[GREATER_DEF] >> irule bp_map_rank_strict >>
      metis_tac[bp_one_pass_growth])
  >- (qexists_tac `0` >> simp[])
  >- (rpt strip_tac >> drule bp_inv_rank_bound >> simp[])
  >> rpt strip_tac
  >- metis_tac[bp_one_pass_inv]
  >> qexists_tac `SUC n` >> simp[FUNPOW_SUC]) >> simp[]
QED
