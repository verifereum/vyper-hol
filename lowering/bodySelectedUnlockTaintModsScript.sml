(* Linked post-unlock storage and immutable-prefix taint. *)
Theory bodySelectedUnlockTaintMods
Ancestors
  bodyFullShadowBodyInv bodyFullPostsMods bodyPtrDefs stmtSimReturn
  bodyInvSplit loweringStateRelDefs vyperState venomState
  finite_map pred_set list

Theorem selected_unlock_exit_taint_mods:
  dead_lo_ok_mods H D lo ce cx /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     FST (SND (SND ce.ce_nonreentrant))) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
  tf.t_imm = tn.t_imm /\ tf.t_mem = tn.t_mem /\
  ghost_inv_at_mods D lo d ce cx ee G tn s ==>
  stor_taint_ok_at D tf (return_unlock_state ce s) /\
  (!i. i < lo /\ i IN tf.t_mem ==>
    imm_section_dead_mods ce
      (mem_bytes_at 0 lo (return_unlock_state ce s).vs_memory) i)
Proof
  rpt strip_tac >> fs[ghost_inv_at_mods_def] >> simp[]
  >- (qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
      Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
      gvs[return_unlock_state_def, tstore_def, dead_lo_ok_mods_def,
          stor_taint_ok_at_def, combinTheory.APPLY_UPDATE_THM] >>
      irule SUBSET_TRANS >> qexists_tac `tn.t_trans` >> simp[] >>
      Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
      gvs[sourceUnitExecutionTheory.cx_dead_def, SUBSET_DEF] >>
      rpt strip_tac >> rename1 `p IN tn.t_trans` >> PairCases_on `p` >> fs[] >>
      irule accountsRelPropsTheory.storage_dead_update_zero >>
      qpat_x_assum `!x. x IN tn.t_trans ==> _`
        (qspec_then `(p0,p1)` mp_tac) >> simp[])
  >> first_x_assum irule >> metis_tac[]
QED
