(*
 * frame_sim_rf from a lockstep: when every state a frame of fn' reaches
 * is related by a lockstep R to one a frame of fn reaches, and the
 * position map carries revert-forward instructions of fn to ones of fn',
 * a memory-touching output state outside a revert forwarding is paired
 * (unpaired output states are ASSIGN or NOP, which touch no memory), so
 * its input state touches the same memory, and sits outside a revert
 * forwarding too.
 *)
Theory makeSsaCurrentLockstepRf
Ancestors
  o1FrameLockstep o1PassLift unitMemInv contextCodegenRel codegenRel
  venomInst venomExecProps

Theorem lookup_block_MEM_some[local]:
  !bbs bb. MEM bb bbs ==> ?b. lookup_block bb.bb_label bbs = SOME b
Proof
  Induct >> rw[lookup_block_def, listTheory.FIND_thm] >>
  fs[lookup_block_def]
QED

Theorem lockstep_frame_sim_rf:
  lockstep_sim L C C' fn fn' pos R /\
  (!s0 inst' s'.
     fn_entry_state fn s0 /\ s0.vs_labels = L /\
     frame_reach C' fn' s0 inst' s' ==>
     ?p inst s sg. frame_reach C fn s0 inst s /\
                   R p (inst,s) sg (inst',s')) /\
  (!l bb bb' k.
     lookup_block l fn.fn_blocks = SOME bb /\
     lookup_block l fn'.fn_blocks = SOME bb' /\
     revert_forward_at bb k ==> revert_forward_at bb' (pos l k)) ==>
  frame_sim_rf L C C' fn fn'
Proof
  rw[frame_sim_rf_def] >>
  qpat_x_assum `!s0 inst' s'. _ ==> ?p inst s sg. _`
    (qspecl_then [`s0`, `inst'`, `s'`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `p` by
    (Cases_on `p` >> fs[] >>
     gvs[inst_mem_ranges_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def]) >>
  gvs[] >>
  qexistsl [`inst`, `s`] >> simp[] >>
  drule_all lockstep_paired_mem_ranges >> strip_tac >>
  fs[state_rel_def] >> imp_res_tac execution_frame_fields >>
  conj_tac
  >- (strip_tac >> qpat_x_assum `~in_revert_forward fn' s'` mp_tac >>
      fs[in_revert_forward_def, active_inst_def] >>
      `?b'. lookup_block s.vs_current_bb fn'.fn_blocks = SOME b'` by
        metis_tac[lookup_block_MEM_some] >>
      qexists_tac `b'` >> gvs[] >> first_x_assum irule >> metis_tac[]) >>
  simp[mem_corr_def]
QED
