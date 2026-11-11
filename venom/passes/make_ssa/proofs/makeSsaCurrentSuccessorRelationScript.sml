Theory makeSsaCurrentSuccessorRelation
Ancestors
  makeSsaCurrentCopyPrefixRuntime makeSsaCurrentLockstep makeSsaCurrentCutInv
  makeSsaCurrentEdgePrefix o1FrameLockstep makeSsaCurrentDemandDominance list arithmetic

Theorem current_prefix_steps_state_rel:
  !xs k st' done.
  current_prefix_steps fuel C xs st' done /\ st'.vs_inst_idx = k /\
  state_rel (sgs k) st st' /\
  (!j. j < LENGTH xs ==>
    ((EL j xs).inst_opcode = ASSIGN \/ (EL j xs).inst_opcode = NOP) /\
    copy_rename_ok (sgs (k+j)) (EL j xs) (sgs (SUC (k+j)))) ==>
  state_rel (sgs (k + LENGTH xs)) st done
Proof
  Induct >- simp[current_prefix_steps_def] >>
  rpt gen_tac >> pure_rewrite_tac[current_prefix_steps_def] >> strip_tac >>
  `state_rel (sgs (SUC k)) st mid` by
    (irule state_rel_copy >> qexistsl [`C`, `fuel`, `h`, `sgs k`, `st'`] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `!j. j < LENGTH (h::xs) ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  simp[ADD_CLAUSES] >>
  first_x_assum (qspec_then `SUC k` (irule o SRULE [ADD_CLAUSES])) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
      simp[ADD_CLAUSES]) >>
  qexists `mid with vs_inst_idx := SUC k` >> simp[] >> metis_tac[]
QED

Theorem current_enters_block_deterministic[local]:
  enters_block f edge a /\ enters_block f edge b ==> a = b
Proof
  simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >> gvs[]
QED

Theorem current_cut_successor_prefix_relation:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME old_p /\
  current_cut_inv fn A renamed H events p (LENGTH old_p.bb_instructions) t t' /\
  t.vs_prev_bb = SOME p /\ t.vs_current_bb = h ==>
  ?old_h bb' pre.
    lookup_block h fn.fn_blocks = SOME old_h /\
    lookup_block h fn'.fn_blocks = SOME bb' /\
    A h = current_block_annotations old_h pre /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old_h.bb_instructions /\
    !post post' done fuel C.
      enters_block fn t post /\ enters_block fn' t' post' /\
      current_prefix_steps fuel C
        (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
          phi_prefix_length bb'.bb_instructions)
          (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions))
        post' done ==>
      current_cut_inv fn A renamed H events h
        (LENGTH (collect_phis old_h.bb_instructions)) post done /\
      done.vs_inst_idx = LENGTH pre + LENGTH (collect_phis old_h.bb_instructions)
Proof
  strip_tac >> drule_all current_cut_inv_block_entry_prefix >> strip_tac >>
  qexistsl [`old_h`, `bb'`, `pre`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ps. enters_block _ _ ps ==> _` (qspec_then `post'` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `post'' = post` by
    metis_tac[current_enters_block_deterministic] >>
  qpat_x_assum `post'' = post` SUBST_ALL_TAC >>
  `t'.vs_current_bb = h` by fs[current_cut_inv_def, state_rel_def] >>
  `post'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (qpat_x_assum `enters_block _ t' post'` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
     `bb = bb'` by
       (qpat_x_assum `fn' = _` SUBST_ALL_TAC >> fs[]) >>
     qpat_x_assum `bb = bb'` SUBST_ALL_TAC >> simp[]) >>
  qmatch_asmsub_abbrev_tac `current_prefix_steps fuel C copies post' done` >>
  `LENGTH copies = LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
    phi_prefix_length bb'.bb_instructions` by
    (simp[Abbr `copies`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
     mp_tac (Q.SPEC `old_h.bb_instructions` makeSsaCurrentDemandDominanceTheory.current_collect_phis_length) >>
     decide_tac) >>
  `phi_prefix_length bb'.bb_instructions + LENGTH copies =
    LENGTH pre + LENGTH (collect_phis old_h.bb_instructions)` by decide_tac >>
  reverse conj_tac
  >- (drule current_prefix_steps_index >> simp[] >> decide_tac) >>
  simp[current_cut_inv_def] >>
  `state_rel (sgs (phi_prefix_length bb'.bb_instructions + LENGTH copies)) post done`
    suffices_by simp[] >>
  irule current_prefix_steps_state_rel >>
  reverse conj_tac
  >- (qexistsl [`C`, `fuel`, `post'`] >> asm_rewrite_tac[]) >>
  rpt strip_tac >>
  `j + phi_prefix_length bb'.bb_instructions < LENGTH bb'.bb_instructions` by
    (mp_tac (Q.SPEC `old_h.bb_instructions` makeSsaCurrentDemandDominanceTheory.current_collect_phis_length) >> decide_tac) >>
  `EL j copies = EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions` by
    (simp[Abbr `copies`, EL_TAKE, EL_DROP] >> fs[Abbr `copies`]) >>
  simp[] >>
  first_x_assum (qspec_then `phi_prefix_length bb'.bb_instructions + j` mp_tac) >>
  simp[] >> metis_tac[]
QED
