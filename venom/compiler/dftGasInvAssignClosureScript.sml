Theory dftGasInvAssignClosure
Ancestors
  dftScheduleOrder
  dftGasInvPendingCut dftDefs

Theorem inv_closed_assign_suffix:
  !front mids rev order.
    ALL_DISTINCT (MAP (\i. i.inst_id) (front ++ mids ++ [rev])) /\
    non_pseudo_defs_before_uses (front ++ mids ++ [rev]) /\
    EVERY (\i. i.inst_opcode = ASSIGN) mids /\
    rev.inst_opcode = REVERT ==>
    inv_closed (front ++ mids ++ [rev]) order
      (dft_eda (front ++ mids ++ [rev]))
      (MAP (\i. i.inst_id) front) (\i. i.inst_opcode = ASSIGN)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[inv_closed_def] >> rpt gen_tac >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  `~is_terminator i.inst_opcode` by
    simp[venomInstTheory.is_terminator_def] >>
  drule_all nonterminator_dft_eda_deps_backward >> strip_tac >>
  rename1 `EL idx (front ++ mids ++ [rev]) = child` >>
  `idx < LENGTH (front ++ mids)` by (fs[] >> decide_tac) >>
  `EL idx (front ++ mids) = child` by
    (gvs[listTheory.EL_APPEND_EQN]) >>
  `MEM child (front ++ mids)` by metis_tac[listTheory.MEM_EL] >>
  `MEM child.inst_id (MAP (\i. i.inst_id) front) \/
   child.inst_opcode = ASSIGN` by
    (qpat_x_assum `MEM child (front ++ mids)` mp_tac >>
     simp[listTheory.MEM_APPEND] >> strip_tac
     >- (disj1_tac >> simp[listTheory.MEM_MAP] >>
         qexists_tac `child` >> simp[]) >>
     disj2_tac >> fs[listTheory.EVERY_MEM]) >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED
