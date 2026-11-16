Theory dftPacketPseudoAdvance
Ancestors
  dftPacketEntryReplay dftRunRel dftIndexedExec venomInst venomState list rich_list

Theorem dft_packet_pseudo_prefix_advance:
  EVERY (\i. is_pseudo i.inst_opcode) ps /\ l <= k /\ k < LENGTH ps /\
  FOLDR (dft_exec_cons f C) OK (DROP l (TAKE k ps)) s0 = OK s /\
  s.vs_inst_idx = k /\ step_inst f C (EL k ps) s = OK u ==>
  !g D gs. FOLDR (dft_exec_cons g D) OK (DROP l (TAKE (SUC k) ps))
    (s0 with vs_gas_readings := gs) =
    OK ((u with vs_inst_idx := SUC k) with vs_gas_readings := gs)
Proof
  strip_tac >>
  `l - k = 0` by simp[] >>
  `DROP l (TAKE (SUC k) ps) = DROP l (TAKE k ps) ++ [EL k ps]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, DROP_APPEND, LENGTH_TAKE] >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP l (TAKE k ps))` by
    simp[EVERY_DROP, EVERY_TAKE] >>
  `!op. is_pseudo op ==> ~is_terminator op` by
    (Cases >> simp[is_pseudo_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP l (TAKE k ps)) /\
   ~is_terminator (EL k ps).inst_opcode` by
    gvs[EVERY_MEM, EL_MEM] >>
  `FOLDR (dft_exec_cons f C) OK (DROP l (TAKE (SUC k) ps)) s0 =
     OK (u with vs_inst_idx := SUC k)` by
    (asm_rewrite_tac[FOLDR_APPEND] >>
     simp[Once dft_exec_prefix_continue] >>
     simp[dft_exec_cons_def]) >>
  rpt gen_tac >> irule dft_packet_pseudo_fold_gas >>
  simp[EVERY_DROP, EVERY_TAKE] >> metis_tac[]
QED
