Theory dftGasInvBlockInit
Ancestors
  dftGasInvLookupBlock dftGasInvExtraction dftGasOracleDefs
  dftRunRel dftScheduleOrder dftCorrectness dftFrontEquiv venomExecProofs venomWf
  dftBlockSim dftStructural venomExecSemantics venomInst venomState list rich_list

Theorem inv_lookup_common_pseudos[local]:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' ==>
  ?pre xs ys.
    pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    bb.bb_instructions = pre ++ xs /\ bb'.bb_instructions = pre ++ ys /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `dft_block_rel bb bb'` by metis_tac[dft_fn_rel_lookup_order] >>
  `pseudos_prefix bb /\ bb_well_formed bb` by
    (gvs[dft_fn_rel_def, fn_pseudos_prefix_def, wf_function_def, EVERY_MEM]) >>
  drule_all pseudos_prefix_front_decomposition >> strip_tac >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_terminator_def, is_pseudo_def]) >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  qexistsl_tac [`FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions ++ [LAST bb.bb_instructions]`,
    `scheduled`] >>
  simp[EVERY_APPEND, EVERY_FILTER, EVERY_MEM] >>
  conj_tac >- metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC] >>
  gvs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]
QED

Theorem inv_phis_nonpseudo_suffix[local]:
  !pre xs s. EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
    phi_prefix_length (pre ++ xs) = phi_prefix_length pre /\
    eval_phis s (pre ++ xs) = eval_phis s pre
Proof
  Induct >> simp[phi_prefix_length_def, eval_phis_def] >-
    (Cases_on `xs` >> simp[phi_prefix_length_def, eval_phis_def] >>
     rpt strip_tac >> `h.inst_opcode <> PHI` by
       metis_tac[is_pseudo_def] >> simp[]) >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, eval_phis_def] >>
  Cases_on `eval_one_phi s h` >> simp[]
QED

Theorem inv_lookup_phis:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' ==>
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
  eval_phis s bb'.bb_instructions = eval_phis s bb.bb_instructions
Proof
  strip_tac >> drule_all inv_lookup_common_pseudos >> strip_tac >>
  gvs[inv_phis_nonpseudo_suffix]
QED

Theorem inv_block_common_prefix[local]:
  !n s.
  k - s.vs_inst_idx = n /\ s.vs_inst_idx <= k /\
  (!j. j < k ==> get_instruction bb j = get_instruction bb' j) /\
  (!u. u.vs_inst_idx = k /\ ev_block orc p d fuel ctx bb' u = r ==>
       ev_block orc p d fuel ctx bb u = r) /\
  ev_block orc p d fuel ctx bb' s = r ==>
  ev_block orc p d fuel ctx bb s = r
Proof
  Induct >- (rpt strip_tac >> `s.vs_inst_idx = k` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `s.vs_inst_idx < k` by decide_tac >>
  `get_instruction bb s.vs_inst_idx = get_instruction bb' s.vs_inst_idx` by simp[] >>
  qpat_x_assum `ev_block _ _ _ _ _ bb' s = r` mp_tac >>
  once_rewrite_tac[ev_block_def] >>
  Cases_on `get_instruction bb' s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb' s.vs_inst_idx = SOME inst` >>
  Cases_on `ev_step orc p d fuel ctx inst s` >> simp[] >>
  rename1 `ev_step orc p d fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem inv_lookup_block_init_reflect:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  s.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  (r = OK t \/ r = IntRet vals t) /\
  ev_block orc p d fuel ctx bb' s = r ==>
  ev_block orc p d fuel ctx bb s = r
Proof
  strip_tac >> (
  `?pre xs ys.
     FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pre /\
     bb.bb_instructions = pre ++ xs /\ bb'.bb_instructions = pre ++ ys /\
     EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
     EVERY (\i. ~is_pseudo i.inst_opcode) ys` by
    metis_tac[inv_lookup_common_pseudos] >>
  `s.vs_inst_idx <= LENGTH pre` by
    (gvs[inv_phis_nonpseudo_suffix] >> simp[phi_prefix_length_le]) >>
  irule inv_block_common_prefix >>
  qexistsl_tac [`bb'`, `LENGTH pre`, `LENGTH pre - s.vs_inst_idx`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[get_instruction_def, EL_APPEND]) >>
  rpt strip_tac >>
  `u.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by metis_tac[] >>
  drule_at (Pat `ev_block _ _ _ _ _ _ _ = _`) inv_lookup_block_success_reflect >>
  simp[] >> disch_then irule >> metis_tac[])
QED
