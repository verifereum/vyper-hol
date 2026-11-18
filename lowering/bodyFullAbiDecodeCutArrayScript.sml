Theory bodyFullAbiDecodeCutArray
Ancestors
  bodyFullAbiDecodeArrayCases bodyFullAbiDecodeCutPath
  bodyFullAbiDecodeCutLayout bodyFullAbiDecodeCutEntryPhase
  exprSimAbiGasBridge exprSimAbiDecodeSiteCoverage exprLoweringProps rich_list
Libs
  bodyFullAbiDecodeCutArraySyntaxLib bodyFullAbiDecodeCutPathLib

Theorem array_cut_bind[local]:
  ^(specialize_array_cut array_bind_rule)
Proof
  simp_tac pure_ss [BETA_THM] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "prefix") (mk_asm "suffix")) >>
  rpt gen_tac >> strip_tac >>
  asm "prefix" (qspec_then `u` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [venomExecSemanticsTheory.exec_result_distinct,
    venomExecSemanticsTheory.exec_result_11] >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  irule (BETA_RULE abi_decode_cut_prefix_bind) >> qexists `w` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  asm "suffix" (qspec_then `w` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem array_cut_revert[local]:
  ^(specialize_array_cut array_revert_rule)
Proof
  simp_tac bool_ss [BETA_THM, venomExecSemanticsTheory.exec_result_distinct,
    venomExecSemanticsTheory.exec_result_11]
QED

(* Prefix and index initialization precede the first close.  The full
   layout supplies PHI freedom and the unchanged slice of their instructions. *)
Theorem array_cut_entry[local]:
  ^array_cut_layout ==> ^array_cut_straight_rule
Proof
  simp_tac pure_ss [BETA_THM] >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_start a /\ b.cs_blocks = cut_start.cs_blocks` by
    metis_tac[cs_extends_trans] >>
  `a.cs_current_bb = cut_start.cs_current_bb` by
    (qpat_assum `cs_extends cut_start a` (mp_tac o MATCH_MP frag_extends_emitted_shape) >>
     simp[emitted_blocks_def]) >>
  `!i. MEM i (emitted_insts a b) ==> i.inst_opcode <> PHI` by
    (`frag_code a b = emitted_insts a b` by
       simp[frag_code_same_blocks, emitted_insts_def] >>
     rpt strip_tac >>
     `MEM i (frag_code cut_start b)` by
       (irule abi_decode_frag_code_right_inclusion >> qexists `a` >> simp[]) >>
     `MEM i (frag_code cut_start cut_finish)` by
       (irule abi_decode_frag_code_left_inclusion >> qexists `b` >>
        simp[] >> metis_tac[cs_extends_trans]) >>
     qpat_x_assum `frag_ops_free _ _`
       (qspec_then `i` mp_tac o REWRITE_RULE [frag_ops_free_def, EVERY_MEM]) >> simp[]) >>
  `?shadow. lookup_block L cut_observer.fn_blocks = SOME shadow /\
    isPREFIX (emitted_insts a b) (DROP (LENGTH a.cs_current_insts) shadow.bb_instructions)` by
    (qpat_x_assum `cut_observer = _` SUBST_ALL_TAC >>
     drule_all abi_decode_cut_entry_slice >>
     disch_then (qx_choose_then `orig` (qx_choose_then `shadow` strip_assume_tac)) >>
     qexists `shadow` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
              ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    fs[EVERY_MEM] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_current_bb = L` by fs[] >>
  mp_tac (Q.INST [`obs` |-> `cut_observer`] (BETA_RULE abi_decode_cut_entry_phase)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[]
QED

(* The constructor premise is the length-loop motive at the compiled suffix. *)
Theorem abi_decode_cut_array_clause:
  ^array_cut_layout ==> ^array_cut_clause
Proof
  disch_tac >> mp_tac array_cut_entry >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  mp_tac (Q.INST [`observe_array` |-> `T`, `observe_phase` |-> `^array_shadow`]
    abi_decode_array_guarded_decorated) >>
  (impl_tac >- (disch_tac >> first_assum ACCEPT_TAC)) >>
  (impl_tac >- (disch_tac >> ACCEPT_TAC array_cut_bind)) >>
  (impl_tac >- (disch_tac >> ACCEPT_TAC array_cut_revert)) >>
  disch_then ACCEPT_TAC
QED
