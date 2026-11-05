Theory fnAliasInvOrdering
Ancestors
  fnAliasInvAvailability removeUnusedSsaProofs venomExecProofs
  venomWf venomExecProps list rich_list

Theorem alias_ssa_definition_position:
  wf_function fn /\ ssa_form fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block m fn.fn_blocks = SOME cc /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH cc.bb_instructions /\
  MEM v (inst_defs (EL i bb.bb_instructions)) /\
  MEM v (inst_defs (EL j cc.bb_instructions)) ==> l = m /\ i = j
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ MEM cc fn.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  gvs[venomInstTheory.inst_defs_def] >>
  `bb = cc` by metis_tac[ssa_unique_output_block, EL_MEM] >>
  gvs[] >> conj_tac
  >- metis_tac[lookup_block_label] >>
  metis_tac[removeUnusedProofsTheory.ssa_form_no_dup_in_block]
QED

Theorem alias_path_first_visit_prefix:
  !path fn l. is_fn_path fn path /\ MEM l path ==>
    ?pre. is_fn_path fn (pre ++ [l]) /\
      HD (pre ++ [l]) = HD path /\ ~MEM l pre
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h = l`
  >- (qexists_tac `[]` >> simp[is_fn_path_def]) >>
  `MEM l path` by fs[] >>
  `is_fn_path fn path` by
    (Cases_on `path` >> fs[is_fn_path_def]) >>
  qpat_x_assum `!fn l. _` (qspecl_then [`fn`,`l`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `h::pre` >> simp[] >>
  Cases_on `path` >> gvs[is_fn_path_def] >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem alias_reachable_first_visit:
  fn_reachable fn l ==>
  ?path. is_fn_path fn path /\ path <> [] /\
    (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
    LAST path = l /\ (!k. k < LENGTH path - 1 ==> EL k path <> l)
Proof
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM l path` by
    (qpat_x_assum `LAST path = l` (SUBST1_TAC o SYM) >>
     simp[LAST_EL] >> irule EL_MEM >> Cases_on `path` >> gvs[]) >>
  drule_all alias_path_first_visit_prefix >> strip_tac >>
  qexists_tac `pre ++ [l]` >> simp[] >>
  rpt strip_tac >> gvs[EL_APPEND_EQN] >>
  metis_tac[EL_MEM]
QED

Theorem alias_definition_not_available:
  wf_function fn /\ ssa_form fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  MEM v (inst_defs (EL i bb.bb_instructions)) ==>
  ~alias_path_available fn l i v
Proof
  strip_tac >> drule alias_reachable_first_visit >> strip_tac >>
  rewrite_tac[alias_path_available_def] >> strip_tac >>
  qpat_x_assum `!p. is_fn_path fn p /\ _ ==> _`
    (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`?j. j < LENGTH bb'.bb_instructions /\
          EL j bb'.bb_instructions = inst` by metis_tac[MEM_EL] >>
      `l = EL k path` by metis_tac[alias_ssa_definition_position] >>
      metis_tac[]) >>
  gvs[] >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  `i = j` by metis_tac[alias_ssa_definition_position] >> gvs[]
QED
