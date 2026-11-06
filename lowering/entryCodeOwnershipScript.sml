Theory entryCodeOwnership
Ancestors
  fragExec loweringShapeDefs venomExecProofs list rich_list

Theorem fn_has_code_endpoint_coverage:
  (!bb. MEM bb (all_blocks se) ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb) ==>
  fn_has_code s se fn
Proof
  strip_tac >> simp[fn_has_code_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[emitted_blocks_def, all_blocks_def] >>
      metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  qexists_tac `<| bb_label := se.cs_current_bb;
                 bb_instructions := se.cs_current_insts |>` >>
  simp[] >>
  first_x_assum (qspec_then
    `<| bb_label := se.cs_current_bb;
        bb_instructions := se.cs_current_insts |>` mp_tac) >>
  simp[all_blocks_def]
QED

Theorem fn_has_code_retained_interval:
  cs_extends a b /\ cs_extends b se /\
  (!bb. MEM bb (all_blocks se) ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb) ==>
  fn_has_code a b fn
Proof
  strip_tac >>
  `fn_has_code a se fn` by metis_tac[fn_has_code_endpoint_coverage] >>
  metis_tac[fn_has_code_split]
QED

Theorem fn_has_code_distinct_endpoint:
  cs_extends a b /\ cs_extends b se /\ fn.fn_blocks = all_blocks se /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) ==>
  fn_has_code a b fn
Proof
  strip_tac >> irule fn_has_code_retained_interval >>
  conj_tac >- simp[] >> qexists_tac `se` >> simp[] >> rpt strip_tac >>
  irule MEM_lookup_block >> simp[]
QED
