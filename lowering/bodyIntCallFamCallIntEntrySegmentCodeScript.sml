Theory bodyIntCallFamCallIntEntrySegmentCode
Ancestors
  compileEnv fragExec vyperCompiler loweringShapeDefs venomExecProps

Theorem intcall_segment_contains_code:
  !a old b c lbl seg rb rc.
    new_block lbl a = (old,b) /\ cs_extends b c /\
    all_blocks c = all_blocks a ++ seg /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) seg) ==>
    fn_has_code b c (mk_internal_function lbl seg rb rc)
Proof
  rpt gen_tac >>
  simp[new_block_def, cs_extends_def, all_blocks_def] >>
  strip_tac >> gvs[] >>
  simp[fn_has_code_def, emitted_blocks_def, mk_internal_function_metadata] >>
  conj_tac
  >- (rpt strip_tac >> irule MEM_lookup_block >> simp[] >>
      qpat_x_assum `MEM bb (TAKE _ _)` mp_tac >>
      simp[arithmeticTheory.ADD1] >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                       rich_listTheory.TAKE_LENGTH_APPEND] >> simp[]) >>
  qexists_tac `<|bb_label := c.cs_current_bb;
                bb_instructions := c.cs_current_insts|>` >>
  simp[] >> irule MEM_lookup_block >> simp[]
QED
