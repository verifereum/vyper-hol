Theory fnPlanPlaceFnRegion
Ancestors
  stackPlanGen callLayoutDefs venomInst stackPlanTypes list rich_list arithmetic asmToBytecodeProofs codegen asmSem
  codegenRel words symbolResolve

Theorem generate_block_plan_leading_label:
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps') ==>
  ?tail. ops = SOLabel bb.bb_label :: tail
Proof
  simp[generate_block_plan_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem generate_fn_plan_with_cleanup_analyzed_leading_label:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn spill_base ctr =
    SOME (ops, ps') ==>
  ?tail. ops = SOLabel (HD fn.fn_blocks).bb_label :: tail
Proof
  Cases_on `fn.fn_blocks` >-
    simp[generate_fn_plan_with_cleanup_analyzed_def, canonical_param_prefix_def] >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, fn_entry_label_def,
       entry_block_def] >>
  simp[Once generate_fn_plan_aux_def, lookup_block_def, FIND_thm] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule generate_block_plan_leading_label >> strip_tac >> gvs[]
QED

Theorem generate_context_regions_provenance:
  !fns acc out.
  generate_context_regions gen fns acc = SOME out ==>
  LENGTH out.cpa_regions = LENGTH acc.cpa_regions + LENGTH fns /\
  TAKE (LENGTH acc.cpa_regions) out.cpa_regions = acc.cpa_regions /\
  (!i. i < LENGTH fns ==>
    ?ctr ps. gen (EL i fns)
      (EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_spill_base ctr =
      SOME ((EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_plan, ps))
Proof
  Induct_on `fns` >- simp[generate_context_regions_def] >>
  rpt gen_tac >>
  simp[Once generate_context_regions_def, AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_context_regions gen fns next` >>
  first_x_assum drule >> strip_tac >>
  gvs[Abbr `next`, LENGTH_SNOC] >>
  conj_tac >-
    (qpat_x_assum `TAKE (SUC _) _ = _`
       (mp_tac o Q.AP_TERM `TAKE (LENGTH acc.cpa_regions)`) >>
     simp[TAKE_TAKE, TAKE_SNOC, MIN_DEF]) >>
  Cases_on `i` >> simp[] >-
    (qpat_x_assum `TAKE (SUC _) _ = _` (mp_tac o Q.AP_TERM `EL (LENGTH acc.cpa_regions)`) >>
     simp[EL_TAKE, EL_LENGTH_SNOC] >> strip_tac >>
     qexistsl_tac [`acc.cpa_label_counter`, `ps`] >> simp[]) >>
  strip_tac >> first_x_assum drule >> simp[ADD_CLAUSES]
QED

Theorem generate_context_plan_with_provenance:
  generate_context_plan_with gen ctx = SOME cp ==>
  LENGTH cp.cp_regions = LENGTH ctx.ctx_functions /\
  (!i. i < LENGTH ctx.ctx_functions ==>
    ?ctr ps. gen (EL i ctx.ctx_functions)
      (EL i cp.cp_regions).sr_spill_base ctr =
      SOME ((EL i cp.cp_regions).sr_plan, ps))
Proof
  simp[generate_context_plan_with_def, AllCaseEqs()] >> strip_tac >>
  drule generate_context_regions_provenance >>
  gvs[finish_context_plan_def]
QED

Theorem context_region_leading_label:
  generate_context_plan ctx = SOME cp /\
  i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
  EL i cp.cp_regions = r ==>
  i < LENGTH cp.cp_regions /\
  ?tail. r.sr_plan = SOLabel (HD fn.fn_blocks).bb_label :: tail
Proof
  simp[generate_context_plan_def] >> rpt strip_tac >>
  drule generate_context_plan_with_provenance >> strip_tac >-
    gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[generate_fn_plan_with_cleanup_def] >>
  drule generate_fn_plan_with_cleanup_analyzed_leading_label >> simp[]
QED

Theorem asm_symbols_ok_label_suffix:
  asm_symbols_ok (pre ++ AsmLabel lbl :: rest) ==>
  !j. j < LENGTH rest ==>
    EL j rest <> AsmLabel lbl /\
    (!l. EL j rest = AsmDataHeader l ==> l <> lbl)
Proof
  strip_tac >> drule asm_symbols_ok_distinct >>
  simp[asm_defined_symbols_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >>
  `MEM (EL j rest) rest` by simp[EL_MEM] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[asm_defined_symbols_def, MEM]
QED

Theorem labelled_asm_slice_placed:
  !prog pre body post lbl.
  prog = pre ++ (AsmLabel lbl :: body) ++ post /\ asm_symbols_ok prog ==>
  ?off.
    FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
    off < dimword (:256) /\
    FLOOKUP (build_offset_to_pc prog) off = SOME (LENGTH pre) /\
    asm_block_at prog (LENGTH pre) (AsmLabel lbl :: body)
Proof
  rpt strip_tac >> gvs[] >>
  rename1 `asm_block_at _ _ (AsmLabel lbl :: tail)` >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qexists_tac `asm_pc_to_offset (pre ++ AsmLabel lbl :: (tail ++ post)) (LENGTH pre)` >>
  conj_tac >-
    (drule asm_symbols_ok_label_suffix >> strip_tac >>
     irule label_offset_consistent_proof >>
     simp[EL_APPEND_EQN] >> rpt strip_tac >>
     first_x_assum (qspec_then `PRE (j - LENGTH pre)` mp_tac) >>
     gvs[EL_CONS]) >>
  conj_tac >-
    (gvs[asm_pc_to_offset_def, TAKE_APPEND, asm_symbols_ok_def] >>
     gvs[SUM_APPEND, asm_inst_size_def, dimword_def] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  conj_tac >-
    (irule offset_to_pc_inverse_proof >>
     simp[EL_APPEND_EQN, asm_inst_size_def]) >>
  simp[asm_block_at_def, EL_APPEND_EQN] >>
  rpt strip_tac >> Cases_on `j` >> simp[EL_APPEND_EQN]
QED
