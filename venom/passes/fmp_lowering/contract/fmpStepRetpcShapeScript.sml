(* FmpLowering preserves the return-PC shape (retpc_shape_ok), the
   fn_shape_ok conjunct about how RET reaches the caller's return PC. *)
Theory fmpStepRetpcShape
Ancestors
  fmpStepStructural fmpStepLayout fmpStepOpaque fmpStepRestrictions
  fmpStepCallChecks
  fmpLowerProps fmpWfDefs venomWf venomInst unitShapeDefs o1PassContract
  venomFnScheduleRunner irSupply list rich_list

Theorem fn_cfg_edge_successor_map[local]:
  EVERY bb_well_formed fn.fn_blocks ==>
  (fn_cfg_edge fn a b <=>
   ?succs. MEM (a,succs)
     (MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions)))
       fn.fn_blocks) /\ MEM b succs)
Proof
  simp[fn_cfg_edge_def, MEM_MAP] >> strip_tac >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[EVERY_MEM, bb_well_formed_successors_mem]
QED

Theorem fmp_lower_function_cfg_edge:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  fn_cfg_edge fn' = fn_cfg_edge fn
Proof
  strip_tac >>
  `wf_function fn /\ first_block_no_phi fn` by
    gvs[o1_fn_shape_def] >>
  drule_all fmp_lower_function_blocks_well_formed >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by gvs[wf_function_def, EVERY_MEM] >>
  drule fmp_lower_function_preserves_successors >> strip_tac >>
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  asm_simp_tac (srw_ss()) [fn_cfg_edge_successor_map]
QED

Theorem fmp_lower_function_reachable:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  fn_reachable fn' = fn_reachable fn
Proof
  strip_tac >> drule_all fmp_lower_function_cfg_edge >> strip_tac >>
  drule fmp_lower_function_preserves_entry_label >> strip_tac >>
  simp[FUN_EQ_THM, fn_reachable_def]
QED

Theorem fmp_lower_function_reachable_preds:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  reachable_preds fn' = reachable_preds fn
Proof
  strip_tac >> drule_all fmp_lower_function_cfg_edge >> strip_tac >>
  drule_all fmp_lower_function_reachable >> strip_tac >>
  drule fmp_lower_function_preserves_labels >> strip_tac >>
  gvs[fn_labels_def] >> simp[FUN_EQ_THM, reachable_preds_def]
QED

Theorem fmp_lower_function_reachable_inst:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  reachable_inst fn' = reachable_inst fn
Proof
  strip_tac >> drule_all fmp_lower_function_reachable_preds >>
  simp[FUN_EQ_THM, reachable_inst_def]
QED

Theorem fmp_lower_inst_assign_preserved:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  inst.inst_opcode = ASSIGN ==> out = [inst]
Proof
  strip_tac >> gvs[fmpLowerDefsTheory.fmp_lower_inst_ordinary]
QED

Theorem fmp_lower_indexed_assign_preserved:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ MEM inst insts /\ inst.inst_opcode = ASSIGN ==>
  MEM inst out
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def] >>
  rpt gen_tac >>
  Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmpLowerDefsTheory.fmp_lower_indexed_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all fmp_lower_inst_assign_preserved >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem fmp_make_root_layout_seed_correspondence:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST newpc) =
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST oldpc)
Proof
  strip_tac >> Cases_on `oldpc` >>
  gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs(),
      callLayoutDefsTheory.OPTION_TO_LIST_def, mk_inst_def,
      fmpLowerDefsTheory.set_param_index_def]
QED

Theorem fmp_lower_inst_return_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
  MEM inst.inst_opcode [RET; RETFMP; DRET] /\
  LAST j.inst_operands = LAST inst.inst_operands /\
  (NULL j.inst_operands <=> NULL inst.inst_operands)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
  Cases_on `inst.inst_opcode = DRET`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  gvs[fmpLowerDefsTheory.fmp_lower_inst_ordinary, AllCaseEqs()]
QED

Theorem fmp_lower_inst_return_tail:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM j.inst_opcode [RET; RETFMP; DRET] /\
  inst.inst_operands = front ++ [Var x] ==>
  ?front'. j.inst_operands = front' ++ [Var x]
Proof
  strip_tac >> drule_all fmp_lower_inst_return_origin >> strip_tac >>
  gvs[] >> qexists `FRONT j.inst_operands` >>
  metis_tac[APPEND_FRONT_LAST, NULL_EQ]
QED

Theorem fmp_lower_blocks_label_origin:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  MEM bb out /\ MEM j bb.bb_instructions ==>
  (?src i s0 chunk s1. MEM src bbs /\ src.bb_label = bb.bb_label /\
     MEM i src.bb_instructions /\
     fmp_lower_inst infos ctx runner s0 i = SOME (chunk,s1) /\ MEM j chunk) \/
  (?point base id. MEM (point,base) restores /\
     j = mk_inst id ASSIGN [Var base] [runner])
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmpLowerDefsTheory.fmp_lower_blocks_def] >>
  simp[fmpLowerDefsTheory.fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all fmpStepRewriteTheory.fmp_lower_indexed_origin >>
      strip_tac >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  drule fmpLowerIndexedPropsTheory.fmp_lower_indexed_leftover >>
  strip_tac >> metis_tac[]
QED

Theorem fmp_lower_blocks_assign_preserved:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  MEM bb bbs /\ MEM inst bb.bb_instructions /\ inst.inst_opcode = ASSIGN ==>
  ?bb'. MEM bb' out /\ bb'.bb_label = bb.bb_label /\
        MEM inst bb'.bb_instructions
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmpLowerDefsTheory.fmp_lower_blocks_def] >>
  simp[fmpLowerDefsTheory.fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all fmp_lower_indexed_assign_preserved >> strip_tac >>
      qexists `bb with bb_instructions := insts` >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  qexists `bb'` >> simp[]
QED

Theorem fmp_lower_blocks_retained_location:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  MEM op [GAS; PHI; PARAM; RETPC_PARAM; FMP_PARAM] /\ inst.inst_opcode = op ==>
  ((?bb. MEM bb out /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions) <=>
   (?bb. MEM bb bbs /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions))
Proof
  strip_tac >> drule_all fmpStepRewriteTheory.fmp_lower_blocks_retained_opcodes >>
  disch_then (mp_tac o AP_TERM
    ``\xs : (string # instruction list) list.
       ?is. MEM (lbl,is) xs /\ MEM inst is``) >>
  simp[MEM_MAP, MEM_FILTER, PULL_EXISTS] >> metis_tac[]
QED

Theorem fmp_install_root_ordinary_location:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  EVERY (\i. i.inst_opcode = PARAM) users /\
  (!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST root) ==>
       MEM i.inst_opcode [INITIAL_FMP; FMP_PARAM]) /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s)
    (entry::rest) = SOME (out,s') /\
  ~MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP; FMP_PARAM] ==>
  ((?bb. MEM bb out /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions) <=>
   (?bb. MEM bb (entry::rest) /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions))
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  `~MEM inst users /\ ~MEM inst (OPTION_TO_LIST oldpc) /\
   ~MEM inst (OPTION_TO_LIST newpc) /\ ~MEM inst (OPTION_TO_LIST root)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem fmp_install_checked_root_ordinary_location:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  ~MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP; FMP_PARAM] ==>
  ((?bb. MEM bb out /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions) <=>
   (?bb. MEM bb blocks /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions))
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     metis_tac[fmpLowerPropsTheory.split_fmp_entry_retpc_opcode]) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[] >> pure_once_rewrite_tac[GSYM MEM] >>
  irule fmp_install_root_ordinary_location >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >> metis_tac[]
QED

Theorem fmp_lower_function_phi_location:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ inst.inst_opcode = PHI ==>
  ((?bb. MEM bb fn'.fn_blocks /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions) <=>
   (?bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ MEM inst bb.bb_instructions))
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP; FMP_PARAM]` by simp[] >>
  drule_all fmp_install_checked_root_ordinary_location >> strip_tac >>
  drule fmp_lower_blocks_retained_location >> simp[]
QED

Theorem fmp_lower_function_assign_location:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ inst.inst_opcode = ASSIGN /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  ?bb'. MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label /\
        MEM inst bb'.bb_instructions
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >~ [`fn.fn_fmp_signature = SOME sig`]
  >- (qexists `bb` >> simp[]) >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def]
  >- (qexists `bb` >> simp[]) >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP; FMP_PARAM]` by simp[] >>
  drule_all fmp_install_checked_root_ordinary_location >> strip_tac >>
  drule_all fmp_lower_blocks_assign_preserved >> metis_tac[]
QED

Theorem fmp_lower_blocks_return_origin:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  MEM bb out /\ MEM j bb.bb_instructions /\
  MEM j.inst_opcode [RET; RETFMP; DRET] ==>
  ?src inst. MEM src bbs /\ src.bb_label = bb.bb_label /\
    MEM inst src.bb_instructions /\ MEM inst.inst_opcode [RET; RETFMP; DRET] /\
    LAST j.inst_operands = LAST inst.inst_operands /\
    (NULL j.inst_operands <=> NULL inst.inst_operands)
Proof
  strip_tac >> drule_all fmp_lower_blocks_label_origin >> strip_tac
  >- (drule_all fmp_lower_inst_return_origin >> metis_tac[]) >>
  gvs[mk_inst_def]
QED

Theorem fmp_lower_function_return_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  MEM bb fn'.fn_blocks /\ MEM j bb.bb_instructions /\
  MEM j.inst_opcode [RET; RETFMP; DRET] ==>
  ?src inst. MEM src fn.fn_blocks /\ src.bb_label = bb.bb_label /\
    MEM inst src.bb_instructions /\ MEM inst.inst_opcode [RET; RETFMP; DRET] /\
    LAST j.inst_operands = LAST inst.inst_operands /\
    (NULL j.inst_operands <=> NULL inst.inst_operands)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >>~- ([`fn.fn_fmp_signature = SOME sig`],
         qexistsl [`bb`, `j`] >> simp[]) >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def]
  >>~- ([`~info.fi_needs_fmp`, `~info.fi_publishes_fmp`],
         qexistsl [`bb`, `j`] >> simp[]) >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `~MEM j.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP; FMP_PARAM]` by simp[] >>
  drule_all fmp_install_checked_root_ordinary_location >> strip_tac >>
  `?b. MEM b blocks /\ b.bb_label = bb.bb_label /\ MEM j b.bb_instructions` by
    (first_x_assum (qspec_then `bb.bb_label` (mp_tac o iffLR)) >>
     (impl_tac >- (qexists `bb` >> simp[])) >> simp[]) >>
  `MEM j.inst_opcode [RET; RETFMP; DRET]` by simp[] >>
  drule_all fmp_lower_blocks_return_origin >> simp[]
QED

Theorem fmp_install_root_seed_location:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  EVERY (\i. i.inst_opcode = PARAM) users /\
  (!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST root) ==>
       MEM i.inst_opcode [INITIAL_FMP; FMP_PARAM]) /\
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST newpc) =
  MAP (\i. (i.inst_id,i.inst_outputs)) (OPTION_TO_LIST oldpc) /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s)
    (entry::rest) = SOME (out,s') ==>
  ((?bb i. MEM bb out /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs) <=>
   (?bb i. MEM bb (entry::rest) /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs))
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  `(!i. MEM i users ==> i.inst_opcode <> RETPC_PARAM) /\
   (!i. MEM i (OPTION_TO_LIST root) ==> i.inst_opcode <> RETPC_PARAM)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `(?i. MEM i (OPTION_TO_LIST newpc) /\ i.inst_id = id /\ i.inst_outputs = outputs) <=>
   (?i. MEM i (OPTION_TO_LIST oldpc) /\ i.inst_id = id /\ i.inst_outputs = outputs)` by
    (qpat_x_assum `MAP _ _ = MAP _ _`
      (mp_tac o AP_TERM ``\xs : (num # string list) list. MEM (id,outputs) xs``) >>
     simp[MEM_MAP, EQ_SYM_EQ, AC CONJ_ASSOC CONJ_COMM]) >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem fmp_install_checked_root_seed_location:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) ==>
  ((?bb i. MEM bb out /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs) <=>
   (?bb i. MEM bb blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs))
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule_all fmp_make_root_layout_seed_correspondence >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     metis_tac[fmpLowerPropsTheory.split_fmp_entry_retpc_opcode]) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[] >> pure_once_rewrite_tac[GSYM MEM] >>
  irule fmp_install_root_seed_location >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >> metis_tac[]
QED

Theorem fmp_lower_function_seed_location:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  ((?bb i. MEM bb fn'.fn_blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs) <=>
   (?bb i. MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions /\
       i.inst_opcode = RETPC_PARAM /\ i.inst_id = id /\ i.inst_outputs = outputs))
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_checked_root_seed_location >> strip_tac >>
  `!i. i.inst_opcode = RETPC_PARAM ==>
    ((?bb. MEM bb blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions) <=>
     (?bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions))` by
    (rpt strip_tac >> drule fmp_lower_blocks_retained_location >> simp[]) >>
  metis_tac[]
QED

Theorem fmp_lower_function_reachable_phi:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  inst.inst_opcode = PHI ==>
  (MEM inst (fn_insts (reachable_fn fn')) <=>
   MEM inst (fn_insts (reachable_fn fn)))
Proof
  strip_tac >> drule_all fmp_lower_function_reachable >> strip_tac >>
  drule_all fmp_lower_function_reachable_inst >> strip_tac >>
  `!i lbl. i.inst_opcode = PHI ==>
    ((?bb. MEM bb fn'.fn_blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions) <=>
     (?bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ MEM i bb.bb_instructions))` by
    (rpt strip_tac >> drule_all fmp_lower_function_phi_location >> simp[]) >>
  simp[MEM_reachable_fn_insts] >> eq_tac >> rpt strip_tac >>
  `i.inst_opcode = PHI` by metis_tac[reachable_inst_fields] >>
  first_x_assum (qspecl_then [`i`, `bb.bb_label`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem fmp_lower_function_reachable_assign:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  inst.inst_opcode = ASSIGN /\ MEM inst (fn_insts (reachable_fn fn)) ==>
  MEM inst (fn_insts (reachable_fn fn'))
Proof
  strip_tac >> drule_all fmp_lower_function_reachable >> strip_tac >>
  gvs[MEM_reachable_fn_insts] >>
  `i.inst_opcode = ASSIGN` by metis_tac[reachable_inst_fields] >>
  gvs[reachable_inst_def] >>
  drule_all fmp_lower_function_assign_location >> strip_tac >>
  qexistsl [`bb'`, `i`] >> simp[reachable_inst_def]
QED

Theorem fmp_lower_function_reachable_seed:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  ((?i. MEM i (fn_insts (reachable_fn fn')) /\ i.inst_opcode = RETPC_PARAM /\
        i.inst_id = id /\ i.inst_outputs = outputs) <=>
   (?i. MEM i (fn_insts (reachable_fn fn)) /\ i.inst_opcode = RETPC_PARAM /\
        i.inst_id = id /\ i.inst_outputs = outputs))
Proof
  strip_tac >> drule_all fmp_lower_function_reachable >> strip_tac >>
  drule fmp_lower_function_seed_location >> strip_tac >>
  simp[MEM_reachable_fn_insts, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac >>
  gvs[reachable_inst_fields] >>
  gvs[reachable_inst_def] >>
  rename1 `MEM seed bb.bb_instructions` >>
  first_x_assum (qspecl_then [`seed.inst_outputs`, `bb.bb_label`, `seed.inst_id`] mp_tac) >>
  simp[SF CONJ_ss] >> strip_tac >> metis_tac[]
QED

Theorem fmp_lower_function_reachable_return_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  MEM j (fn_insts (reachable_fn fn')) /\ MEM j.inst_opcode [RET; RETFMP; DRET] ==>
  ?inst. MEM inst (fn_insts (reachable_fn fn)) /\
    MEM inst.inst_opcode [RET; RETFMP; DRET] /\
    LAST j.inst_operands = LAST inst.inst_operands /\
    (NULL j.inst_operands <=> NULL inst.inst_operands)
Proof
  strip_tac >> drule_all fmp_lower_function_reachable >> strip_tac >>
  gvs[MEM_reachable_fn_insts] >>
  gvs[reachable_inst_fields, reachable_inst_def] >>
  drule_at Any fmp_lower_function_return_origin >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists `inst` >> simp[] >> qexistsl [`src`, `inst`] >> simp[]
QED

Theorem fmp_lower_inst_retpc_writer:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM x j.inst_outputs /\ MEM x s.irs_used_vars /\ x <> runner /\
  (MEM x inst.inst_outputs ==> MEM inst.inst_opcode [RETPC_PARAM; ASSIGN; PHI]) ==>
  j = inst /\ MEM inst.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def] >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs(), MEM_APPEND] >>
      Cases_on `info.fi_publishes_fmp` >> gvs[]) >>
  gvs[fmpLowerDefsTheory.fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem fmp_lower_indexed_retpc_writer:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ ir_supply_inst_ok s /\
  MEM x s.irs_used_vars /\ x <> runner /\
  (!i. MEM i insts /\ MEM x i.inst_outputs ==>
       MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]) ==>
  MEM j out /\ MEM x j.inst_outputs ==>
  MEM j insts /\ MEM j.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts` >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def] >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule_all fmpStepRewriteTheory.fmp_emit_restores_supply >> strip_tac >>
  drule_all fmpStepRewriteTheory.fmp_lower_inst_supply >> strip_tac >>
  `MEM x s0.irs_used_vars /\ MEM x s1.irs_used_vars` by
    gvs[dretDesugarProofsTheory.dret_supply_extends_def] >>
  gvs[MEM_APPEND]
  >- (drule_all fmpStepRewriteTheory.fmp_emit_restores_assign_origin >>
      strip_tac >> gvs[mk_inst_def])
  >- (`MEM x h.inst_outputs ==> MEM h.inst_opcode [RETPC_PARAM; ASSIGN; PHI]` by
        (simp[] >> metis_tac[]) >>
      drule_all fmp_lower_inst_retpc_writer >> simp[]) >>
  first_x_assum drule >> simp[] >> disch_then drule >> simp[] >>
  metis_tac[]
QED

Theorem fmp_lower_blocks_retpc_writer:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\ ir_supply_inst_ok s /\
  MEM x s.irs_used_vars /\ x <> runner /\
  (!bb i. MEM bb bbs /\ MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]) ==>
  MEM bb' out /\ MEM j bb'.bb_instructions /\ MEM x j.inst_outputs ==>
  ?bb. MEM bb bbs /\ bb.bb_label = bb'.bb_label /\ MEM j bb.bb_instructions /\
       MEM j.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmpLowerDefsTheory.fmp_lower_blocks_def] >>
  simp[fmpLowerDefsTheory.fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule_all fmpStepRewriteTheory.fmp_lower_indexed_supply >> strip_tac >>
  `MEM x s2.irs_used_vars` by
    gvs[dretDesugarProofsTheory.dret_supply_extends_def] >>
  gvs[]
  >- (`!i. MEM i h.bb_instructions /\ MEM x i.inst_outputs ==>
           MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]` by (simp[] >> metis_tac[]) >>
      drule_all fmp_lower_indexed_retpc_writer >> strip_tac >>
      qexists `h` >> simp[]) >>
  first_x_assum drule >> simp[] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> qexists `bb` >> simp[]
QED

Theorem fmp_make_root_layout_runner_outputs:
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root pc s') ==>
  !i. MEM i (OPTION_TO_LIST root) ==> i.inst_outputs = [runner]
Proof
  simp[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, mk_inst_def]
QED

Theorem fmp_install_root_retpc_writer_origin:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  (!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM) /\
  (!i. MEM i (OPTION_TO_LIST root) ==> i.inst_outputs = [runner]) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s)
    (entry::rest) = SOME (out,s') /\
  MEM bb' out /\ MEM j bb'.bb_instructions /\ MEM x j.inst_outputs /\ x <> runner ==>
  j.inst_opcode = RETPC_PARAM \/
  ?bb. MEM bb (entry::rest) /\ bb.bb_label = bb'.bb_label /\ MEM j bb.bb_instructions
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qpat_x_assum `!s'' root rest fn ctx. _` kall_tac >>
  `~MEM j (OPTION_TO_LIST root)` by (strip_tac >> first_x_assum drule >> simp[] >>
    disch_then (fn th => gvs[th])) >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >> metis_tac[MEM_APPEND]
QED

Theorem fmp_install_checked_root_retpc_writer_origin:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  MEM bb' out /\ MEM j bb'.bb_instructions /\ MEM x j.inst_outputs /\ x <> runner ==>
  j.inst_opcode = RETPC_PARAM \/
  ?bb. MEM bb blocks /\ bb.bb_label = bb'.bb_label /\ MEM j bb.bb_instructions
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule fmp_make_root_layout_runner_outputs >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  gvs[] >> pure_once_rewrite_tac[GSYM MEM] >>
  irule fmp_install_root_retpc_writer_origin >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >> metis_tac[]
QED

Theorem fmp_lower_function_retpc_writer_location:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ ir_supply_inst_ok s /\
  MEM x s.irs_used_vars /\
  (!bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
       MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]) /\
  MEM bb' fn'.fn_blocks /\ MEM j bb'.bb_instructions /\ MEM x j.inst_outputs ==>
  j.inst_opcode = RETPC_PARAM \/
  ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = bb'.bb_label /\ MEM j bb.bb_instructions /\
       MEM j.inst_opcode [ASSIGN; PHI]
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >~ [`fn.fn_fmp_signature = SOME sig`]
  >- (first_x_assum drule >> simp[] >> metis_tac[]) >>
  drule fmpLowerDefsTheory.fmp_checked_seal_some >> strip_tac >>
  gvs[fmpLowerDefsTheory.fmp_seal_def]
  >- (first_x_assum drule >> simp[] >> metis_tac[]) >>
  Cases_on `root_layout` >> gvs[] >>
  drule_all irSupplyTheory.fresh_ir_var_inst_ok >> strip_tac >>
  drule (cj 1 fresh_ir_var_contract) >> strip_tac >>
  drule (cj 2 fresh_ir_var_contract) >> strip_tac >>
  drule_all fmp_make_root_layout_inst_ok >> strip_tac >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  `x <> runner` by metis_tac[] >>
  `?users oldpc suffix.
     split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_x_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_checked_root_retpc_writer_origin >> strip_tac >- simp[] >>
  rename1 `fmp_lower_blocks infos ctx runner seedSupply _ _ = _` >>
  `MEM x seedSupply.irs_used_vars` by gvs[] >>
  drule fmp_lower_blocks_retpc_writer >>
  disch_then (qspecl_then [`x`, `j`, `bb`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem retpc_shape_writer_opcodes:
  retpc_shape_ok fn /\ retpc_var fn x ==>
  !bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
    MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  simp[retpc_shape_ok_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  rpt strip_tac >>
  qpat_x_assum `!inst x. _` (qspecl_then [`i`, `x`] mp_tac) >>
  simp[] >> (impl_tac >- (qexists `bb` >> simp[])) >> metis_tac[]
QED

Theorem retpc_var_supply_member:
  ir_supply_covers_fn s fn /\ retpc_var fn x ==> MEM x s.irs_used_vars
Proof
  simp[retpc_var_def, ir_supply_covers_fn_def, list_subset_def] >>
  rpt strip_tac >> drule copy_phi_var_in_ir_vars >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_lower_function_retpc_writer:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ ir_supply_inst_ok s /\
  ir_supply_covers_fn s fn /\ retpc_shape_ok fn /\ retpc_var fn x /\
  MEM j (fn_insts fn') /\ MEM x j.inst_outputs ==>
  ?i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs /\ j.inst_id = i.inst_id /\
    ((i.inst_opcode = RETPC_PARAM /\ j.inst_opcode = RETPC_PARAM) \/
     (MEM i.inst_opcode [ASSIGN; PHI] /\ j = i))
Proof
  strip_tac >> drule retpc_shape_writer_opcodes >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  drule_all retpc_var_supply_member >> strip_tac >>
  gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  drule fmp_lower_function_retpc_writer_location >>
  disch_then (qspecl_then [`x`, `j`, `bb`] mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac
  >- (drule fmp_lower_function_seed_location >>
      disch_then (qspecl_then [`j.inst_outputs`, `bb.bb_label`, `j.inst_id`]
        (mp_tac o iffLR)) >>
      simp[] >> (impl_tac >- (qexistsl [`bb`, `j`] >> simp[])) >>
      strip_tac >> qexists `i` >> simp[] >> metis_tac[]) >>
  qexists `j` >> simp[] >> metis_tac[]
QED

Theorem fmp_lower_function_reachable_assign_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ retpc_var fn x /\
  MEM j (fn_insts (reachable_fn fn')) /\ MEM x j.inst_outputs /\
  j.inst_opcode = ASSIGN ==>
  MEM j (fn_insts (reachable_fn fn))
Proof
  strip_tac >> drule_all fmp_lower_function_reachable >> strip_tac >>
  `retpc_shape_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule retpc_shape_writer_opcodes >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  drule_all retpc_var_supply_member >> strip_tac >>
  gvs[MEM_reachable_fn_insts, reachable_inst_fields] >>
  gvs[reachable_inst_def] >>
  drule fmp_lower_function_retpc_writer_location >>
  disch_then (qspecl_then [`x`, `i`, `bb`] mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl [`bb'`, `i`] >> simp[]
QED

Theorem copy_phi_var_seed_transport:
  (!inst x. MEM inst (fn_insts src) /\ inst.inst_opcode = origin /\
       MEM x inst.inst_outputs ==>
       ?j. MEM j (fn_insts dst) /\ j.inst_opcode = origin /\ MEM x j.inst_outputs) /\
  (!inst. MEM inst (fn_insts src) /\ MEM inst.inst_opcode [ASSIGN; PHI] ==>
       MEM inst (fn_insts dst)) ==>
  !x. copy_phi_var origin src x ==> copy_phi_var origin dst x
Proof
  strip_tac >>
  `copy_phi_upper_bound origin src (copy_phi_var origin dst)` by
    (simp[fmpStepClosureTheory.copy_phi_upper_bound_def] >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >>
     metis_tac[copy_phi_var_rules, MEM]) >>
  metis_tac[fmpStepClosureTheory.copy_phi_upper_bound_sound]
QED

Theorem fmp_lower_function_retpc_var_forward:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ retpc_var fn x ==>
  retpc_var fn' x
Proof
  strip_tac >>
  `!x. copy_phi_var RETPC_PARAM fn x ==> copy_phi_var RETPC_PARAM fn' x` by
    (match_mp_tac copy_phi_var_seed_transport >> conj_tac
     >- (rpt strip_tac >> gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
         drule fmp_lower_function_seed_location >>
         disch_then (qspecl_then [`inst.inst_outputs`, `bb.bb_label`, `inst.inst_id`]
           (mp_tac o iffRL)) >>
         (impl_tac >- (qexistsl [`bb`, `inst`] >> simp[])) >>
         strip_tac >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
     simp[] >> rpt strip_tac >> gvs[fn_insts_def, MEM_fn_insts_blocks_iff]
     >- (drule_all fmp_lower_function_assign_location >> metis_tac[]) >>
     drule_all fmp_lower_function_phi_location >> metis_tac[]) >>
  gvs[retpc_var_def]
QED

Theorem fmp_lower_function_reachable_retpc_var_forward:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  retpc_var (reachable_fn fn) x ==> retpc_var (reachable_fn fn') x
Proof
  strip_tac >>
  `!x. copy_phi_var RETPC_PARAM (reachable_fn fn) x ==>
       copy_phi_var RETPC_PARAM (reachable_fn fn') x` by
    (match_mp_tac copy_phi_var_seed_transport >> conj_tac
     >- (rpt strip_tac >> drule_all fmp_lower_function_reachable_seed >>
         disch_then (qspecl_then [`inst.inst_outputs`, `inst.inst_id`]
           (mp_tac o iffRL)) >>
         (impl_tac >- metis_tac[]) >> metis_tac[]) >>
     simp[] >> rpt strip_tac
     >- metis_tac[fmp_lower_function_reachable_assign] >>
     metis_tac[fmp_lower_function_reachable_phi]) >>
  gvs[retpc_var_def]
QED

Theorem fmp_lower_function_reachable_retpc_var_reflect:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  retpc_var (reachable_fn fn') x ==> retpc_var (reachable_fn fn) x
Proof
  strip_tac >>
  `!origin g x. copy_phi_var origin g x ==>
    origin = RETPC_PARAM /\ g = reachable_fn fn' ==>
    copy_phi_var RETPC_PARAM (reachable_fn fn) x` suffices_by
    metis_tac[retpc_var_def] >>
  Induct_on `copy_phi_var` >> rpt strip_tac >> gvs[]
  >- (drule_all fmp_lower_function_reachable_seed >>
      disch_then (qspecl_then [`inst.inst_outputs`, `inst.inst_id`]
        (mp_tac o iffLR)) >>
      (impl_tac >- metis_tac[]) >>
      metis_tac[copy_phi_var_rules])
  >- (`retpc_var (reachable_fn fn') x'` by
        metis_tac[retpc_var_def, copy_phi_var_rules] >>
      drule reachable_retpc_var >> strip_tac >>
      `retpc_var fn x'` by
        metis_tac[fmp_lower_function_retpc_var_reflect] >>
      drule_all fmp_lower_function_reachable_assign_origin >>
      metis_tac[copy_phi_var_rules]) >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    metis_tac[fmp_lower_function_reachable_phi] >>
  metis_tac[copy_phi_var_rules]
QED

Theorem fmp_lower_function_retpc_returns:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  !inst. MEM inst (fn_insts (reachable_fn fn')) /\
    MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
    ?front x. inst.inst_operands = front ++ [Var x] /\
      retpc_var (reachable_fn fn') x
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule_all fmp_lower_function_reachable_return_origin >> strip_tac >>
  `?front x. inst'.inst_operands = front ++ [Var x] /\
      retpc_var (reachable_fn fn) x` by
    (gvs[o1_fn_shape_def, fn_shape_ok_def, retpc_shape_ok_def] >> metis_tac[]) >>
  `retpc_var (reachable_fn fn') x` by
    metis_tac[fmp_lower_function_reachable_retpc_var_forward] >>
  qexistsl [`FRONT inst.inst_operands`, `x`] >>
  gvs[NULL_EQ] >> metis_tac[APPEND_FRONT_LAST]
QED

Theorem fmp_lower_function_retpc_phis:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  !inst x y. MEM inst (fn_insts (reachable_fn fn')) /\
    inst.inst_opcode = PHI /\ MEM (Var x) inst.inst_operands /\
    MEM (Var y) inst.inst_operands /\ retpc_var (reachable_fn fn') x ==>
    retpc_var (reachable_fn fn') y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    metis_tac[fmp_lower_function_reachable_phi] >>
  `retpc_var (reachable_fn fn) x` by
    metis_tac[fmp_lower_function_reachable_retpc_var_reflect] >>
  `retpc_var (reachable_fn fn) y` by
    (gvs[o1_fn_shape_def, fn_shape_ok_def, retpc_shape_ok_def] >> metis_tac[]) >>
  metis_tac[fmp_lower_function_reachable_retpc_var_forward]
QED

Theorem fmp_lower_function_retpc_writers:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  !inst x. MEM inst (fn_insts fn') /\ MEM x inst.inst_outputs /\ retpc_var fn' x ==>
    inst.inst_opcode = RETPC_PARAM \/
    (inst.inst_opcode = ASSIGN /\ ?y. inst.inst_operands = [Var y] /\ retpc_var fn' y) \/
    (inst.inst_opcode = PHI /\
     (?y. MEM (Var y) inst.inst_operands /\ retpc_var fn' y) /\
     (!y. MEM (Var y) inst.inst_operands ==> retpc_var fn' y))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `retpc_shape_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `retpc_var fn x` by metis_tac[fmp_lower_function_retpc_var_reflect] >>
  drule_all fmp_lower_function_retpc_writer >> strip_tac
  >- simp[] >>
  gvs[] >>
  qpat_x_assum `retpc_shape_ok fn` mp_tac >>
  simp[retpc_shape_ok_def] >> strip_tac >>
  qpat_x_assum `!inst x. _` (qspecl_then [`i`, `x`] mp_tac) >>
  simp[] >>
  metis_tac[fmp_lower_function_retpc_var_forward]
QED

Theorem fmp_lower_function_inst_id_inj:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  !i j. MEM i (fn_insts fn') /\ MEM j (fn_insts fn') /\
        i.inst_id = j.inst_id ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks))` by
    gvs[o1_fn_shape_def, wf_function_def, fn_inst_ids_distinct_def] >>
  `EVERY (\bb. EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions) fn.fn_blocks` by
    gvs[ir_supply_covers_fn_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
        EVERY_FLAT, EVERY_MAP] >>
  drule_all fmp_lower_function_ids_distinct >> strip_tac >>
  `!bbs. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs) =
    MAP (\i. i.inst_id) (fn_insts_blocks bbs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_FLAT, MAP_MAP_o]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn'))` by
    metis_tac[fn_insts_def] >>
  qpat_x_assum `ALL_DISTINCT (MAP _ (fn_insts fn'))` mp_tac >>
  SPEC_TAC (``fn_insts fn'``, ``insts : instruction list``) >>
  Induct >> simp[] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_lower_function_retpc_writer_unique:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==>
  !i j x. MEM i (fn_insts fn') /\ MEM j (fn_insts fn') /\
    MEM x i.inst_outputs /\ MEM x j.inst_outputs /\ retpc_var fn' x ==> i = j
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `retpc_shape_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `retpc_var fn x` by metis_tac[fmp_lower_function_retpc_var_reflect] >>
  drule fmp_lower_function_retpc_writer >>
  disch_then (qspecl_then [`x`, `i`] mp_tac) >> simp[] >>
  strip_tac >>
  drule fmp_lower_function_retpc_writer >>
  disch_then (qspecl_then [`x`, `j`] mp_tac) >> simp[] >>
  strip_tac >>
  `i.inst_id = j.inst_id` by
    (qpat_x_assum `retpc_shape_ok fn` mp_tac >>
     simp[retpc_shape_ok_def] >> metis_tac[]) >>
  metis_tac[fmp_lower_function_inst_id_inj]
QED

(* The four clause interfaces above separate reachable return/PHI transport
   from full-function writer provenance.  All are validated before assembly. *)
Theorem fmp_lower_function_retpc_shape_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==> retpc_shape_ok fn'
Proof
  strip_tac >> rewrite_tac[retpc_shape_ok_def] >>
  conj_tac >- (match_mp_tac fmp_lower_function_retpc_returns >> simp[]) >>
  conj_tac >- (match_mp_tac fmp_lower_function_retpc_phis >> simp[]) >>
  conj_tac >- (match_mp_tac fmp_lower_function_retpc_writers >> simp[]) >>
  match_mp_tac fmp_lower_function_retpc_writer_unique >> simp[]
QED
