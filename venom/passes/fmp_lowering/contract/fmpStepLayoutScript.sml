(* Physical entry layout reconstruction for FMP lowering. *)
Theory fmpStepLayout
Ancestors
  fmpLowerDefs fmpLowerProps fmpStepTraversal fmpStepReclaim
  list rich_list finite_map venomInst arithmetic o1PassContract irSupply

Theorem split_fmp_entry_from_reconstruct:
  split_fmp_entry_from k acc insts = SOME (FmpEntryLayout users retpc suffix) ==>
  REVERSE acc ++ insts = users ++ option_CASE retpc [] (\i. [i]) ++ suffix
Proof
  map_every qid_spec_tac [`k`, `acc`] >> Induct_on `insts`
  >- simp[split_fmp_entry_from_def] >>
  simp[Once split_fmp_entry_from_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem split_fmp_entry_reconstruct:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc suffix) ==>
  ?entry rest. fn.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++ option_CASE retpc [] (\i. [i]) ++ suffix
Proof
  simp[split_fmp_entry_def, AllCaseEqs()] >> rpt strip_tac >>
  drule split_fmp_entry_from_reconstruct >> simp[] >> metis_tac[]
QED

Theorem split_fmp_entry_from_users:
  split_fmp_entry_from k acc insts = SOME (FmpEntryLayout users retpc suffix) /\
  EVERY (\i. i.inst_opcode = PARAM) acc ==>
  EVERY (\i. i.inst_opcode = PARAM) users
Proof
  map_every qid_spec_tac [`k`, `acc`] >> Induct_on `insts`
  >- (rpt strip_tac >> gvs[split_fmp_entry_from_def, EVERY_REVERSE]) >>
  simp[Once split_fmp_entry_from_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[EVERY_REVERSE] >> first_x_assum irule >>
  qexistsl [`h::acc`, `SUC k`] >> simp[]
QED

Theorem split_fmp_entry_users:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc suffix) ==>
  EVERY (\i. i.inst_opcode = PARAM) users
Proof
  simp[split_fmp_entry_def, AllCaseEqs()] >> rpt strip_tac >>
  drule split_fmp_entry_from_users >> simp[]
QED

Theorem analyze_fmp_reclaims_parameter_prefix_absent:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  lookup_block label fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ suffix /\
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix ==>
  !n base. n < LENGTH prefix ==>
    ~MEM ((label,n),base) (fmp_plan_to_alist fn plan)
Proof
  rpt strip_tac >> rename1 `MEM ((label,n),target) (fmp_plan_to_alist fn plan)` >>
  `FLOOKUP plan (label,n) = SOME target` by
    gvs[MEM_fmp_plan_to_alist] >>
  drule_all analyze_fmp_reclaims_position >> simp[] >> strip_tac >> gvs[] >>
  drule fmp_reclaim_point_not_prefix >>
  `MEM (EL n prefix).inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]` by
    (fs[EVERY_EL] >> first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  gvs[EL_APPEND1]
QED

Theorem split_fmp_entry_parameter_prefix:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc suffix) ==>
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
    (users ++ option_CASE retpc [] (\i. [i]))
Proof
  strip_tac >> drule split_fmp_entry_users >>
  Cases_on `retpc`
  >- (simp[EVERY_MEM] >> metis_tac[]) >>
  drule split_fmp_entry_retpc_opcode >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_lower_blocks_checked_entry_prefix:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_lower_blocks infos ctx runner s (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult out leftover s') ==>
  ?entry rest tail.
    out = entry::rest /\
    entry.bb_instructions = users ++ option_CASE retpc [] (\i. [i]) ++ tail
Proof
  strip_tac >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `!n target. n < LENGTH (users ++ option_CASE retpc [] (\i. [i])) ==>
    ~MEM ((entry.bb_label,n),target) (fmp_plan_to_alist fn plan)` by
    (rpt strip_tac >>
     drule_all analyze_fmp_reclaims_parameter_prefix_absent >>
     metis_tac[]) >>
  fs[] >> drule fmp_lower_blocks_entry_parameter_prefix >>
  disch_then (qspecl_then [`suffix`, `users ++ option_CASE retpc [] (\i. [i])`] mp_tac) >>
  simp[APPEND_ASSOC] >> metis_tac[]
QED

Theorem fmp_install_root_exact_prefix:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) ==>
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME ((entry with bb_instructions :=
      (if fn_is_context_entry ctx fn then
         users ++ OPTION_TO_LIST newpc ++ OPTION_TO_LIST root ++ tail
       else users ++ OPTION_TO_LIST root ++ OPTION_TO_LIST newpc ++ tail))::rest,s)
Proof
  strip_tac >> Cases_on `oldpc` >> Cases_on `newpc` >>
  gvs[fmp_install_root_def, callLayoutDefsTheory.OPTION_TO_LIST_def, TAKE_APPEND1, DROP_APPEND1,
      DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem fmp_make_root_layout_prefix:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  n = LENGTH users /\ (newpc = NONE <=> oldpc = NONE)
Proof
  simp[fmp_make_root_layout_def] >>
  Cases_on `info.fi_needs_fmp` >> simp[] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[AllCaseEqs()] >>
  Cases_on `oldpc` >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_install_root_preserves_labels:
  fmp_install_root ctx fn layout blocks = SOME (blocks',s') ==>
  MAP (\bb. bb.bb_label) blocks' = MAP (\bb. bb.bb_label) blocks
Proof
  Cases_on `layout` >> Cases_on `blocks` >>
  simp[fmp_install_root_def] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_lower_blocks_preserves_labels:
  fmp_lower_blocks infos ctx runner s restores blocks =
    SOME (FmpBlocksResult blocks' leftover s') ==>
  MAP (\bb. bb.bb_label) blocks' = MAP (\bb. bb.bb_label) blocks
Proof
  strip_tac >> drule fmpStepRewriteTheory.fmp_lower_blocks_successors >>
  disch_then (mp_tac o AP_TERM ``MAP (FST : string # string list -> string)``) >> simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem fmp_lower_function_preserves_labels:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  fn_labels fn' = fn_labels fn
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >>
  gvs[fmp_seal_def, fn_labels_def] >>
  drule fmp_install_root_preserves_labels >>
  drule fmp_lower_blocks_preserves_labels >> simp[]
QED

Theorem fmp_install_root_supply:
  fmp_install_root ctx fn (FmpRootLayout n root pc s) blocks = SOME (blocks',s') ==>
  s' = s
Proof
  Cases_on `blocks` >> simp[fmp_install_root_def] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_make_root_layout_inst_ok:
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root pc s') /\
  ir_supply_inst_ok s ==> ir_supply_inst_ok s'
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[irSupplyTheory.fresh_inst_id_contract]
QED

Theorem fmp_lower_function_inst_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  ir_supply_inst_ok s ==> ir_supply_inst_ok s'
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all irSupplyTheory.fresh_ir_var_inst_ok >> strip_tac >>
  Cases_on `root_layout` >> gvs[] >>
  drule_all fmp_make_root_layout_inst_ok >> strip_tac >>
  drule_all fmpStepRewriteTheory.fmp_lower_blocks_supply >> strip_tac >>
  drule fmp_install_root_supply >> gvs[]
QED

Theorem fmp_lower_function_preserves_entry_label:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> drule fmp_lower_function_preserves_labels >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  simp[fn_labels_def, fn_entry_label_def, entry_block_def]
QED

Theorem fmp_parameter_prefix_successors:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM; INITIAL_FMP]) xs ==>
  FLAT (MAP get_successors xs) = []
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  gvs[get_successors_def, is_terminator_def] >> metis_tac[]
QED

Theorem fmp_make_root_layout_successors:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  FLAT (MAP get_successors (OPTION_TO_LIST root)) = [] /\
  FLAT (MAP get_successors (OPTION_TO_LIST newpc)) = [] /\
  FLAT (MAP get_successors (OPTION_TO_LIST oldpc)) = []
Proof
  strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     metis_tac[split_fmp_entry_retpc_opcode]) >>
  Cases_on `oldpc` >>
  gvs[fmp_make_root_layout_def, AllCaseEqs(), callLayoutDefsTheory.OPTION_TO_LIST_def,
      mk_inst_def, set_param_index_def, get_successors_def, is_terminator_def]
QED

Theorem fmp_install_checked_root_successors:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) ==>
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) out =
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) fn.fn_blocks
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_successors >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  drule fmpStepRewriteTheory.fmp_lower_blocks_successors >>
  simp[MAP_APPEND, FLAT_APPEND] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[]
QED

Theorem fmp_lower_function_preserves_successors:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) fn'.fn_blocks =
  MAP (\bb. (bb.bb_label, FLAT (MAP get_successors bb.bb_instructions))) fn.fn_blocks
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_install_checked_root_successors >> simp[]
QED

Theorem fmp_make_root_layout_ids:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  MAP (\i. i.inst_id) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_id) (OPTION_TO_LIST oldpc) /\
  EVERY (\i. s.irs_next_inst <= i.inst_id /\ i.inst_id < s'.irs_next_inst)
    (OPTION_TO_LIST root) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (OPTION_TO_LIST root)) /\
  s.irs_next_inst <= s'.irs_next_inst
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, mk_inst_def, set_param_index_def,
      irSupplyTheory.fresh_inst_id_def]
QED

Theorem fmp_install_root_ids_distinct:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  MAP (\i. i.inst_id) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_id) (OPTION_TO_LIST oldpc) /\
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) (entry::rest))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (OPTION_TO_LIST root)) /\
  (!i. MEM i (OPTION_TO_LIST root) ==>
    ~MEM i.inst_id (FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) (entry::rest)))) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) out))
Proof
  strip_tac >>
  `!id. MEM id (MAP (\i. i.inst_id) (OPTION_TO_LIST root)) ==>
    ~MEM id (FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) (entry::rest)))` by
    (pure_rewrite_tac[MEM_MAP] >> metis_tac[]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qpat_x_assum `!s'' root rest fn ctx. _` kall_tac >>
  qpat_x_assum `!i. MEM i (OPTION_TO_LIST root) ==> _` kall_tac >>
  Cases_on `fn_is_context_entry ctx fn` >>
  gvs[MAP_APPEND] >> gvs[ALL_DISTINCT_APPEND] >> rpt strip_tac >> metis_tac[]
QED

Theorem fmp_install_checked_root_ids_distinct:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)) /\
  EVERY (\bb. EVERY (\i. i.inst_id < s0.irs_next_inst) bb.bb_instructions) fn.fn_blocks ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) out))
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_ids >> strip_tac >>
  drule fmp_lower_blocks_id_transport >>
  disch_then (qspec_then `s0.irs_next_inst` mp_tac) >> simp[] >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) blocks))` by
    metis_tac[fmpStepIdTransportTheory.ir_id_transport_distinct] >>
  `!i. MEM i (OPTION_TO_LIST root) ==>
    ~MEM i.inst_id (FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) blocks))` by
    (rpt strip_tac >>
     `s0.irs_next_inst <= i.inst_id /\ i.inst_id < s1.irs_next_inst` by
       gvs[EVERY_MEM] >>
     drule_all fmpStepIdTransportTheory.ir_id_transport_origin >> strip_tac
     >- (gvs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS]) >>
     decide_tac) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  irule fmp_install_root_ids_distinct >>
  qexistsl [`ctx`, `entry`, `fn`, `newpc`, `oldpc`, `rest`, `root`, `s2`, `s3`, `tail`, `users`] >>
  simp[] >> Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

Theorem fmp_lower_function_ids_distinct:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)) /\
  EVERY (\bb. EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions) fn.fn_blocks ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn'.fn_blocks))
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >>
  `EVERY (\bb. EVERY (\j. j.inst_id < s1.irs_next_inst) bb.bb_instructions) fn.fn_blocks` by simp[] >>
  drule_all fmp_install_checked_root_ids_distinct >> simp[]
QED

Theorem fmp_install_root_id_predicate:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  MAP (\i. i.inst_id) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_id) (OPTION_TO_LIST oldpc) /\
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) (entry::rest) /\
  EVERY (\i. P i.inst_id) (OPTION_TO_LIST root) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) out
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qpat_x_assum `!s'' root rest fn ctx. _` kall_tac >>
  `EVERY P (MAP (\i. i.inst_id) (OPTION_TO_LIST newpc))` by
    (pure_asm_rewrite_tac[] >> simp[EVERY_MAP]) >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[EVERY_MAP]
QED

Theorem fmp_install_checked_root_id_predicate:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) fn.fn_blocks /\
  (!id. s0.irs_next_inst <= id ==> P id) ==>
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) out
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_make_root_layout_ids >> strip_tac >>
  `EVERY (\i. P i.inst_id) (OPTION_TO_LIST root)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all fmpStepRewriteTheory.fmp_lower_blocks_id_origin >> strip_tac
     >- (gvs[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[LESS_EQ_TRANS]) >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  drule_all fmp_install_root_id_predicate >> simp[]
QED

Theorem fmp_lower_function_id_predicate:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) fn.fn_blocks /\
  (!id. s.irs_next_inst <= id ==> P id) ==>
  EVERY (\bb. EVERY (\i. P i.inst_id) bb.bb_instructions) fn'.fn_blocks
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >>
  `!id. s1.irs_next_inst <= id ==> P id` by simp[] >>
  drule_all fmp_install_checked_root_id_predicate >> simp[]
QED

Theorem fmp_lower_function_fresh_names:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ ir_supply_inst_ok s ==>
  fresh_names_ok s fn fn'
Proof
  strip_tac >> drule fmp_lower_function_preserves_labels >> strip_tac >>
  simp[fresh_names_ok_def] >>
  `EVERY (\bb. EVERY (\i. MEM i.inst_id (fn_ir_inst_ids fn) \/
      ~MEM i.inst_id s.irs_used_inst_ids) bb.bb_instructions) fn'.fn_blocks` suffices_by
    (simp[irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.block_ir_inst_ids_def,
          EVERY_MEM, MEM_FLAT, MEM_MAP] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
  ho_match_mp_tac fmp_lower_function_id_predicate >>
  simp[irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.block_ir_inst_ids_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      qexists `MAP (\inst. inst.inst_id) bb.bb_instructions` >> simp[MEM_MAP] >> metis_tac[]) >>
  metis_tac[fmpStepSupplyTheory.ir_supply_old_id_bound, NOT_LESS]
QED

Theorem fmp_install_root_instruction_origin:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') /\ MEM j (fn_insts (fn with fn_blocks := out)) ==>
  MEM j (fn_insts (fn with fn_blocks := entry::rest)) \/
  MEM j (OPTION_TO_LIST root) \/ MEM j (OPTION_TO_LIST newpc)
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qpat_x_assum `!s'' root rest fn ctx. _` kall_tac >>
  Cases_on `fn_is_context_entry ctx fn` >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem fmp_optional_outputs_origin:
  MAP (\i. i.inst_outputs) (OPTION_TO_LIST newpc) =
    MAP (\i. i.inst_outputs) (OPTION_TO_LIST oldpc) /\
  MEM j (OPTION_TO_LIST newpc) ==>
  ?i. MEM i (OPTION_TO_LIST oldpc) /\ j.inst_outputs = i.inst_outputs
Proof
  Cases_on `oldpc` >> Cases_on `newpc` >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >> rpt strip_tac >> gvs[]
QED
