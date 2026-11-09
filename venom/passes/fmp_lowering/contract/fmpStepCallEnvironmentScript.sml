Theory fmpStepCallEnvironment
Ancestors
  fmpStepStructural fmpStepFlagTransport fmpStepPredicateTransport
  fmpLowerDefs fmpLowerIndexedProps unitShapeDefs list rich_list

Theorem fmp_lower_inst_revert_terminal:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  (inst.inst_opcode = REVERT \/ inst.inst_opcode = JMP) ==>
  out = [inst]
Proof
  strip_tac >> gvs[fmp_lower_inst_def]
QED

Theorem fmp_lower_indexed_revert_last:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ insts <> [] /\
  ((LAST insts).inst_opcode = REVERT \/ (LAST insts).inst_opcode = JMP) ==>
  out <> [] /\ LAST out = LAST insts
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[fmp_lower_indexed_cons] >> strip_tac >>
  (Cases_on `insts = []`
   >- (gvs[fmp_lower_indexed_def] >>
       drule fmp_lower_inst_revert_terminal >> simp[] >> strip_tac >>
       gvs[]) >>
   gvs[LAST_DEF] >> first_x_assum drule >> simp[] >> strip_tac >>
   Cases_on `tail` >> gvs[LAST_APPEND])
QED

Theorem fmp_lower_inst_no_invoke:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  inst.inst_opcode <> INVOKE ==>
  EVERY (\i. i.inst_opcode <> INVOKE) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), venomInstTheory.mk_inst_def]
QED

Theorem fmp_lower_indexed_no_invoke:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\
  EVERY (\i. i.inst_opcode <> INVOKE) insts ==>
  EVERY (\i. i.inst_opcode <> INVOKE) out
Proof
  strip_tac >> drule fmpStepRewriteTheory.fmp_lower_indexed_every >>
  disch_then (qspec_then `\i. i.inst_opcode <> INVOKE` mp_tac) >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >> drule fmp_lower_inst_no_invoke >>
      gvs[EVERY_MEM]) >>
  rpt strip_tac >>
  rename1 `fmp_emit_restores runner t bases = (prefix,t')` >>
  irule fmpStepRewriteTheory.fmp_emit_restores_every >>
  qexistsl_tac [`bases`, `runner`, `t`, `t'`] >>
  simp[venomInstTheory.mk_inst_def]
QED

Theorem fmp_lower_blocks_revert_witness:
  !bbs s restores out leftover s' bb.
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  MEM bb bbs /\ bb.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
  ((LAST bb.bb_instructions).inst_opcode = REVERT \/
   (LAST bb.bb_instructions).inst_opcode = JMP) ==>
  ?bb'. MEM bb' out /\ bb'.bb_label = bb.bb_label /\
    bb'.bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> strip_tac >>
  (Cases_on `bb = h`
   >- (gvs[] >>
       drule fmp_lower_indexed_revert_last >> simp[] >> strip_tac >>
       drule fmp_lower_indexed_no_invoke >> simp[] >> strip_tac >>
       qexists_tac `bb with bb_instructions := insts` >> simp[]) >>
   gvs[] >> first_x_assum drule >> simp[] >>
   disch_then (qspec_then `bb` mp_tac) >> simp[] >>
   strip_tac >> goal_assum (drule_at Any) >> simp[])
QED

Theorem revert_path_block_witness_transport:
  (!bb. MEM bb src /\ bb.bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    ((LAST bb.bb_instructions).inst_opcode = REVERT \/
     (LAST bb.bb_instructions).inst_opcode = JMP) ==>
    ?bb'. MEM bb' dst /\ bb'.bb_label = bb.bb_label /\
      bb'.bb_instructions <> [] /\
      EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions /\
      LAST bb'.bb_instructions = LAST bb.bb_instructions) ==>
  !n l. revert_path src n l ==> revert_path dst n l
Proof
  strip_tac >> Induct >- simp[revert_path_def] >>
  simp[revert_path_def, EXISTS_MEM] >> rpt strip_tac >>
  qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[] >>
  strip_tac >> goal_assum (drule_at Any) >>
  gvs[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem fmp_lower_blocks_revert_path:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  !n l. revert_path bbs n l ==> revert_path out n l
Proof
  rpt strip_tac >> irule revert_path_block_witness_transport >>
  qexists_tac `bbs` >> simp[] >>
  rpt strip_tac >> drule fmp_lower_blocks_revert_witness >>
  disch_then (qspec_then `bb` mp_tac) >> simp[]
QED

Theorem flag_fails_revert_environment:
  LENGTH dst = LENGTH src /\
  (!n l. revert_path src n l ==> revert_path dst n l) ==>
  !vs i. flag_fails src vs i ==> flag_fails dst vs i
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `i.inst_opcode` >> simp[flag_fails_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[]
QED


Theorem revert_terminal_suffix_nonempty:
  EVERY (\i. i.inst_opcode <> REVERT /\ i.inst_opcode <> JMP) pre /\
  pre ++ tail <> [] /\
  ((LAST (pre ++ tail)).inst_opcode = REVERT \/
   (LAST (pre ++ tail)).inst_opcode = JMP) ==>
  tail <> []
Proof
  strip_tac >> Cases_on `tail <> []` >- simp[] >>
  gvs[] >>
  `MEM (LAST pre) pre` by (Cases_on `pre` >> gvs[MEM_LAST]) >>
  gvs[EVERY_MEM]
QED

Theorem revert_witness_replace_prefix:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode <> REVERT /\ i.inst_opcode <> JMP) pre /\
  EVERY (\i. i.inst_opcode <> INVOKE) new /\
  bb.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
  ((LAST bb.bb_instructions).inst_opcode = REVERT \/
   (LAST bb.bb_instructions).inst_opcode = JMP) ==>
  new ++ tail <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) (new ++ tail) /\
  LAST (new ++ tail) = LAST bb.bb_instructions
Proof
  strip_tac >>
  `tail <> []` by (irule revert_terminal_suffix_nonempty >>
    qexists_tac `pre` >> gvs[]) >>
  Cases_on `tail` >> gvs[LAST_APPEND, EVERY_APPEND] >>
  Cases_on `t` >> gvs[LAST_APPEND]
QED

Theorem fmp_root_layout_no_invoke:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') ==>
  EVERY (\i. i.inst_opcode <> INVOKE)
    (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[venomInstTheory.mk_inst_def, set_param_index_def,
      callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  drule fmpStepRestrictionClosureTheory.split_fmp_entry_retpc_restrictions >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[unitShapeDefsTheory.inst_shape_ok_def] >>
  metis_tac[]
QED

Theorem fmp_install_checked_root_revert_witness:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) /\
  MEM bb blocks /\ bb.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
  ((LAST bb.bb_instructions).inst_opcode = REVERT \/
   (LAST bb.bb_instructions).inst_opcode = JMP) ==>
  ?bb'. MEM bb' out /\ bb'.bb_label = bb.bb_label /\
    bb'.bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  strip_tac >> (
  drule_all fmpStepLayoutTheory.fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule fmp_root_layout_no_invoke >> strip_tac >>
  drule fmpStepLayoutTheory.split_fmp_entry_parameter_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> REVERT /\ i.inst_opcode <> JMP)
    (users ++ OPTION_TO_LIST oldpc)` by
    (Cases_on `oldpc` >>
     gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> gvs[]) >>
  drule_all fmpStepLayoutTheory.fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmpStepLayoutTheory.fmp_install_root_exact_prefix >> strip_tac >> gnvs[] >>
  Cases_on `bb = entry`
  >- (gvs[] >>
      `tail <> []` by
        (irule revert_terminal_suffix_nonempty >>
         qexists_tac `users ++ OPTION_TO_LIST oldpc` >>
         gvs[EVERY_APPEND, APPEND_ASSOC]) >>
      Cases_on `fn_is_context_entry ctx fn`
      >- (qexists_tac `bb with bb_instructions := users ++ OPTION_TO_LIST newpc ++ OPTION_TO_LIST root ++ tail` >>
          Cases_on `tail` >> gvs[LAST_APPEND] >>
          Cases_on `t` >> gvs[LAST_APPEND]) >>
      qexists_tac `bb with bb_instructions := users ++ OPTION_TO_LIST root ++ OPTION_TO_LIST newpc ++ tail` >>
      Cases_on `tail` >> gvs[LAST_APPEND] >>
      Cases_on `t` >> gvs[LAST_APPEND]) >>
  qexists_tac `bb` >> gvs[])
QED

Theorem fmp_install_checked_root_revert_path:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root newpc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s2) blocks = SOME (out,s3) ==>
  !k l. revert_path blocks k l ==> revert_path out k l
Proof
  rpt strip_tac >> irule revert_path_block_witness_transport >>
  qexists_tac `blocks` >> simp[] >>
  rpt strip_tac >> irule fmp_install_checked_root_revert_witness >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem fmp_lower_function_revert_path:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  !n l. revert_path fn.fn_blocks n l ==> revert_path fn'.fn_blocks n l
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fmp_checked_seal_some >> gvs[fmp_seal_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `revert_path blocks n l` by
    (drule_all fmp_lower_blocks_revert_path >> simp[]) >>
  drule_all fmp_install_checked_root_revert_path >> simp[]
QED

Theorem fmp_lower_function_flag_fails:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  !vs i. flag_fails fn.fn_blocks vs i ==> flag_fails fn'.fn_blocks vs i
Proof
  rpt strip_tac >>
  `LENGTH fn'.fn_blocks = LENGTH fn.fn_blocks` by
    (drule fmpStepLayoutTheory.fmp_lower_function_preserves_labels >>
     disch_then (mp_tac o AP_TERM ``LENGTH : string list -> num``) >>
     simp[venomInstTheory.fn_labels_def]) >>
  irule flag_fails_revert_environment >>
  qexists_tac `fn.fn_blocks` >> simp[] >>
  metis_tac[fmp_lower_function_revert_path]
QED
