(*
 * SimplifyCFG keeps every CALL/STATICCALL success check (call_checks_ok).
 *
 * The check after a call stays in its block: merging only appends the
 * successor's instructions to a block that ended in JMP, and a JMP into a
 * revert path is replaced by that path's own instructions, which end in
 * REVERT or a JMP into another revert path.  Bypassing a jump-only block
 * and canonicalizing a JNZ with equal targets keep each revert-path target
 * a revert path, and removing unreachable blocks keeps every block a
 * reachable block can jump to.
 *)
Theory simplifyCfgCallChecks
Ancestors
  simplifyCfgDefs simplifyCfgCollapseShape simplifyCfgReferences cfgTransform cfgTransformProps venomExecProps
  simplifyCfgStruct simplifyCfgLabelProps simplifyCfgInvariant simplifyCfgShape simplifyCfgReachuses
  dftCallChecks unitShapeDefs venomWf venomInst list rich_list

Theorem revert_path_fuel_mono:
  !n m bbs l. revert_path bbs n l /\ n <= m ==>
    revert_path bbs m l
Proof
  Induct >- simp[revert_path_def] >>
  Cases_on `m` >- simp[] >>
  simp[revert_path_def, EXISTS_MEM] >>
  rpt strip_tac >> qexists_tac `bb` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem flag_fails_empty_mono:
  !bbs i vs. flag_fails bbs [] i ==> flag_fails bbs vs i
Proof
  rpt gen_tac >>
  Cases_on `i.inst_opcode` >> simp[flag_fails_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem flag_path_unconditional_last:
  !insts bbs vs.
    insts <> [] /\ EVERY (\i. i.inst_opcode <> INVOKE) insts /\
    flag_fails bbs [] (LAST insts) ==>
    flag_path bbs vs insts
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `insts` >> simp[flag_path_def] >> rpt strip_tac
  >- metis_tac[flag_fails_empty_mono] >>
  disj2_tac >> first_x_assum irule >> simp[]
QED

Theorem revert_path_minimal_step:
  !n bbs l.
    revert_path bbs (SUC (SUC n)) l /\
    (!m. m < SUC (SUC n) ==> ~revert_path bbs m l) ==>
    ?bb t.
      MEM bb bbs /\ bb.bb_label = l /\
      bb.bb_instructions <> [] /\
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      (LAST bb.bb_instructions).inst_opcode = JMP /\
      (LAST bb.bb_instructions).inst_operands = [Label t] /\
      revert_path bbs (SUC n) t /\
      (!m. m < SUC n ==> ~revert_path bbs m t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ _ _` mp_tac >>
  simp[Once revert_path_def, EXISTS_MEM] >> strip_tac
  >- (`revert_path bbs (SUC 0) l` by
        (pure_rewrite_tac[revert_path_def, EXISTS_MEM] >>
         qexists_tac `bb` >> simp[]) >>
      first_x_assum (qspec_then `SUC 0` mp_tac) >> simp[]) >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  qexistsl_tac [`bb`, `s`] >> simp[] >>
  rpt strip_tac >>
  `revert_path bbs (SUC m) bb.bb_label` by
    (pure_once_rewrite_tac[revert_path_def] >>
     pure_rewrite_tac[EXISTS_MEM] >>
     qexists_tac `bb` >> simp[]) >>
  first_x_assum (qspec_then `SUC m` mp_tac) >> simp[]
QED

Theorem revert_path_minimal_blocks:
  !n bbs l.
    revert_path bbs n l /\
    (!m. m < n ==> ~revert_path bbs m l) ==>
    ?xs. LENGTH xs = n /\ ALL_DISTINCT xs /\
      EVERY (\bb. MEM bb bbs /\ revert_path bbs n bb.bb_label) xs
Proof
  Induct >- simp[revert_path_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `n`
  >- (qpat_assum `revert_path _ _ _` mp_tac >>
      pure_once_rewrite_tac[revert_path_def] >>
      pure_rewrite_tac[EXISTS_MEM] >>
      disch_then (qx_choose_then `bb` strip_assume_tac) >>
      qexists_tac `[bb]` >> simp[] >> metis_tac[]) >>
  drule_all revert_path_minimal_step >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `bb::xs` >> simp[] >>
  conj_tac
  >- (strip_tac >>
      gvs[EVERY_MEM] >>
      first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
      metis_tac[prim_recTheory.LESS_SUC_REFL]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[revert_path_fuel_mono, arithmeticTheory.LESS_EQ_SUC_REFL]
QED

Theorem revert_path_fuel_normalize:
  !bbs n l. revert_path bbs n l ==>
    revert_path bbs (LENGTH bbs) l
Proof
  rpt strip_tac >>
  qspec_then `\k. revert_path bbs k l` mp_tac arithmeticTheory.WOP >>
  (impl_tac >- metis_tac[]) >> BETA_TAC >> strip_tac >>
  drule_all revert_path_minimal_blocks >> strip_tac >>
  `set xs SUBSET set bbs` by gvs[EVERY_MEM, pred_setTheory.SUBSET_DEF] >>
  `CARD (set xs) <= CARD (set bbs)` by
    (irule pred_setTheory.CARD_SUBSET >> simp[]) >>
  `LENGTH xs <= LENGTH bbs` by
    metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, CARD_LIST_TO_SET,
              arithmeticTheory.LESS_EQ_TRANS] >>
  metis_tac[revert_path_fuel_mono]
QED

Theorem flag_path_append:
  !xs bbs vs ys. flag_path bbs vs xs ==> flag_path bbs vs (xs ++ ys)
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> simp[flag_path_def] >> metis_tac[]
QED

Theorem calls_flagged_append:
  !xs bbs ys. calls_flagged bbs xs /\ calls_flagged bbs ys ==>
    calls_flagged bbs (xs ++ ys)
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt gen_tac >> simp[calls_flagged_def] >> strip_tac >>
  strip_tac >> Cases_on `h.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[flag_path_append]
QED

Theorem calls_flagged_prefix_no_calls:
  !xs bbs ys.
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) xs ==>
    (calls_flagged bbs (xs ++ ys) <=> calls_flagged bbs ys)
Proof
  Induct >> simp[calls_flagged_def] >> metis_tac[]
QED

Theorem flag_path_replace_last:
  !xs bbs vs old ys.
    flag_path bbs vs (xs ++ [old]) /\
    (!ws. flag_path bbs ws ys) ==>
    flag_path bbs vs (xs ++ ys)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[flag_path_def] >> metis_tac[]
QED

Theorem calls_flagged_replace_last:
  !xs bbs old ys.
    calls_flagged bbs (xs ++ [old]) /\ calls_flagged bbs ys /\
    (!ws. flag_path bbs ws ys) ==>
    calls_flagged bbs (xs ++ ys)
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt gen_tac >> simp[calls_flagged_def] >> strip_tac >>
  conj_tac
  >- (strip_tac >> Cases_on `h.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[] >> metis_tac[flag_path_replace_last]) >>
  metis_tac[]
QED

Theorem calls_flagged_phi_map:
  !xs f bbs.
    (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
       (EL i xs).inst_opcode = PHI) /\
    (!i. i.inst_opcode <> PHI ==> f i = i) /\
    (!i. i.inst_opcode = PHI ==>
       (f i).inst_opcode <> CALL /\ (f i).inst_opcode <> STATICCALL) ==>
    (calls_flagged bbs (MAP f xs) <=> calls_flagged bbs xs)
Proof
  Induct >- simp[calls_flagged_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[calls_flagged_def] >> first_x_assum irule >> simp[] >>
      rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `MAP f xs = xs` by (`MAP f xs = MAP I xs` suffices_by simp[] >>
      irule MAP_CONG >> gvs[EVERY_MEM]) >>
  simp[calls_flagged_def]
QED

Theorem calls_flagged_block_phi_map:
  bb_well_formed bb /\
  (!i. i.inst_opcode <> PHI ==> f i = i) /\
  (!i. i.inst_opcode = PHI ==>
    (f i).inst_opcode <> CALL /\ (f i).inst_opcode <> STATICCALL) ==>
  (calls_flagged bbs (MAP f bb.bb_instructions) <=>
   calls_flagged bbs bb.bb_instructions)
Proof
  strip_tac >> irule calls_flagged_phi_map >> gvs[bb_well_formed_def] >>
  metis_tac[]
QED

Theorem phi_map_revert_observations:
  bb_well_formed bb /\
  (!i. (f i).inst_opcode = i.inst_opcode) /\
  (!i. i.inst_opcode <> PHI ==> f i = i) ==>
  MAP f bb.bb_instructions <> [] /\
  LAST (MAP f bb.bb_instructions) = LAST bb.bb_instructions /\
  (EVERY (\i. i.inst_opcode <> INVOKE) (MAP f bb.bb_instructions) <=>
   EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions)
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   (LAST bb.bb_instructions).inst_opcode <> PHI` by
    (gvs[bb_well_formed_def] >> strip_tac >> gvs[is_terminator_def]) >>
  simp[LAST_MAP, EVERY_MAP]
QED

Theorem reachable_block_successor:
  ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks /\
  reachable fn bb.bb_label /\ MEM t (bb_succs bb) ==>
  reachable fn t
Proof
  strip_tac >> irule reachable_step >>
  qexists_tac `bb.bb_label` >> simp[fn_succ_def] >>
  qexists_tac `bb` >> simp[] >>
  irule MEM_lookup_block >> gvs[fn_labels_def]
QED

Theorem revert_path_remove_unreachable:
  !n fn l.
    ALL_DISTINCT (fn_labels fn) /\ reachable fn l /\
    revert_path fn.fn_blocks n l ==>
    revert_path (remove_unreachable_blocks fn).fn_blocks n l
Proof
  Induct >- simp[revert_path_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ _ _` mp_tac >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> BETA_TAC >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> BETA_TAC >>
  qexists_tac `bb` >>
  `MEM bb (remove_unreachable_blocks fn).fn_blocks` by
    (Cases_on `fn_entry_label fn` >>
     gvs[remove_unreachable_blocks_def, MEM_FILTER]) >>
  simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  irule reachable_block_successor >> simp[] >>
  qexists_tac `bb` >>
  Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def]
QED

Theorem flag_fails_remove_unreachable:
  ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks /\
  reachable fn bb.bb_label /\ bb_well_formed bb /\
  MEM i bb.bb_instructions /\ flag_fails fn.fn_blocks vs i ==>
  flag_fails (remove_unreachable_blocks fn).fn_blocks vs i
Proof
  strip_tac >>
  `!l. is_terminator i.inst_opcode /\ MEM (Label l) i.inst_operands ==>
       reachable fn l` by
    (rpt strip_tac >> irule reachable_block_successor >> simp[] >>
     qexists_tac `bb` >> simp[] >>
     irule bb_terminator_label_successor >> metis_tac[]) >>
  Cases_on `i.inst_opcode` >> gvs[flag_fails_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[]
  >- (irule revert_path_fuel_normalize >> qexists_tac `LENGTH fn.fn_blocks` >>
      irule revert_path_remove_unreachable >> simp[is_terminator_def]) >>
  Cases_on `h` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  irule revert_path_fuel_normalize >> qexists_tac `LENGTH fn.fn_blocks` >>
  irule revert_path_remove_unreachable >> simp[is_terminator_def] >>
  metis_tac[]
QED

Theorem flag_path_remove_unreachable:
  !xs fn bb vs.
    ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks /\
    reachable fn bb.bb_label /\ bb_well_formed bb /\
    (!i. MEM i xs ==> MEM i bb.bb_instructions) /\
    flag_path fn.fn_blocks vs xs ==>
    flag_path (remove_unreachable_blocks fn).fn_blocks vs xs
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> simp[flag_path_def] >> strip_tac >> simp[] >>
  Cases_on `flag_fails fn.fn_blocks vs h`
  >- (disj1_tac >> irule flag_fails_remove_unreachable >> metis_tac[MEM]) >>
  disj2_tac >> first_x_assum irule >> metis_tac[MEM]
QED

Theorem calls_flagged_remove_unreachable:
  !xs fn bb.
    ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks /\
    reachable fn bb.bb_label /\ bb_well_formed bb /\
    (!i. MEM i xs ==> MEM i bb.bb_instructions) /\
    calls_flagged fn.fn_blocks xs ==>
    calls_flagged (remove_unreachable_blocks fn).fn_blocks xs
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt gen_tac >> simp[calls_flagged_def] >> strip_tac >>
  conj_tac
  >- (strip_tac >> Cases_on `h.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      irule flag_path_remove_unreachable >> metis_tac[MEM]) >>
  first_x_assum irule >> metis_tac[MEM]
QED

Theorem remove_unreachable_call_checks_ok:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  call_checks_ok fn ==>
  call_checks_ok (remove_unreachable_blocks fn)
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- gvs[remove_unreachable_blocks_def] >>
  `!bb. MEM bb fn.fn_blocks /\ reachable fn bb.bb_label ==>
    calls_flagged (remove_unreachable_blocks fn).fn_blocks bb.bb_instructions` by
    (rpt strip_tac >> irule calls_flagged_remove_unreachable >>
     gvs[call_checks_ok_def, EVERY_MEM] >>
     qexists_tac `bb` >> simp[]) >>
  gvs[call_checks_ok_def, remove_unreachable_blocks_def, EVERY_MEM, MEM_FILTER]
QED

Theorem phi_prefix_partition_identity:
  !xs.
    (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
       (EL i xs).inst_opcode = PHI) ==>
    FILTER (\i. i.inst_opcode = PHI) xs ++
    FILTER (\i. i.inst_opcode <> PHI) xs = xs
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[] >> first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER (\i. i.inst_opcode <> PHI) xs = xs /\
   FILTER (\i. i.inst_opcode = PHI) xs = []` by
    gvs[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >>
  simp[]
QED

Theorem fix_phis_in_block_calls_flagged:
  bb_well_formed bb ==>
  (calls_flagged bbs (fix_phis_in_block ps bb).bb_instructions <=>
   calls_flagged bbs bb.bb_instructions)
Proof
  strip_tac >>
  `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions ++
   FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions = bb.bb_instructions` by
    (irule phi_prefix_partition_identity >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  qabbrev_tac `phis = FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions` >>
  qabbrev_tac `body_insts = FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions` >>
  `EVERY (\i. i.inst_opcode = PHI) phis /\
   EVERY (\i. i.inst_opcode <> PHI) body_insts` by
    simp[Abbr `phis`, Abbr `body_insts`, EVERY_FILTER] >>
  `MAP (fix_phi_inst ps) body_insts = body_insts` by
    (`MAP (fix_phi_inst ps) body_insts = MAP I body_insts` suffices_by simp[] >>
     irule MAP_CONG >> gvs[EVERY_MEM] >> rpt strip_tac >>
     irule fix_phi_inst_non_phi >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL)
    (MAP (fix_phi_inst ps) phis)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     irule (BETA_RULE (Q.INST [`P` |-> `\op. op <> CALL /\ op <> STATICCALL`]
       fix_phi_inst_opcode_property)) >> gvs[EVERY_MEM]) >>
  simp[fix_phis_in_block_def] >>
  qpat_x_assum `phis ++ body_insts = _` (fn th => once_rewrite_tac[GSYM th]) >>
  `FILTER (\i. i.inst_opcode = PHI) body_insts = [] /\
   FILTER (\i. i.inst_opcode <> PHI) body_insts = body_insts` by
    gvs[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) phis /\
   EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL)
     (FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst ps) phis)) /\
   EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL)
     (FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst ps) phis))` by
    gvs[EVERY_MEM, MEM_FILTER] >>
  simp[MAP_APPEND, FILTER_APPEND, GSYM APPEND_ASSOC,
       calls_flagged_prefix_no_calls]
QED

Theorem revert_path_fix_all_phis:
  !n fn l. EVERY bb_well_formed fn.fn_blocks /\
    revert_path fn.fn_blocks n l ==>
    revert_path (fix_all_phis fn).fn_blocks n l
Proof
  Induct >- simp[revert_path_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ _ _` mp_tac >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> BETA_TAC >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  `bb_well_formed (fix_phis_in_block (pred_labels fn bb.bb_label) bb)` by
    simp[simplifyCfgStructTheory.fix_phis_in_block_wf] >>
  `!ps. (fix_phis_in_block ps bb).bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fix_phis_in_block ps bb).bb_instructions` by
    (gen_tac >> conj_tac
     >- (`bb_well_formed (fix_phis_in_block ps bb)` by
           simp[simplifyCfgStructTheory.fix_phis_in_block_wf] >>
         gvs[bb_well_formed_def]) >>
     irule fix_phis_in_block_every >> simp[] >> rpt gen_tac >> disch_tac >>
     mp_tac (Q.INST [`code` |-> `INVOKE`, `actual_preds` |-> `ps`,
                     `inst` |-> `i`] fix_phi_inst_opcode_source) >> simp[]) >>
  `MEM (fix_phis_in_block (pred_labels fn bb.bb_label) bb)
       (fix_all_phis fn).fn_blocks` by
    (simp[fix_all_phis_def, MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> BETA_TAC >>
  qexists_tac `fix_phis_in_block (pred_labels fn bb.bb_label) bb` >>
  simp[bb_label_fix_phis_in_block, fix_phis_in_block_last] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem flag_fails_fix_all_phis:
  EVERY bb_well_formed fn.fn_blocks /\ flag_fails fn.fn_blocks vs i ==>
  flag_fails (fix_all_phis fn).fn_blocks vs i
Proof
  strip_tac >>
  `!l. revert_path fn.fn_blocks (LENGTH fn.fn_blocks) l ==>
    revert_path (fix_all_phis fn).fn_blocks (LENGTH (fix_all_phis fn).fn_blocks) l` by
    (rpt strip_tac >> irule revert_path_fuel_normalize >>
     qexists_tac `LENGTH fn.fn_blocks` >>
     irule revert_path_fix_all_phis >> simp[]) >>
  Cases_on `i.inst_opcode` >> gvs[flag_fails_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem fix_all_phis_call_checks_ok:
  EVERY bb_well_formed fn.fn_blocks /\ call_checks_ok fn ==>
  call_checks_ok (fix_all_phis fn)
Proof
  strip_tac >> simp[call_checks_ok_def, fix_all_phis_def, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  simp[fix_phis_in_block_calls_flagged] >>
  irule calls_flagged_environment >> qexists_tac `fn.fn_blocks` >>
  conj_tac
  >- (rpt strip_tac >> drule_all flag_fails_fix_all_phis >>
      simp[fix_all_phis_def]) >>
  gvs[call_checks_ok_def, EVERY_MEM]
QED

Theorem get_successors_no_labels:
  EVERY (\op. ~is_label_operand op) i.inst_operands ==>
  get_successors i = []
Proof
  strip_tac >> simp[get_successors_def] >>
  `FILTER IS_SOME (MAP venomState$get_label i.inst_operands) = []` suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MAP] >> gvs[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `x` >> gvs[venomStateTheory.get_label_def,
                          stackPlanTypesTheory.is_label_operand_def] >>
  first_x_assum drule >> simp[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shaped_terminator_jump_cases:
  label_positions_ok i /\ is_terminator i.inst_opcode ==>
  (i.inst_opcode = JMP /\ (?l. i.inst_operands = [Label l])) \/
  (i.inst_opcode = JNZ /\ (?c t f. i.inst_operands = [c; Label t; Label f] /\
     ~is_label_operand c /\ t <> f)) \/ get_successors i = []
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[is_terminator_def, label_positions_ok_def]
  >- (Cases_on `i.inst_operands` >> gvs[]
      >- simp[get_successors_def] >>
      Cases_on `h` >> gvs[stackPlanTypesTheory.is_label_operand_def]
      >- (irule get_successors_no_labels >>
          simp[stackPlanTypesTheory.is_label_operand_def])
      >- (irule get_successors_no_labels >>
          simp[stackPlanTypesTheory.is_label_operand_def]) >>
      Cases_on `t` >> gvs[stackPlanTypesTheory.is_label_operand_def])
  >- (Cases_on `?c t f. i.inst_operands = [c; Label t; Label f] /\
          ~is_label_operand c /\ t <> f` >- simp[] >>
      disj2_tac >> irule get_successors_no_labels >>
      Cases_on `i.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `h'` >> gvs[stackPlanTypesTheory.is_label_operand_def] >>
      Cases_on `t'` >> gvs[stackPlanTypesTheory.is_label_operand_def] >>
      Cases_on `h'` >> gvs[stackPlanTypesTheory.is_label_operand_def] >>
      Cases_on `t` >> gvs[stackPlanTypesTheory.is_label_operand_def]) >>
  irule get_successors_no_labels >> simp[]
QED

Theorem shaped_bb_single_successor_jmp:
  bb_well_formed bb /\ EVERY label_positions_ok bb.bb_instructions /\
  bb_succs bb = [l] ==>
  (LAST bb.bb_instructions).inst_opcode = JMP /\
  (LAST bb.bb_instructions).inst_operands = [Label l]
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `label_positions_ok (LAST bb.bb_instructions)` by
    (fs[EVERY_MEM] >> qpat_x_assum `!x. MEM x _ ==> _` irule >> simp[LAST_MEM]) >>
  drule shaped_terminator_jump_cases >>
  impl_tac >- gvs[bb_well_formed_def] >>
  strip_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def, listTheory.nub_def] >>
  Cases_on `c` >>
  gvs[stackPlanTypesTheory.is_label_operand_def,
      venomStateTheory.get_label_def, listTheory.nub_def]
QED

Theorem revert_path_step_witness:
  revert_path bbs n l ==>
  ?bb. MEM bb bbs /\ bb.bb_label = l /\ bb.bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    ((LAST bb.bb_instructions).inst_opcode = REVERT \/
     (LAST bb.bb_instructions).inst_opcode = JMP /\
     ?t m. (LAST bb.bb_instructions).inst_operands = [Label t] /\
       m < n /\ revert_path bbs m t)
Proof
  Cases_on `n` >> simp[revert_path_def, EXISTS_MEM] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  qexists_tac `n'` >> simp[]
QED

Theorem merge_revert_target_not_removed:
  can_merge_blocks fn a b /\ MEM a fn.fn_blocks /\ MEM c fn.fn_blocks /\
  c <> a /\ c.bb_instructions <> [] /\
  (LAST c.bb_instructions).inst_opcode = JMP /\
  (LAST c.bb_instructions).inst_operands = [Label t] ==>
  t <> b.bb_label
Proof
  strip_tac >> strip_tac >> gvs[] >>
  `MEM b.bb_label (bb_succs c)` by
    (Cases_on `c.bb_instructions` >>
     gvs[bb_succs_def, get_successors_def, is_terminator_def,
         venomStateTheory.get_label_def, listTheory.nub_def]) >>
  drule_all can_merge_blocks_unique_pred >> simp[]
QED

Theorem chain_merge_revert_step:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  bbs = replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks) /\
  l <> b.bb_label /\ revert_path fn.fn_blocks n l ==>
  ?c. MEM c bbs /\ c.bb_label = l /\ c.bb_instructions <> [] /\
      EVERY (\i. i.inst_opcode <> INVOKE) c.bb_instructions /\
      ((LAST c.bb_instructions).inst_opcode = REVERT \/
       ((LAST c.bb_instructions).inst_opcode = JMP /\
        ?t m. (LAST c.bb_instructions).inst_operands = [Label t] /\
          t <> b.bb_label /\ m < n /\ revert_path fn.fn_blocks m t))
Proof
  strip_tac >> drule revert_path_step_witness >> strip_tac >>
  Cases_on `bb = a` >>
  TRY (qpat_x_assum `bb = a` SUBST_ALL_TAC >> suspend "merged_root") >>
  qexists_tac `bb` >>
  `bb.bb_label <> a.bb_label` by
    (strip_tac >> `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
      lookup_block bb.bb_label fn.fn_blocks = SOME a` by
       (conj_tac >> irule MEM_lookup_block >> gvs[fn_labels_def]) >> gvs[]) >>
  `MEM bb bbs` by
    (gvs[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
     qexists_tac `bb` >> simp[]) >>
  simp[] >> qexists_tac `m` >> simp[] >>
  irule merge_revert_target_not_removed >> metis_tac[]
QED

Resume chain_merge_revert_step[merged_root]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `bb_well_formed a /\ EVERY label_positions_ok a.bb_instructions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `bb_succs a = [b.bb_label]` by gvs[can_merge_blocks_def] >>
  drule_all shaped_bb_single_successor_jmp >> strip_tac >> gvs[] >>
  qpat_x_assum `revert_path _ m _` (strip_assume_tac o MATCH_MP revert_path_step_witness) >>
  `bb = b` by
    (`lookup_block b.bb_label fn.fn_blocks = SOME bb /\
      lookup_block b.bb_label fn.fn_blocks = SOME b` by
       (conj_tac >> irule MEM_lookup_block >> gvs[fn_labels_def]) >> gvs[]) >>
  gvs[] >> qexists_tac `merge_blocks a b` >>
  `MEM (merge_blocks a b)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks))` by
    (simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
     qexists_tac `a` >> simp[]) >>
  `LAST (FRONT a.bb_instructions ++ b.bb_instructions) =
    LAST b.bb_instructions` by
    (Cases_on `b.bb_instructions` >> gvs[LAST_APPEND_CONS]) >>
  simp[merge_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (FRONT a.bb_instructions)` by
    (fs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]) >>
  simp[] >> qexists_tac `m'` >> simp[] >>
  irule merge_revert_target_not_removed >>
  qexistsl_tac [`a`, `b`, `fn`] >> simp[] >> strip_tac >> gvs[]
QED

Finalise chain_merge_revert_step

Theorem revert_path_chain_merge_base:
  !n fn a b bbs l.
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  bbs = replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks) /\
  l <> b.bb_label /\ revert_path fn.fn_blocks n l ==>
  ?k. revert_path bbs k l
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  drule_all chain_merge_revert_step >> strip_tac
  >- (qexists_tac `SUC 0` >>
      pure_rewrite_tac[revert_path_def, EXISTS_MEM] >>
      qexists_tac `c` >> metis_tac[]) >>
  `?k. revert_path bbs k t` by
    (first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  qexists_tac `SUC k` >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> qexists_tac `c` >>
  qpat_x_assum `bbs = _` kall_tac >> simp[]
QED

Theorem revert_path_map_observations:
  !n bbs l f.
  (!bb. MEM bb bbs ==>
    (f bb).bb_label = bb.bb_label /\
    ((f bb).bb_instructions = [] <=> bb.bb_instructions = []) /\
    LAST (f bb).bb_instructions = LAST bb.bb_instructions /\
    (EVERY (\i. i.inst_opcode <> INVOKE) (f bb).bb_instructions <=>
     EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions)) /\
  revert_path bbs n l ==> revert_path (MAP f bbs) n l
Proof
  Induct >- simp[revert_path_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ _ _` mp_tac >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> BETA_TAC >> strip_tac >>
  rename1 `MEM bb bbs` >>
  pure_once_rewrite_tac[revert_path_def] >>
  pure_rewrite_tac[EXISTS_MEM] >> qexists_tac `f bb` >>
  `MEM (f bb) (MAP f bbs)` by (simp[MEM_MAP] >> metis_tac[]) >>
  first_assum (qspec_then `bb` mp_tac) >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem revert_path_update_succ_phi_labels:
  !n bbs l old new succs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    EVERY bb_well_formed bbs /\ revert_path bbs n l ==>
    revert_path (update_succ_phi_labels old new bbs succs) n l
Proof
  rpt strip_tac >>
  asm_simp_tac (srw_ss())
    [simplifyCfgReachusesTheory.update_succ_phi_labels_exact] >>
  irule revert_path_map_observations >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  drule (phi_map_revert_observations |> Q.INST
    [`f` |-> `\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i`]
    |> BETA_RULE) >>
  disch_then (qspecl_then [`old`, `new`] mp_tac) >>
  (impl_tac >- (conj_tac >- (gen_tac >> IF_CASES_TAC >> simp[subst_label_inst_def]) >> simp[])) >>
  simp[]
QED

Theorem revert_path_chain_merge:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  bbs = update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b)) /\
  l <> b.bb_label /\ revert_path fn.fn_blocks n l ==>
  revert_path bbs (LENGTH bbs) l
Proof
  rpt strip_tac >>
  qabbrev_tac `merged_bbs = replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks)` >>
  `?k. revert_path merged_bbs k l` by
    (irule revert_path_chain_merge_base >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) merged_bbs)` by
    (simp[Abbr `merged_bbs`, fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> fs[fn_labels_def]) >>
  `EVERY bb_well_formed merged_bbs` by
    (simp[Abbr `merged_bbs`] >> irule EVERY_replace_block >>
     conj_tac
     >- (irule bb_well_formed_merge_blocks >> fs[EVERY_MEM, can_merge_blocks_def]) >>
     fs[remove_block_def, EVERY_MEM, MEM_FILTER]) >>
  irule revert_path_fuel_normalize >>
  qexists_tac `k` >>
  qpat_x_assum `bbs = _` SUBST1_TAC >>
  irule revert_path_update_succ_phi_labels >> simp[]
QED

Theorem can_bypass_jump_single_jmp:
  bb_well_formed b /\ EVERY label_positions_ok b.bb_instructions /\
  can_bypass_jump fn a b ==>
  ?j target. b.bb_instructions = [j] /\ j.inst_opcode = JMP /\
    j.inst_operands = [Label target] /\ bb_succs b = [target]
Proof
  strip_tac >>
  `LENGTH b.bb_instructions = 1 /\ LENGTH (bb_succs b) = 1` by
    fs[can_bypass_jump_def, num_succs_def] >>
  Cases_on `b.bb_instructions` >> gvs[] >>
  Cases_on `bb_succs b` >> gvs[] >>
  drule shaped_bb_single_successor_jmp >> simp[]
QED

Theorem revert_path_single_jmp_target:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM b bbs /\
  b.bb_instructions = [j] /\ j.inst_opcode = JMP /\
  j.inst_operands = [Label target] /\ revert_path bbs n b.bb_label ==>
  ?m. m < n /\ revert_path bbs m target
Proof
  strip_tac >> drule revert_path_step_witness >> strip_tac >>
  `bb = b` by
    (`lookup_block b.bb_label bbs = SOME bb /\
      lookup_block b.bb_label bbs = SOME b` by
       (conj_tac >> irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Theorem flag_path_replace_terminal_selective:
  !xs oldbbs newbbs j ys.
  (!i vs. MEM i xs /\ flag_fails oldbbs vs i ==> flag_fails newbbs vs i) /\
  (!vs. flag_path oldbbs vs [j] ==> flag_path newbbs vs ys) ==>
  !vs. flag_path oldbbs vs (xs ++ [j]) ==> flag_path newbbs vs (xs ++ ys)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gen_tac >> pure_rewrite_tac[APPEND, flag_path_def] >>
  qmatch_goalsub_abbrev_tac `flag_path oldbbs nextvs (xs ++ [j])` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `!i ws. MEM i xs /\ flag_fails oldbbs ws i ==> flag_fails newbbs ws i` by
    (rpt strip_tac >> qpat_x_assum `!i ws. MEM i (h::xs) /\ _ ==> _` irule >> simp[]) >>
  qpat_x_assum `!oldbbs newbbs j ys. _` (qspecl_then [`oldbbs`, `newbbs`, `j`, `ys`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then (qspec_then `nextvs` assume_tac) >>
  `flag_fails oldbbs vs h ==> flag_fails newbbs vs h` by
    (strip_tac >> qpat_x_assum `!i ws. MEM i (h::xs) /\ _ ==> _` irule >> simp[]) >>
  metis_tac[]
QED

Theorem calls_flagged_replace_terminal_selective:
  !xs oldbbs newbbs j ys.
  (!i vs. MEM i xs /\ flag_fails oldbbs vs i ==> flag_fails newbbs vs i) /\
  (!vs. flag_path oldbbs vs [j] ==> flag_path newbbs vs ys) /\
  calls_flagged oldbbs (xs ++ [j]) /\ calls_flagged newbbs ys ==>
  calls_flagged newbbs (xs ++ ys)
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[calls_flagged_def] >> strip_tac >>
  conj_tac
  >- (strip_tac >> Cases_on `h.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      irule flag_path_replace_terminal_selective >> metis_tac[MEM]) >>
  first_x_assum irule >> metis_tac[MEM]
QED

Theorem revert_path_chain_merge_raw:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  raw = replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks) /\
  l <> b.bb_label /\ revert_path fn.fn_blocks n l ==>
  revert_path raw (LENGTH raw) l
Proof
  strip_tac >> irule revert_path_fuel_normalize >>
  irule revert_path_chain_merge_base >> metis_tac[]
QED

Theorem flag_fails_nonterminator_environment:
  ~is_terminator i.inst_opcode /\ flag_fails oldbbs vs i ==>
  flag_fails newbbs vs i
Proof
  Cases_on `i.inst_opcode` >> simp[is_terminator_def, flag_fails_def]
QED

Theorem flag_fails_front_environment:
  bb_well_formed bb /\ MEM i (FRONT bb.bb_instructions) /\
  flag_fails oldbbs vs i ==> flag_fails newbbs vs i
Proof
  strip_tac >> irule flag_fails_nonterminator_environment >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `MEM i _` mp_tac >> rewrite_tac[MEM_EL] >> strip_tac >>
  drule_all bb_front_no_terminator >> simp[]
QED

Theorem flag_fails_chain_merge_other:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  raw = replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks) /\
  MEM c fn.fn_blocks /\ c <> a /\ MEM i c.bb_instructions /\
  flag_fails fn.fn_blocks vs i ==> flag_fails raw vs i
Proof
  strip_tac >>
  `bb_well_formed c` by gvs[EVERY_MEM] >>
  `!l. is_terminator i.inst_opcode /\ MEM (Label l) i.inst_operands ==>
       l <> b.bb_label` by
    (rpt strip_tac >> gvs[] >>
     `MEM b.bb_label (bb_succs c)` by
       (irule bb_terminator_label_successor >> metis_tac[]) >>
     drule_all can_merge_blocks_unique_pred >> simp[]) >>
  `!l. is_terminator i.inst_opcode /\ MEM (Label l) i.inst_operands /\
       revert_path fn.fn_blocks (LENGTH fn.fn_blocks) l ==>
       revert_path raw (LENGTH raw) l` by
    (rpt strip_tac >> irule revert_path_chain_merge_raw >> metis_tac[]) >>
  Cases_on `i.inst_opcode` >> gvs[flag_fails_def, is_terminator_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  metis_tac[MEM]
QED

Theorem calls_flagged_chain_merge_other:
  ALL_DISTINCT (fn_labels fn) /\ EVERY bb_well_formed fn.fn_blocks /\
  EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  raw = replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks) /\
  MEM c fn.fn_blocks /\ c <> a /\ calls_flagged fn.fn_blocks c.bb_instructions ==>
  calls_flagged raw c.bb_instructions
Proof
  strip_tac >>
  `bb_well_formed c` by gvs[EVERY_MEM] >>
  `c.bb_instructions <> [] /\ is_terminator (LAST c.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `!i vs. MEM i c.bb_instructions /\ flag_fails fn.fn_blocks vs i ==>
      flag_fails raw vs i` by
    (rpt strip_tac >> irule flag_fails_chain_merge_other >> metis_tac[]) >>
  `calls_flagged fn.fn_blocks (FRONT c.bb_instructions ++ [LAST c.bb_instructions])` by
    simp[APPEND_FRONT_LAST] >>
  `calls_flagged raw (FRONT c.bb_instructions ++ [LAST c.bb_instructions])` suffices_by
    simp[APPEND_FRONT_LAST] >>
  irule calls_flagged_replace_terminal_selective >>
  conj_tac
  >- (Cases_on `(LAST c.bb_instructions).inst_opcode` >>
      gvs[is_terminator_def, calls_flagged_def]) >>
  qexistsl_tac [`LAST c.bb_instructions`, `fn.fn_blocks`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> first_x_assum irule >>
      metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]) >>
  gen_tac >> simp[flag_path_def] >>
      qpat_x_assum `!i vs. MEM i c.bb_instructions /\ _ ==> _`
        (qspec_then `LAST c.bb_instructions` mp_tac) >>
      simp[LAST_MEM]
QED

Theorem simplify_cfg_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  call_checks_ok (simplify_cfg_fn fn)
Proof
  cheat
QED
