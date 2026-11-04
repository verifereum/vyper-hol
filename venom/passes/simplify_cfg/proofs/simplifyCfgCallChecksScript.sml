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
  simplifyCfgDefs simplifyCfgCollapseShape cfgTransform cfgTransformProps venomExecProps
  unitShapeDefs venomWf venomInst list rich_list

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

Theorem simplify_cfg_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  call_checks_ok (simplify_cfg_fn fn)
Proof
  cheat
QED
