(*
 * DFT keeps every external call's success flag checked (call_checks_ok).
 * TOP-LEVEL: dft_blocks_call_checks_ok.
 *
 * call_checks_ok is part of fn_shape_ok, which the admitted O1 step
 * contracts owe for every pass output; this proves the DFT part of that
 * obligation at block granularity, as a soundness check on the admission.
 *)
Theory dftCallChecks
Ancestors
  dftCorrectnessFinal dftCorrectness dftStructural dftTopoSort dftWf dftIdempotent
  unitShapeDefs venomWf dftDefs list rich_list sorting finite_map relation

(* Identity matching is deliberately stated for every non-flippable opcode,
   rather than enumerating the particular call-check opcodes. *)
Theorem from_block_nonflippable_identity:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi x /\ MEM y bi /\
    x.inst_id = y.inst_id /\ ~is_flippable y.inst_opcode ==>
    x = y
Proof
  rpt strip_tac >>
  gvs[from_block_def] >>
  `j = y` by
    metis_tac[flip_operands_inst_id, all_distinct_map_mem_inj] >>
  gvs[]
QED

Theorem dft_block_same_last:
  !fn bb order.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  `block_perm_of fn bb` by
    (simp[block_perm_of_def] >> qexists_tac `bb` >>
     simp[EVERY_MEM, MEM_FILTER, from_block_def] >> metis_tac[]) >>
  `block_perm_of fn (dft_block order bb)` by
    metis_tac[dft_block_preserves_perm_of] >>
  `bb_well_formed (dft_block order bb)` by
    metis_tac[dft_block_well_formed_gen] >>
  `bb.bb_label = (dft_block order bb).bb_label` by
    simp[dft_block_def, LET_THM] >>
  metis_tac[block_perm_of_same_last]
QED

Theorem dft_block_schedule_order:
  !bb order.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    output_producer_before bb.bb_instructions
      (FILTER (\i. ~is_pseudo i.inst_opcode)
        (dft_block order bb).bb_instructions) /\
    output_eda_before (build_eda bb.bb_instructions)
      (FILTER (\i. ~is_pseudo i.inst_opcode)
        (dft_block order bb).bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  `eda_wf (build_eda bi) bi` by simp[build_eda_wf] >>
  `np_defs_before_uses bi /\ bi <> [] /\
   is_terminator (LAST bi).inst_opcode /\
   (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
        k = PRE (LENGTH bi))` by
    gvs[bb_well_formed_def, non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `eda_topo_compatible bi (build_eda bi) order` by
    (irule eda_topo_compatible_gen_weak_plain >> simp[Abbr `bi`]) >>
  qabbrev_tac `entries = entry_instructions bi order (build_eda bi)` >>
  qabbrev_tac `sched = schedule_from_entries bi order (build_eda bi)
    (build_offspring_map bi order) entries` >>
  `EVERY (\i. MEM i bi) entries` by simp[Abbr `entries`, entry_instructions_mem] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode)
     (dft_block order bb).bb_instructions = sched` by
    (simp[dft_block_def, LET_THM, Abbr `sched`, Abbr `entries`, Abbr `bi`,
          FILTER_APPEND_DISTRIB, FILTER_FILTER] >>
     simp[FILTER_EQ_ID]) >>
  simp[] >>
  conj_tac >> simp[Abbr `sched`] >>
  metis_tac[schedule_output_producer_before, schedule_output_eda_before]
QED

Theorem dft_block_nonflippable_mem:
  !bb order i.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\j. j.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
    ~is_flippable i.inst_opcode ==>
    MEM i (dft_block order bb).bb_instructions
Proof
  rpt strip_tac >>
  drule_all dft_block_perm_ids >>
  disch_then (qspec_then `order` assume_tac) >>
  `MEM i.inst_id (MAP (\j. j.inst_id)
    (FILTER (\j. ~is_pseudo j.inst_opcode)
       (dft_block order bb).bb_instructions))` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[MEM_MAP, MEM_FILTER] >>
  rename1 `MEM j (dft_block order bb).bb_instructions` >>
  `from_block bb.bb_instructions j` by
    (irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]) >>
  `j = i` by metis_tac[from_block_nonflippable_identity] >>
  gvs[]
QED

Theorem effect_write_fold_lookup:
  !effs et inst eff.
    FLOOKUP (FOLDL (\acc weff.
      acc with <|et_last_write := acc.et_last_write |+ (weff, inst);
                 et_all_reads := acc.et_all_reads |+ (weff, [])|>)
      et effs).et_last_write eff =
    if MEM eff effs then SOME inst else FLOOKUP et.et_last_write eff
Proof
  Induct >- simp[] >> rpt gen_tac >>
  pure_rewrite_tac[FOLDL] >>
  first_x_assum (rewrite_tac o single) >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `MEM eff effs` >> simp[] >>
  Cases_on `eff = h` >> simp[]
QED

Theorem compute_effect_deps_last_write:
  !et inst eff.
    FLOOKUP (SND (compute_effect_deps et inst)).et_last_write eff =
    if MEM eff (effects_to_list (write_effects inst.inst_opcode))
    then SOME inst else FLOOKUP et.et_last_write eff
Proof
  simp[compute_effect_deps_def, LET_THM, read_foldl_last_write,
       SRULE [] effect_write_fold_lookup]
QED

Theorem compute_effect_deps_writer_dep:
  !et inst eff w.
    FLOOKUP et.et_last_write eff = SOME w /\
    w.inst_id <> inst.inst_id /\
    MEM eff (effects_to_list (write_effects inst.inst_opcode) ++
             effects_to_list (read_effects inst.inst_opcode)) ==>
    MEM w (FST (compute_effect_deps et inst))
Proof
  rpt strip_tac >>
  simp[compute_effect_deps_def, LET_THM] >>
  Cases_on `MEM eff (effects_to_list (write_effects inst.inst_opcode))`
  >- (disj1_tac >> simp[MEM_FLAT, MEM_MAP] >>
      qexists_tac `et_get_reads et eff ++ [w]` >> simp[] >>
      qexists_tac `eff` >> simp[]) >>
  disj2_tac >> simp[MEM_MAP, MEM_FILTER] >>
  qexists_tac `SOME w` >> simp[] >>
  qexists_tac `eff` >> gvs[MEM_APPEND]
QED

Definition eda_scan_step_def:
  eda_scan_step (eda,et) i =
    let (ds,et') = compute_effect_deps et i in
    (eda |+ (i.inst_id,ds),et')
End

Definition eda_id_edge_def:
  eda_id_edge eda x y <=>
    ?d ds. FLOOKUP eda y = SOME ds /\ MEM d ds /\
           ~is_pseudo d.inst_opcode /\ d.inst_id = x
End

Definition eda_writer_inv_def:
  eda_writer_inv p eda et <=>
    ALL_DISTINCT (MAP (\i. i.inst_id) p) /\
    EVERY (\i. ~is_pseudo i.inst_opcode) p /\
    FDOM eda SUBSET set (MAP (\i. i.inst_id) p) /\
    (!eff w. FLOOKUP et.et_last_write eff = SOME w ==> MEM w p) /\
    (!eff v. MEM v p /\ MEM eff (effects_to_list (write_effects v.inst_opcode)) ==>
      ?w. FLOOKUP et.et_last_write eff = SOME w /\
          RTC (eda_id_edge eda) v.inst_id w.inst_id)
End

Theorem eda_writer_inv_empty:
  eda_writer_inv [] FEMPTY empty_effect_track
Proof
  simp[eda_writer_inv_def, empty_effect_track_def]
QED

Theorem eda_scan_step_old_edge:
  !p eda et i eda' et'.
    eda_writer_inv p eda et /\
    ~MEM i.inst_id (MAP (\j. j.inst_id) p) /\
    ~is_pseudo i.inst_opcode /\
    eda_scan_step (eda,et) i = (eda',et') ==>
    !x y. eda_id_edge eda x y ==> eda_id_edge eda' x y
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compute_effect_deps et i` >>
  gvs[eda_scan_step_def, eda_writer_inv_def, eda_id_edge_def,
      pairTheory.UNCURRY_DEF, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `y <> i.inst_id` by
    (gvs[pred_setTheory.SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  metis_tac[]
QED

Theorem eda_scan_step_writer_edge:
  !p eda et i eda' et' eff w.
    eda_writer_inv p eda et /\
    ~MEM i.inst_id (MAP (\j. j.inst_id) p) /\
    ~is_pseudo i.inst_opcode /\
    eda_scan_step (eda,et) i = (eda',et') /\
    FLOOKUP et.et_last_write eff = SOME w /\
    MEM eff (effects_to_list (write_effects i.inst_opcode) ++
             effects_to_list (read_effects i.inst_opcode)) ==>
    eda_id_edge eda' w.inst_id i.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `MEM w p` by metis_tac[eda_writer_inv_def] >>
  `~is_pseudo w.inst_opcode` by
    gvs[eda_writer_inv_def, EVERY_MEM] >>
  `w.inst_id <> i.inst_id` by
    (simp[] >> metis_tac[MEM_MAP]) >>
  drule_all compute_effect_deps_writer_dep >> strip_tac >>
  Cases_on `compute_effect_deps et i` >>
  gvs[eda_scan_step_def, eda_id_edge_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem eda_scan_step_writer_inv:
  !p eda et i eda' et'.
    eda_writer_inv p eda et /\
    ~MEM i.inst_id (MAP (\j. j.inst_id) p) /\
    ~is_pseudo i.inst_opcode /\
    eda_scan_step (eda,et) i = (eda',et') ==>
    eda_writer_inv (p ++ [i]) eda' et'
Proof
  rpt gen_tac >> strip_tac >>
  `!x y. eda_id_edge eda x y ==> eda_id_edge eda' x y` by
    metis_tac[eda_scan_step_old_edge] >>
  `!x y. RTC (eda_id_edge eda) x y ==> RTC (eda_id_edge eda') x y` by
    (rpt strip_tac >> irule RTC_MONOTONE >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!eff. FLOOKUP et'.et_last_write eff =
    if MEM eff (effects_to_list (write_effects i.inst_opcode)) then SOME i
    else FLOOKUP et.et_last_write eff` by
    (Cases_on `compute_effect_deps et i` >>
     gvs[eda_scan_step_def] >> metis_tac[compute_effect_deps_last_write, pairTheory.SND]) >>
  `eda' = eda |+ (i.inst_id,FST (compute_effect_deps et i))` by
    (Cases_on `compute_effect_deps et i` >> gvs[eda_scan_step_def]) >>
  qpat_x_assum `eda_writer_inv _ _ _` mp_tac >>
  simp[eda_writer_inv_def] >> strip_tac >>
  simp[eda_writer_inv_def, ALL_DISTINCT_APPEND, EVERY_APPEND,
       pred_setTheory.SUBSET_DEF] >>
  rpt conj_tac
  >- (gvs[pred_setTheory.SUBSET_DEF, MEM_MAP] >> metis_tac[])
  >- (rpt strip_tac >> Cases_on `MEM eff (effects_to_list (write_effects i.inst_opcode))` >>
      gvs[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  Cases_on `v = i`
  >- (gvs[] >> metis_tac[RTC_REFL]) >>
  fs[] >>
  first_assum (drule_all_then strip_assume_tac) >>
  Cases_on `MEM eff (effects_to_list (write_effects i.inst_opcode))`
  >- (qexists_tac `i` >> simp[] >>
      `eda_id_edge eda' w.inst_id i.inst_id` by
        (irule eda_scan_step_writer_edge >> simp[] >>
         goal_assum (drule_at Any) >>
         qexistsl_tac [`eda`, `et'`, `p`] >>
         simp[eda_writer_inv_def] >> metis_tac[]) >>
      metis_tac[RTC_RULES_RIGHT1]) >>
  qexists_tac `w` >> simp[]
QED

Theorem eda_scan_fold_inv:
  !xs p eda et eda' et'.
    eda_writer_inv p eda et /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (p ++ xs)) /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    FOLDL eda_scan_step (eda,et) xs = (eda',et') ==>
    eda_writer_inv (p ++ xs) eda' et' /\
    (!x y. eda_id_edge eda x y ==> eda_id_edge eda' x y)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `eda_scan_step (eda,et) h` >>
  `~MEM h.inst_id (MAP (\j. j.inst_id) p)` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `~is_pseudo h.inst_opcode` by gvs[] >>
  `eda_writer_inv (p ++ [h]) q r` by
    metis_tac[eda_scan_step_writer_inv] >>
  `!x y. eda_id_edge eda x y ==> eda_id_edge q x y` by
    metis_tac[eda_scan_step_old_edge] >>
  first_x_assum drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[FOLDL, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem eda_scan_split_writer_path:
  !p eda et c s eda' et' w eff.
    eda_writer_inv p eda et /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (p ++ c::s)) /\
    EVERY (\i. ~is_pseudo i.inst_opcode) (c::s) /\
    MEM w p /\ MEM eff (effects_to_list (write_effects w.inst_opcode)) /\
    MEM eff (effects_to_list (write_effects c.inst_opcode) ++
             effects_to_list (read_effects c.inst_opcode)) /\
    FOLDL eda_scan_step (eda,et) (c::s) = (eda',et') ==>
    TC (eda_id_edge eda') w.inst_id c.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `?v. FLOOKUP et.et_last_write eff = SOME v /\
       RTC (eda_id_edge eda) w.inst_id v.inst_id` by
    metis_tac[eda_writer_inv_def] >>
  Cases_on `eda_scan_step (eda,et) c` >>
  `~MEM c.inst_id (MAP (\j. j.inst_id) p) /\ ~is_pseudo c.inst_opcode` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `eda_writer_inv (p ++ [c]) q r` by
    metis_tac[eda_scan_step_writer_inv] >>
  `!x y. eda_id_edge eda x y ==> eda_id_edge q x y` by
    metis_tac[eda_scan_step_old_edge] >>
  `eda_id_edge q v.inst_id c.inst_id` by
    metis_tac[eda_scan_step_writer_edge] >>
  `RTC (eda_id_edge q) w.inst_id v.inst_id` by
    (irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[]) >>
  `TC (eda_id_edge q) w.inst_id c.inst_id` by
    metis_tac[EXTEND_RTC_TC_RIGHT1] >>
  `!x y. eda_id_edge q x y ==> eda_id_edge eda' x y` by
    (rpt strip_tac >> irule (cj 2 eda_scan_fold_inv) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`r`, `et'`, `p ++ [c]`, `s`] >>
     gvs[FOLDL, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  irule TC_MONOTONE >> goal_assum (drule_at Any) >> simp[]
QED

Theorem build_eda_writer_path:
  !bi a b eff.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    a < b /\ b < LENGTH bi /\
    ~is_pseudo (EL a bi).inst_opcode /\
    ~is_pseudo (EL b bi).inst_opcode /\
    MEM eff (effects_to_list (write_effects (EL a bi).inst_opcode)) /\
    MEM eff (effects_to_list (write_effects (EL b bi).inst_opcode) ++
             effects_to_list (read_effects (EL b bi).inst_opcode)) ==>
    TC (eda_id_edge (build_eda bi)) (EL a bi).inst_id (EL b bi).inst_id
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = FILTER (\i. ~is_pseudo i.inst_opcode) (TAKE b bi)` >>
  qabbrev_tac `s = FILTER (\i. ~is_pseudo i.inst_opcode) (DROP (SUC b) bi)` >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bi = p ++ EL b bi::s` by
    (qspec_then `b` (qspec_then `bi` mp_tac) TAKE_DROP_SUC >>
     simp[] >> disch_then (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
     simp[FILTER_APPEND_DISTRIB, Abbr `p`, Abbr `s`]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (p ++ EL b bi::s))` by
    (qpat_x_assum `FILTER _ bi = _` (fn th => rewrite_tac[GSYM th]) >>
     metis_tac[all_distinct_map_filter]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) p /\
   EVERY (\i. ~is_pseudo i.inst_opcode) (EL b bi::s)` by
    simp[Abbr `p`, Abbr `s`, EVERY_FILTER] >>
  `MEM (EL a bi) p` by
    (simp[Abbr `p`, MEM_FILTER] >>
     `a < LENGTH (TAKE b bi)` by simp[] >>
     metis_tac[MEM_EL, EL_TAKE]) >>
  Cases_on `FOLDL eda_scan_step (FEMPTY,empty_effect_track) p` >>
  `eda_writer_inv p q r` by
    (qspec_then `p` (qspec_then `[]` mp_tac) eda_scan_fold_inv >>
     disch_then (qspecl_then [`FEMPTY`, `empty_effect_track`, `q`, `r`] mp_tac) >>
     gvs[eda_writer_inv_empty, ALL_DISTINCT_APPEND]) >>
  Cases_on `FOLDL eda_scan_step (q,r) (EL b bi::s)` >>
  `build_eda bi = q'` by
    (`(\(acc_map,et) inst. eda_scan_step (acc_map,et) inst) = eda_scan_step` by
       simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
     simp[build_eda_def, GSYM eda_scan_step_def] >>
     gvs[FOLDL_APPEND]) >>
  simp[] >> irule eda_scan_split_writer_path >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem output_eda_path_before:
  !eda output x y k.
    output_eda_before eda output /\
    TC (eda_id_edge eda) x y /\
    k < LENGTH output /\ (EL k output).inst_id = y ==>
    ?m. m < k /\ (EL m output).inst_id = x
Proof
  ntac 2 gen_tac >>
  qsuff_tac `!x y. TC (eda_id_edge eda) x y ==>
    !k. output_eda_before eda output /\
        k < LENGTH output /\ (EL k output).inst_id = y ==>
        ?m. m < k /\ (EL m output).inst_id = x`
  >- metis_tac[] >>
  ho_match_mp_tac TC_INDUCT_RIGHT1 >> conj_tac
  >- (rpt strip_tac >>
      gvs[eda_id_edge_def, output_eda_before_def] >>
      first_x_assum drule >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `?j. j < k /\ (EL j output).inst_id = y` by
    (gvs[eda_id_edge_def, output_eda_before_def] >>
     qpat_x_assum `!k d. _` drule >> simp[] >> metis_tac[]) >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `m` >> simp[]
QED

Theorem build_eda_writer_before:
  !bi a b eff output k.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    a < b /\ b < LENGTH bi /\
    ~is_pseudo (EL a bi).inst_opcode /\
    ~is_pseudo (EL b bi).inst_opcode /\
    MEM eff (effects_to_list (write_effects (EL a bi).inst_opcode)) /\
    MEM eff (effects_to_list (write_effects (EL b bi).inst_opcode) ++
             effects_to_list (read_effects (EL b bi).inst_opcode)) /\
    output_eda_before (build_eda bi) output /\
    k < LENGTH output /\ (EL k output).inst_id = (EL b bi).inst_id ==>
    ?m. m < k /\ (EL m output).inst_id = (EL a bi).inst_id
Proof
  rpt strip_tac >> drule_all build_eda_writer_path >>
  strip_tac >> irule output_eda_path_before >> metis_tac[]
QED

Theorem dft_block_writer_before_call:
  !bb order bi out a b k.
    bi = bb.bb_instructions /\
    out = FILTER (\i. ~is_pseudo i.inst_opcode)
            (dft_block order bb).bb_instructions /\
    bb_well_formed bb /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    non_pseudo_defs_before_uses bi /\ a < b /\ b < LENGTH bi /\
    ~is_pseudo (EL a bi).inst_opcode /\
    ((EL b bi).inst_opcode = CALL \/ (EL b bi).inst_opcode = STATICCALL) /\
    write_effects (EL a bi).inst_opcode <> {} /\
    k < LENGTH out /\ (EL k out).inst_id = (EL b bi).inst_id ==>
    ?m. m < k /\ (EL m out).inst_id = (EL a bi).inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `output_eda_before (build_eda bi) out` by
    metis_tac[dft_block_schedule_order] >>
  `?eff. MEM eff (effects_to_list (write_effects (EL a bi).inst_opcode))` by
    (pure_rewrite_tac[effects_to_list_def, MEM_FILTER] >>
     `?e. e IN write_effects (EL a bi).inst_opcode` by
       metis_tac[pred_setTheory.MEMBER_NOT_EMPTY] >>
     qexists_tac `e` >> Cases_on `e` >> simp[]) >>
  irule build_eda_writer_before >>
  simp[venomInstTheory.is_pseudo_def] >> qexistsl_tac [`b`, `eff`] >>
  gvs[] >>
  simp[venomInstTheory.is_pseudo_def, venomEffectsTheory.read_effects_def] >>
  disj2_tac >> pure_rewrite_tac[effects_to_list_def, MEM_FILTER] >>
  Cases_on `eff` >> simp[venomEffectsTheory.all_effects_def]
QED

Theorem dft_block_no_invoke:
  !bb order.
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (dft_block order bb).bb_instructions
Proof
  rpt gen_tac >> simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
  rename1 `MEM i (dft_block order bb).bb_instructions` >>
  `from_block bb.bb_instructions i` by
    (irule dft_block_from_orig >> qexists_tac `order` >>
     simp[MEM_FILTER, venomInstTheory.is_pseudo_def]) >>
  `(flip_operands i).inst_opcode = INVOKE` by
    (simp[flip_operands_def, passSharedDefsTheory.is_comparator_def] >>
     BasicProvers.every_case_tac >> simp[]) >>
  gvs[from_block_def] >> metis_tac[flip_operands_involution]
QED

Theorem dft_blocks_revert_path:
  !n fn bbs' l.
    wf_function fn /\
    EVERY (\bb. bb_well_formed bb /\
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
      non_pseudo_defs_before_uses bb.bb_instructions) fn.fn_blocks /\
    LIST_REL (\bb bb'. bb' = bb \/ ?order. bb' = dft_block order bb)
      fn.fn_blocks bbs' /\ revert_path fn.fn_blocks n l ==>
    revert_path bbs' n l
Proof
  Induct >- simp[revert_path_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ (SUC n) _` mp_tac >>
  simp[Once revert_path_def, EXISTS_MEM] >> strip_tac >>
  `?bb'. MEM bb' bbs' /\
     (bb' = bb \/ ?order. bb' = dft_block order bb)` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     simp[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  `bb_well_formed bb /\
   ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
   non_pseudo_defs_before_uses bb.bb_instructions` by
    (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `bb'.bb_label = bb.bb_label /\ bb'.bb_instructions <> [] /\
   LAST bb'.bb_instructions = LAST bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions` by
    (Cases_on `bb' = bb` >- simp[] >>
     gvs[] >>
     `bb_well_formed (dft_block order bb)` by
       metis_tac[dft_block_well_formed_gen] >>
     `LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions` by
       (irule dft_block_same_last >> simp[] >> qexists_tac `fn` >> simp[]) >>
     `(dft_block order bb).bb_instructions <> []` by
       gvs[bb_well_formed_def] >>
     simp[dft_block_no_invoke, dft_block_def, LET_THM]) >>
  simp[Once revert_path_def, EXISTS_MEM] >> qexists_tac `bb'` >>
  simp[] >> BasicProvers.every_case_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_blocks_flag_fails:
  !fn bbs' vs i.
    wf_function fn /\
    EVERY (\bb. bb_well_formed bb /\
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
      non_pseudo_defs_before_uses bb.bb_instructions) fn.fn_blocks /\
    LIST_REL (\bb bb'. bb' = bb \/ ?order. bb' = dft_block order bb)
      fn.fn_blocks bbs' /\ flag_fails fn.fn_blocks vs i ==>
    flag_fails bbs' vs i
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH bbs' = LENGTH fn.fn_blocks` by metis_tac[LIST_REL_LENGTH] >>
  `!n l. revert_path fn.fn_blocks n l ==> revert_path bbs' n l` by
    (rpt strip_tac >> irule dft_blocks_revert_path >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `flag_fails _ _ _` mp_tac >>
  Cases_on `i.inst_opcode` >> simp[flag_fails_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Definition cc_copy_def:
  cc_copy i u v <=> i.inst_opcode = ASSIGN /\
    i.inst_operands = [Var u] /\ MEM v i.inst_outputs
End

Definition copy_chain_def:
  (copy_chain vs [] x <=> MEM x vs) /\
  (copy_chain vs (i::is) x <=>
    copy_chain vs is x \/
    ?u v. MEM u vs /\ cc_copy i u v /\ copy_chain [v] is x)
End

Definition check_witness_def:
  check_witness bbs vs is <=>
    ?pre chk post.
      is = pre ++ chk::post /\
      EVERY (\i. i.inst_opcode <> INVOKE) pre /\
      (flag_fails bbs [] chk \/
       (EVERY (\i. write_effects i.inst_opcode = empty_effects) pre /\
        ?x. copy_chain vs pre x /\ flag_fails bbs [x] chk))
End

Theorem copy_chain_empty:
  !is x. ~copy_chain [] is x
Proof
  Induct >> simp[copy_chain_def]
QED

Theorem copy_chain_roots:
  !is vs x. copy_chain vs is x <=>
    ?u. MEM u vs /\ copy_chain [u] is x
Proof
  Induct >> pure_rewrite_tac[copy_chain_def, MEM] >> metis_tac[]
QED

Theorem copy_chain_union:
  !as bs is x. copy_chain (as ++ bs) is x <=>
    copy_chain as is x \/ copy_chain bs is x
Proof
  once_rewrite_tac[copy_chain_roots] >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem copy_chain_mono:
  !as bs is x.
    (!v. MEM v as ==> MEM v bs) /\ copy_chain as is x ==>
    copy_chain bs is x
Proof
  once_rewrite_tac[copy_chain_roots] >> metis_tac[]
QED

Theorem copy_chain_append:
  !pre vs post x. copy_chain vs (pre ++ post) x <=>
    ?u. copy_chain vs pre u /\ copy_chain [u] post x
Proof
  Induct
  >- (simp[copy_chain_def] >> metis_tac[copy_chain_roots]) >>
  pure_rewrite_tac[APPEND, copy_chain_def] >> metis_tac[]
QED

Theorem copy_chain_insert:
  !vs pre i post u v x.
    copy_chain vs pre u /\ cc_copy i u v /\ copy_chain [v] post x ==>
    copy_chain vs (pre ++ i::post) x
Proof
  rpt strip_tac >> simp[copy_chain_append] >>
  qexists_tac `u` >> simp[copy_chain_def] >> metis_tac[]
QED

Theorem flag_fails_mono:
  !bbs as bs i.
    (!v. MEM v as ==> MEM v bs) /\ flag_fails bbs as i ==>
    flag_fails bbs bs i
Proof
  rpt strip_tac >> Cases_on `i.inst_opcode` >> gvs[flag_fails_def]
  >- (Cases_on `i.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `h` >> gvs[] >>
      Cases_on `t'` >> gvs[] >>
      Cases_on `h` >> gvs[] >>
      Cases_on `t` >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem flag_fails_not_invoke:
  !bbs vs i. flag_fails bbs vs i ==> i.inst_opcode <> INVOKE
Proof
  rpt strip_tac >> gvs[flag_fails_def]
QED

Theorem flag_fails_singleton:
  !bbs vs i. flag_fails bbs vs i <=>
    flag_fails bbs [] i \/ ?x. MEM x vs /\ flag_fails bbs [x] i
Proof
  rpt gen_tac >> eq_tac
  >- (Cases_on `i.inst_opcode` >> simp[flag_fails_def]
      >- (Cases_on `i.inst_operands` >> simp[] >>
          Cases_on `h` >> simp[] >>
          Cases_on `t` >> simp[] >>
          Cases_on `h` >> simp[] >>
          Cases_on `t'` >> simp[] >>
          Cases_on `h` >> simp[] >>
          Cases_on `t` >> simp[] >> metis_tac[]) >>
      Cases_on `i.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[] >>
      Cases_on `t` >> simp[] >> metis_tac[]) >>
  metis_tac[flag_fails_mono, MEM]
QED

Theorem unconditional_check_flag_path:
  !pre bbs chk vs post.
    EVERY (\i. i.inst_opcode <> INVOKE) pre /\ flag_fails bbs [] chk ==>
    flag_path bbs vs (pre ++ chk::post)
Proof
  Induct
  >- (rpt strip_tac >> simp[flag_path_def] >>
      metis_tac[flag_fails_mono, flag_fails_not_invoke, MEM]) >>
  rpt strip_tac >> simp[Once flag_path_def] >>
  gvs[EVERY_DEF] >> metis_tac[]
QED

Theorem flag_path_mono:
  !is bbs as bs.
    (!v. MEM v as ==> MEM v bs) /\ flag_path bbs as is ==>
    flag_path bbs bs is
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `flag_path _ _ _` mp_tac >>
  simp[flag_path_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- metis_tac[flag_fails_mono] >>
  simp[] >> disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  Cases_on `write_effects h.inst_opcode = empty_effects` >> simp[] >>
  Cases_on `h.inst_opcode` >> simp[MEM_FILTER] >>
  Cases_on `h.inst_operands` >> simp[MEM_FILTER] >>
  Cases_on `h'` >> simp[MEM_FILTER] >>
  Cases_on `t` >> simp[MEM_FILTER] >>
  Cases_on `MEM s as` >> Cases_on `MEM s bs` >>
  gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem flag_path_check_witness:
  !is bbs vs. flag_path bbs vs is ==> check_witness bbs vs is
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> simp[Once flag_path_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- (simp[check_witness_def] >>
      qexistsl_tac [`[]`, `h`, `is`] >>
      simp[copy_chain_def] >> metis_tac[flag_fails_singleton]) >>
  gvs[] >> qmatch_asmsub_abbrev_tac `flag_path bbs ws is` >>
  first_x_assum drule >>
  qpat_x_assum `flag_path _ _ _` kall_tac >>
  simp[check_witness_def] >> strip_tac >>
  qexistsl_tac [`h::pre`, `chk`, `post`] >> simp[] >>
  Cases_on `flag_fails bbs [] chk` >> simp[] >>
  gvs[] >>
  `write_effects h.inst_opcode = empty_effects` by
    (CCONTR_TAC >> gvs[Abbr `ws`, copy_chain_empty]) >>
  simp[] >> qexists_tac `x` >> simp[] >>
  qpat_x_assum `copy_chain ws pre x` mp_tac >>
  simp[Abbr `ws`] >>
  Cases_on `h.inst_opcode` >> simp[copy_chain_def, cc_copy_def] >>
  (all_tac >>~- ([`copy_chain (FILTER _ _) _ _ ==> _`],
    strip_tac >> irule copy_chain_mono >>
    qexists_tac `FILTER (\x. ~MEM x h.inst_outputs) vs` >>
    simp[MEM_FILTER])) >>
  Cases_on `h.inst_operands` >> simp[]
  >- metis_tac[copy_chain_mono, MEM_FILTER] >>
  rename1 `h.inst_operands = operand::operands` >>
  Cases_on `operand` >> simp[]
  >- metis_tac[copy_chain_mono, MEM_FILTER]
  >- (Cases_on `operands` >> simp[]
      >- (rename1 `MEM u vs` >> Cases_on `MEM u vs` >> simp[copy_chain_union]
          >- metis_tac[copy_chain_roots] >>
          metis_tac[copy_chain_mono, MEM_FILTER]) >>
      metis_tac[copy_chain_mono, MEM_FILTER]) >>
  metis_tac[copy_chain_mono, MEM_FILTER]
QED

Theorem copy_check_flag_path:
  !pre bbs vs x chk post.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre)) /\
    (!v. MEM v vs ==> ~MEM v (FLAT (MAP (\i. i.inst_outputs) pre))) /\
    EVERY (\i. i.inst_opcode <> INVOKE) pre /\
    EVERY (\i. write_effects i.inst_opcode = empty_effects) pre /\
    copy_chain vs pre x /\ flag_fails bbs [x] chk ==>
    flag_path bbs vs (pre ++ chk::post)
Proof
  Induct
  >- (simp[copy_chain_def, flag_path_def] >>
      metis_tac[flag_fails_mono, flag_fails_not_invoke, MEM]) >>
  rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, EVERY_DEF] >>
  qpat_x_assum `copy_chain _ _ _` mp_tac >>
  simp[Once copy_chain_def] >> disch_then DISJ_CASES_TAC
  >- (`flag_path bbs vs (pre ++ chk::post)` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      simp[Once flag_path_def] >> disj2_tac >>
      irule flag_path_mono >> goal_assum (drule_at Any) >>
      Cases_on `h.inst_opcode` >> simp[MEM_FILTER] >>
      Cases_on `h.inst_operands` >> simp[MEM_FILTER] >>
      Cases_on `h'` >> simp[MEM_FILTER] >>
      Cases_on `t` >> simp[MEM_FILTER] >>
      rename1 `MEM u vs` >> Cases_on `MEM u vs` >>
      simp[MEM_FILTER] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> gvs[cc_copy_def] >>
  `flag_path bbs [v] (pre ++ chk::post)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[Once flag_path_def] >> disj2_tac >>
  irule flag_path_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem check_witness_flag_path:
  !bbs vs is.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) is)) /\
    (!v. MEM v vs ==> ~MEM v (FLAT (MAP (\i. i.inst_outputs) is))) /\
    check_witness bbs vs is ==> flag_path bbs vs is
Proof
  rpt gen_tac >> simp[check_witness_def] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  metis_tac[unconditional_check_flag_path, copy_check_flag_path]
QED

Theorem compute_effect_deps_neutral:
  !et i. read_effects i.inst_opcode = empty_effects /\
    write_effects i.inst_opcode = empty_effects ==>
    compute_effect_deps et i = ([], et)
Proof
  rpt strip_tac >>
  simp[compute_effect_deps_def, effects_to_list_def,
       venomEffectsTheory.empty_effects_def, passSharedDefsTheory.nub_first_def]
QED

Theorem compute_effect_deps_domain:
  !et i ds et' domain.
    compute_effect_deps et i = (ds, et') /\ et_wf et domain /\
    ~is_pseudo i.inst_opcode /\
    (MEM i domain \/ (read_effects i.inst_opcode = empty_effects /\
                      write_effects i.inst_opcode = empty_effects)) ==>
    (!d. MEM d ds ==> MEM d domain /\ ~is_pseudo d.inst_opcode) /\
    et_wf et' domain
Proof
  rpt gen_tac >> strip_tac
  >- metis_tac[compute_effect_deps_wf]
  >> drule_all compute_effect_deps_neutral >> strip_tac >> gvs[]
QED

Theorem build_eda_domain_fold:
  !xs domain acc et.
    et_wf et domain /\
    (!id ds d. FLOOKUP acc id = SOME ds /\ MEM d ds ==>
       MEM d domain /\ ~is_pseudo d.inst_opcode) /\
    EVERY (\i. ~is_pseudo i.inst_opcode /\
      (MEM i domain \/ (read_effects i.inst_opcode = empty_effects /\
                        write_effects i.inst_opcode = empty_effects))) xs ==>
    !id ds d.
      FLOOKUP (FST (FOLDL (\(acc, et) i.
        (\(deps, et'). (acc |+ (i.inst_id, deps), et'))
          (compute_effect_deps et i)) (acc, et) xs)) id = SOME ds /\
      MEM d ds ==> MEM d domain /\ ~is_pseudo d.inst_opcode
Proof
  Induct >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rename1 `et_wf et allowed` >>
  qpat_x_assum `EVERY _ (h::xs)` mp_tac >>
  pure_rewrite_tac[EVERY_DEF] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 assume_tac assume_tac) assume_tac) >>
  Cases_on `compute_effect_deps et h` >>
  rename1 `compute_effect_deps et h = (nd, ne)` >>
  `(!d. MEM d nd ==> MEM d allowed /\ ~is_pseudo d.inst_opcode) /\
   et_wf ne allowed` by
    (irule compute_effect_deps_domain >> qexistsl [`et`, `h`] >> simp[]) >>
  first_x_assum (qspecl_then [`allowed`, `acc |+ (h.inst_id, nd)`, `ne`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[])) >>
  simp[]
QED

Theorem build_eda_effectful_deps:
  !bi id ds d. FLOOKUP (build_eda bi) id = SOME ds /\ MEM d ds ==>
    MEM d bi /\
    (read_effects d.inst_opcode <> empty_effects \/
     write_effects d.inst_opcode <> empty_effects)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL
    [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`,
     `FILTER (\i. read_effects i.inst_opcode <> empty_effects \/
                  write_effects i.inst_opcode <> empty_effects) bi`,
     `FEMPTY`, `empty_effect_track`] build_eda_domain_fold) >>
  (impl_tac >- simp[et_wf_def, empty_effect_track_def,
    finite_mapTheory.FLOOKUP_DEF, EVERY_FILTER, EVERY_MEM, MEM_FILTER]) >>
  simp[build_eda_def, MEM_FILTER] >> metis_tac[]
QED

Theorem inst_data_deps_outputs:
  !bi order i d. MEM d (inst_data_deps bi order i) ==>
    d.inst_outputs <> []
Proof
  rpt gen_tac >>
  simp[inst_data_deps_def, passSharedDefsTheory.MEM_nub_first,
       MEM_APPEND, MEM_FILTER, MEM_MAP, optionTheory.IS_SOME_EXISTS] >>
  Cases_on `is_terminator i.inst_opcode` >> simp[] >>
  rpt strip_tac >>
  gvs[MEM_FILTER, MEM_MAP, optionTheory.IS_SOME_EXISTS]
  >- metis_tac[producing_inst_mem_outputs, MEM]
  >> rename1 `operand_producer bi op = SOME producer` >>
  Cases_on `op` >> gvs[operand_producer_def] >>
  metis_tac[producing_inst_mem_outputs, MEM]
QED

Theorem effect_free_output_free_not_dependency:
  !bi a order i d.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM a bi /\
    a.inst_outputs = [] /\
    read_effects a.inst_opcode = empty_effects /\
    write_effects a.inst_opcode = empty_effects /\
    MEM d (inst_all_deps bi order (build_eda bi) i) ==>
    d.inst_id <> a.inst_id
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM d bi` by metis_tac[inst_all_deps_mem, build_eda_wf] >>
  `d = a` by metis_tac[all_distinct_map_mem_inj] >> gvs[] >>
  qpat_x_assum `MEM a (inst_all_deps _ _ _ _)` mp_tac >>
  simp[inst_all_deps_def, passSharedDefsTheory.MEM_nub_first] >>
  Cases_on `FLOOKUP (build_eda bi) i.inst_id` >> simp[] >>
  metis_tac[inst_data_deps_outputs, build_eda_effectful_deps]
QED

Theorem effect_free_output_free_entry:
  !bi a order.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM a bi /\
    a.inst_outputs = [] /\
    read_effects a.inst_opcode = empty_effects /\
    write_effects a.inst_opcode = empty_effects /\
    ~is_pseudo a.inst_opcode ==>
    MEM a (entry_instructions bi order (build_eda bi))
Proof
  rpt strip_tac >>
  simp[entry_instructions_def, MEM_FILTER, MEM_nub, MEM_FLAT, MEM_MAP] >>
  gen_tac >> spose_not_then strip_assume_tac >> gvs[MEM_MAP] >>
  metis_tac[effect_free_output_free_not_dependency]
QED

Theorem assert_entry:
  !bi a order.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM a bi /\
    inst_wf a /\ a.inst_opcode = ASSERT ==>
    MEM a (entry_instructions bi order (build_eda bi))
Proof
  rpt strip_tac >> irule effect_free_output_free_entry >> simp[] >>
  gvs[inst_wf_def, venomEffectsTheory.read_effects_def,
      venomEffectsTheory.write_effects_def, venomInstTheory.is_pseudo_def]
QED

Definition source_prefix_ids_def:
  source_prefix_ids bi left id <=>
    ?j. MEM j bi /\ j.inst_id = id /\
        (is_pseudo j.inst_opcode \/ MEM j left)
End

Theorem source_prefix_ids_not_barrier:
  !left a right.
    ALL_DISTINCT (MAP (\i. i.inst_id) (left ++ a::right)) /\
    ~is_pseudo a.inst_opcode ==>
    ~source_prefix_ids (left ++ a::right) left a.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[source_prefix_ids_def] >> strip_tac >>
  `MEM a (left ++ a::right)` by simp[] >>
  `j = a` by metis_tac[all_distinct_map_mem_inj] >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem source_prefix_entry_split:
  !left a right order.
    ALL_DISTINCT (MAP (\i. i.inst_id) (left ++ a::right)) /\
    inst_wf a /\ a.inst_opcode = ASSERT ==>
    ?es rs.
      entry_instructions (left ++ a::right) order (build_eda (left ++ a::right)) =
        es ++ a::rs /\
      EVERY (\i. source_prefix_ids (left ++ a::right) left i.inst_id) es
Proof
  rpt strip_tac >>
  `MEM a (entry_instructions (left ++ a::right) order
           (build_eda (left ++ a::right)))` by
    (irule assert_entry >> simp[]) >>
  qpat_x_assum `MEM a _` mp_tac >>
  pure_rewrite_tac[entry_instructions_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `FILTER keep (FILTER _ _)` >>
  simp_tac bool_ss [MEM_FILTER] >> strip_tac >>
  pure_rewrite_tac[FILTER_APPEND, FILTER] >> simp[] >>
  qexistsl [`FILTER keep (FILTER (\i. ~is_pseudo i.inst_opcode) left)`,
            `FILTER keep (FILTER (\i. ~is_pseudo i.inst_opcode) right)`] >>
  simp[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  simp[source_prefix_ids_def] >> metis_tac[MEM_APPEND]
QED

Theorem nonterminator_deps_backward:
  !bi order inst dep.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    non_pseudo_defs_before_uses bi /\ MEM inst bi /\
    ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
    MEM dep (inst_all_deps bi order (build_eda bi) inst) ==>
    ?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
          EL i bi = dep /\ EL j bi = inst
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM dep (inst_all_deps _ _ _ _)` mp_tac >>
  simp[inst_all_deps_def, inst_data_deps_def,
       passSharedDefsTheory.MEM_nub_first] >> strip_tac
  >- (gvs[MEM_MAP, MEM_FILTER, optionTheory.IS_SOME_EXISTS] >>
      rename1 `operand_producer bi op = SOME dep` >>
      Cases_on `op` >> gvs[operand_producer_def] >>
      `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
      qpat_x_assum `non_pseudo_defs_before_uses _` mp_tac >>
      rewrite_tac[non_pseudo_defs_before_uses_def, np_defs_before_uses_def] >>
      disch_then (qspecl_then [`j`, `s`, `dep`] mp_tac) >> simp[] >>
      strip_tac >> qexistsl [`i`, `j`] >> simp[]) >>
  Cases_on `FLOOKUP (build_eda bi) inst.inst_id` >> gvs[] >>
  `~is_pseudo dep.inst_opcode` by
    metis_tac[build_eda_wf, eda_wf_def] >>
  metis_tac[eda_deps_backward_plain]
QED
Theorem source_prefix_nonterminating:
  !bb left a right k.
    bb_well_formed bb /\ bb.bb_instructions = left ++ a::right /\
    ~is_terminator a.inst_opcode /\ k <= LENGTH left ==>
    ~is_terminator (EL k bb.bb_instructions).inst_opcode
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by simp[] >>
  `k = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `k = LENGTH left` by (gvs[] >> decide_tac) >>
  gvs[EL_APPEND_EQN]
QED

Theorem source_prefix_index_bound:
  !left a right inst j.
    ALL_DISTINCT (MAP (\i. i.inst_id) (left ++ a::right)) /\
    (MEM inst left \/ inst = a) /\ j < LENGTH (left ++ a::right) /\
    EL j (left ++ a::right) = inst ==>
    j <= LENGTH left
Proof
  rpt gen_tac >> strip_tac
  >- (`?k. k < LENGTH left /\ EL k left = inst` by metis_tac[MEM_EL] >>
      `EL k (left ++ a::right) = inst` by simp[EL_APPEND_EQN] >>
      `k = j` by
        (qspecl_then [`MAP (\i. i.inst_id) (left ++ a::right)`, `k`, `j`]
           mp_tac ALL_DISTINCT_EL_IMP >> simp[EL_MAP] >> fs[]) >> decide_tac) >>
  `EL (LENGTH left) (left ++ a::right) = a` by simp[EL_APPEND_EQN] >>
  `LENGTH left = j` by
    (qspecl_then [`MAP (\i. i.inst_id) (left ++ a::right)`, `LENGTH left`, `j`]
       mp_tac ALL_DISTINCT_EL_IMP >> simp[EL_MAP] >> fs[]) >> simp[]
QED

Theorem source_prefix_dependency_closed:
  !bb bi left a right order inst dep.
    bb_well_formed bb /\ bi = bb.bb_instructions /\
    bi = left ++ a::right /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    non_pseudo_defs_before_uses bi /\ a.inst_opcode = ASSERT /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    (source_prefix_ids bi left inst.inst_id \/ inst = a) /\
    MEM dep (inst_all_deps bi order (build_eda bi) inst) ==>
    source_prefix_ids bi left dep.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst left \/ inst = a` by
    (Cases_on `inst = a` >> fs[] >>
     qpat_x_assum `source_prefix_ids _ _ _` mp_tac >>
     pure_rewrite_tac[source_prefix_ids_def] >> strip_tac >>
     `j = inst` by metis_tac[all_distinct_map_mem_inj] >> gvs[]) >>
  `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
  `j <= LENGTH left` by metis_tac[source_prefix_index_bound] >>
  `~is_terminator a.inst_opcode` by simp[venomInstTheory.is_terminator_def] >>
  `bb.bb_instructions = left ++ a::right` by metis_tac[] >>
  `~is_terminator inst.inst_opcode` by
    (drule_all source_prefix_nonterminating >> gvs[]) >>
  drule_all nonterminator_deps_backward >> strip_tac >>
  rename1 `EL p bi = dep` >> rename1 `EL q bi = inst` >>
  `q <= LENGTH left` by metis_tac[source_prefix_index_bound] >>
  `p < LENGTH left` by decide_tac >>
  `MEM dep left` by
    (`EL p left = dep` by (gvs[] >> fs[EL_APPEND_EQN]) >> metis_tac[MEM_EL]) >>
  simp[source_prefix_ids_def] >>
  qexists_tac `dep` >> simp[] >> metis_tac[MEM_EL]
QED


Definition work_ok_def:
  (work_ok P (DfsProcess i) <=> P i.inst_id) /\
  (work_ok P (DfsEmit i) <=> P i.inst_id)
End

Definition work_source_def:
  (work_source bi (DfsProcess i) <=> MEM i bi) /\
  (work_source bi (DfsEmit i) <=> T)
End

Definition barrier_process_def:
  barrier_process bi P a s <=>
    EVERY (\i. P i.inst_id) s.ds_output /\
    ~MEM a.inst_id s.ds_visited /\
    EVERY (work_source bi) s.ds_stack /\
    ?w r. s.ds_stack = w ++ DfsProcess a::r /\ EVERY (work_ok P) w
End

Definition barrier_emit_def:
  barrier_emit bi P a s <=>
    EVERY (\i. P i.inst_id) s.ds_output /\
    EVERY (work_source bi) s.ds_stack /\
    ?w r. s.ds_stack = w ++ DfsEmit a::r /\ EVERY (work_ok P) w
End

Definition barrier_done_def:
  barrier_done P a s <=>
    ?pre post. s.ds_output = pre ++ a::post /\
               EVERY (\i. P i.inst_id) pre
End

Definition barrier_inv_def:
  barrier_inv bi P a s <=>
    barrier_process bi P a s \/ barrier_emit bi P a s \/ barrier_done P a s
End

Theorem barrier_done_step:
  !P a s bi order eda offspring do_flip.
    barrier_done P a s ==>
    barrier_done P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt gen_tac >> simp[barrier_done_def] >> strip_tac >>
  Cases_on `s.ds_stack`
  >- (simp[dfs_step_def] >> metis_tac[]) >>
  Cases_on `h` >> simp[dfs_step_def]
  >- (rpt IF_CASES_TAC >> simp[] >> metis_tac[]) >>
  qexistsl [`pre`, `post ++ [i]`] >> simp[APPEND_ASSOC]
QED

Theorem barrier_children:
  !bi order eda offspring P a inst.
    eda_wf eda bi /\ MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    (P inst.inst_id \/ inst = a) /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) ==>
    EVERY (work_ok P)
      (MAP DfsProcess (sort_children bi order eda offspring inst
        (inst_all_deps bi order eda inst))) /\
    EVERY (work_source bi)
      (MAP DfsProcess (sort_children bi order eda offspring inst
        (inst_all_deps bi order eda inst)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[EVERY_MAP, EVERY_MEM, work_ok_def, work_source_def, sort_children_mem] >>
  metis_tac[inst_all_deps_mem]
QED

Theorem barrier_emit_head:
  !bi order eda offspring do_flip P a s rest.
    s.ds_stack = DfsEmit a::rest /\
    EVERY (\i. P i.inst_id) s.ds_output ==>
    barrier_done P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt strip_tac >> simp[barrier_done_def, dfs_step_def] >>
  qexistsl [`s.ds_output`, `[]`] >> simp[]
QED

Theorem barrier_process_head:
  !bi order eda offspring do_flip P a s rest.
    eda_wf eda bi /\ MEM a bi /\
    ~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode /\
    s.ds_stack = DfsProcess a::rest /\
    EVERY (\i. P i.inst_id) s.ds_output /\
    ~MEM a.inst_id s.ds_visited /\ EVERY (work_source bi) s.ds_stack /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) ==>
    barrier_emit bi P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (work_ok P)
      (MAP DfsProcess (sort_children bi order eda offspring a
        (inst_all_deps bi order eda a))) /\
   EVERY (work_source bi)
      (MAP DfsProcess (sort_children bi order eda offspring a
        (inst_all_deps bi order eda a)))` by
     (irule barrier_children >> simp[] >> qexists_tac `a` >> simp[] >>
      first_assum ACCEPT_TAC) >>
  simp[barrier_emit_def, dfs_step_def, EVERY_APPEND, work_source_def] >>
  conj_tac >- gvs[work_source_def] >>
  qexistsl [`MAP DfsProcess (sort_children bi order eda offspring a
               (inst_all_deps bi order eda a))`, `rest`] >> simp[]
QED

Theorem barrier_prefix_step:
  !bi order eda offspring do_flip P a s h w tail.
    eda_wf eda bi /\ ~P a.inst_id /\
    s.ds_stack = h::(w ++ tail) /\ work_ok P h /\
    EVERY (work_ok P) w /\ EVERY (work_source bi) s.ds_stack /\
    EVERY (\i. P i.inst_id) s.ds_output /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) ==>
    let s' = dfs_step bi order eda offspring do_flip s in
      EVERY (\i. P i.inst_id) s'.ds_output /\
      EVERY (work_source bi) s'.ds_stack /\
      (~MEM a.inst_id s.ds_visited ==> ~MEM a.inst_id s'.ds_visited) /\
      ?w'. s'.ds_stack = w' ++ tail /\ EVERY (work_ok P) w'
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `h` >> gvs[work_ok_def, work_source_def]
  >- (Cases_on `MEM i.inst_id s.ds_visited`
      >- (simp[dfs_step_def] >> metis_tac[]) >>
      Cases_on `is_pseudo i.inst_opcode`
      >- (simp[dfs_step_def] >> metis_tac[]) >>
      `EVERY (work_ok P)
        (MAP DfsProcess (sort_children bi order eda offspring i
          (inst_all_deps bi order eda i))) /\
       EVERY (work_source bi)
        (MAP DfsProcess (sort_children bi order eda offspring i
          (inst_all_deps bi order eda i)))` by
        (irule barrier_children >> simp[] >> qexists_tac `a` >> simp[] >>
         first_assum ACCEPT_TAC) >>
      `a.inst_id <> i.inst_id` by metis_tac[] >>
      simp[dfs_step_def] >> IF_CASES_TAC >>
      simp[EVERY_APPEND, work_source_def, work_ok_def,
           flip_operands_inst_id] >>
      qexists_tac `MAP DfsProcess (sort_children bi order eda offspring i
        (inst_all_deps bi order eda i)) ++ DfsEmit
        (if do_flip /\ is_flippable i.inst_opcode /\
            sort_children bi order eda offspring i
              (inst_all_deps bi order eda i) <> inst_all_deps bi order eda i
         then flip_operands i else i)::w` >>
      simp[EVERY_APPEND, work_ok_def, flip_operands_inst_id, APPEND_ASSOC]) >>
  simp[dfs_step_def, EVERY_APPEND] >> metis_tac[]
QED

Theorem barrier_process_step:
  !bi order eda offspring do_flip P a s.
    eda_wf eda bi /\ MEM a bi /\ ~P a.inst_id /\
    ~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) /\ barrier_process bi P a s ==>
    barrier_inv bi P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `barrier_process _ _ _ _` mp_tac >>
  simp[barrier_process_def] >> strip_tac >> Cases_on `w` >> gvs[]
  >- (irule (iffRL barrier_inv_def) >> disj2_tac >> disj1_tac >>
      irule barrier_process_head >> simp[] >> first_assum ACCEPT_TAC) >>
  `EVERY (work_source bi) s.ds_stack` by simp[EVERY_APPEND] >>
  qpat_x_assum `s.ds_stack = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> disch_tac >>
  drule_all barrier_prefix_step >> simp[] >> strip_tac >>
  simp[barrier_inv_def] >> disj1_tac >>
  simp[barrier_process_def] >> metis_tac[]
QED

Theorem barrier_emit_step:
  !bi order eda offspring do_flip P a s.
    eda_wf eda bi /\ ~P a.inst_id /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) /\ barrier_emit bi P a s ==>
    barrier_inv bi P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `barrier_emit _ _ _ _` mp_tac >>
  simp[barrier_emit_def] >> strip_tac >> Cases_on `w` >> gvs[]
  >- (simp[barrier_inv_def] >> disj2_tac >> disj2_tac >>
      irule barrier_emit_head >> simp[]) >>
  `EVERY (work_source bi) s.ds_stack` by simp[EVERY_APPEND] >>
  qpat_x_assum `s.ds_stack = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> disch_tac >>
  drule_all barrier_prefix_step >> simp[] >> strip_tac >>
  simp[barrier_inv_def] >> disj2_tac >> disj1_tac >>
  simp[barrier_emit_def] >> metis_tac[]
QED

Theorem barrier_inv_step:
  !bi order eda offspring do_flip P a s.
    eda_wf eda bi /\ MEM a bi /\ ~P a.inst_id /\
    ~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) /\ barrier_inv bi P a s ==>
    barrier_inv bi P a (dfs_step bi order eda offspring do_flip s)
Proof
  rpt gen_tac >> simp[barrier_inv_def] >>
  metis_tac[barrier_process_step, barrier_emit_step,
            barrier_done_step, barrier_inv_def]
QED

Theorem barrier_inv_run:
  !n bi order eda offspring do_flip P a s.
    eda_wf eda bi /\ MEM a bi /\ ~P a.inst_id /\
    ~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) /\ barrier_inv bi P a s ==>
    barrier_inv bi P a
      (FUNPOW (dfs_step bi order eda offspring do_flip) n s)
Proof
  Induct >> simp[arithmeticTheory.FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule barrier_inv_step >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem schedule_barrier_split:
  !bi order eda offspring P a entries es rs out.
    eda_wf eda bi /\ MEM a bi /\ ~P a.inst_id /\
    ~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode /\
    EVERY (\i. MEM i bi) entries /\ entries = es ++ a::rs /\
    EVERY (\i. P i.inst_id) es /\
    (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
       (P i.inst_id \/ i = a) /\ MEM d (inst_all_deps bi order eda i) ==>
       P d.inst_id) /\
    out = schedule_from_entries bi order eda offspring entries /\ MEM a out ==>
    ?pre post. out = pre ++ a::post /\ EVERY (\i. P i.inst_id) pre
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `init = <|ds_stack := MAP DfsProcess entries;
                       ds_output := []; ds_visited := []|>` >>
  `barrier_inv bi P a init` by
    (simp[barrier_inv_def] >> disj1_tac >>
     simp[barrier_process_def, Abbr `init`, EVERY_MAP, work_source_def] >>
     conj_tac >- gvs[EVERY_APPEND] >>
     qexistsl [`MAP DfsProcess es`, `MAP DfsProcess rs`] >>
     simp[MAP_APPEND, EVERY_MAP, work_ok_def]) >>
  `barrier_inv bi P a
     (FUNPOW (dfs_step bi order eda offspring T)
       ((LENGTH bi + 1) * (LENGTH bi + 1)) init)` by
    (irule barrier_inv_run >> simp[] >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_abbrev_tac `barrier_inv bi P a final` >>
  `out = final.ds_output` by
    simp[Abbr `final`, Abbr `init`, schedule_from_entries_def] >>
  qpat_x_assum `barrier_inv _ _ _ final` mp_tac >>
  simp[barrier_inv_def, barrier_process_def, barrier_emit_def,
       barrier_done_def] >>
  `~EVERY (\i. P i.inst_id) final.ds_output` by
    (simp[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem assert_schedule_barrier:
  !bb bi left a right order sched.
    bb_well_formed bb /\ bi = bb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    non_pseudo_defs_before_uses bi /\ bi = left ++ a::right /\
    inst_wf a /\ a.inst_opcode = ASSERT /\
    sched = schedule_from_entries bi order (build_eda bi)
      (build_offspring_map bi order) (entry_instructions bi order (build_eda bi)) /\
    MEM a sched ==>
    ?pre post. sched = pre ++ a::post /\
      EVERY (\i. source_prefix_ids bi left i.inst_id) pre
Proof
  rpt gen_tac >> strip_tac >>
  `~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode` by
    simp[venomInstTheory.is_pseudo_def, is_flippable_def,
         venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def] >>
  `~source_prefix_ids bi left a.inst_id` by
    metis_tac[source_prefix_ids_not_barrier] >>
  `?es rs. entry_instructions bi order (build_eda bi) = es ++ a::rs /\
     EVERY (\i. source_prefix_ids bi left i.inst_id) es` by
    metis_tac[source_prefix_entry_split] >>
  drule_at (Pat `out = schedule_from_entries _ _ _ _ _`) schedule_barrier_split >>
  disch_then irule >> simp[build_eda_wf, entry_instructions_mem] >>
  reverse conj_tac >- (qexistsl [`es`, `rs`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule source_prefix_dependency_closed >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem from_block_source_prefix:
  !bi left x.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ from_block bi x /\
    source_prefix_ids bi left x.inst_id /\ ~is_pseudo x.inst_opcode ==>
    ?y. MEM y left /\ y.inst_id = x.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  gvs[source_prefix_ids_def, from_block_def] >>
  `j = j'` by metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
  gvs[flip_operands_is_pseudo] >> metis_tac[flip_operands_inst_id]
QED

Theorem dft_block_assert_barrier:
  !bb left a right order.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ a::right /\
    inst_wf a /\ a.inst_opcode = ASSERT ==>
    ?pre post. (dft_block order bb).bb_instructions = pre ++ a::post /\
      (!x. MEM x pre /\ ~is_pseudo x.inst_opcode ==>
        ?y. MEM y left /\ y.inst_id = x.inst_id)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `sched = schedule_from_entries bi order (build_eda bi)
    (build_offspring_map bi order) (entry_instructions bi order (build_eda bi))` >>
  `~is_pseudo a.inst_opcode /\ ~is_flippable a.inst_opcode` by
    simp[venomInstTheory.is_pseudo_def, is_flippable_def,
         venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def] >>
  `MEM a (dft_block order bb).bb_instructions` by
    (irule dft_block_nonflippable_mem >> simp[] >> gvs[]) >>
  `(dft_block order bb).bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bi ++ sched` by
    simp[dft_block_def, Abbr `sched`, Abbr `bi`] >>
  `MEM a sched` by gvs[MEM_APPEND, MEM_FILTER] >>
  `?pre post. sched = pre ++ a::post /\
     EVERY (\i. source_prefix_ids bi left i.inst_id) pre` by
    (irule assert_schedule_barrier >> metis_tac[]) >>
  qexistsl [`FILTER (\i. is_pseudo i.inst_opcode) bi ++ pre`, `post`] >>
  simp[APPEND_ASSOC] >> rpt gen_tac >> strip_tac
  >- gvs[MEM_FILTER] >>
  `from_block bb.bb_instructions x` by
    (irule dft_block_from_orig >> simp[MEM_FILTER] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `from_block bi x` by metis_tac[] >>
  `source_prefix_ids bi left x.inst_id` by
    (qpat_x_assum `EVERY _ pre` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[from_block_source_prefix]
QED

Theorem distinct_marker_prefix:
  !pre a post pre' post'.
    ALL_DISTINCT (pre ++ a::post) /\
    pre ++ a::post = pre' ++ a::post' ==> pre = pre'
Proof
  Induct >> Cases_on `pre'` >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem dft_block_assert_prefix:
  !bb left a right order pre post x.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ a::right /\
    inst_wf a /\ a.inst_opcode = ASSERT /\
    (dft_block order bb).bb_instructions = pre ++ a::post /\
    MEM x pre /\ ~is_pseudo x.inst_opcode ==>
    ?y. MEM y left /\ y.inst_id = x.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `?good rest. (dft_block order bb).bb_instructions = good ++ a::rest /\
    (!x. MEM x good /\ ~is_pseudo x.inst_opcode ==>
      ?y. MEM y left /\ y.inst_id = x.inst_id)` by
    (irule dft_block_assert_barrier >> metis_tac[]) >>
  `~is_pseudo a.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (irule all_distinct_map_filter >> simp[]) >>
  `PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode)
     (dft_block order bb).bb_instructions))
    (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode)
     bb.bb_instructions))` by
    (irule dft_block_perm_ids >> simp[]) >>
  `ALL_DISTINCT (FILTER (\i. ~is_pseudo i.inst_opcode)
     (dft_block order bb).bb_instructions)` by
    (irule (INST_TYPE [beta |-> ``:num``] ALL_DISTINCT_MAP) >>
     qexists_tac `\i. i.inst_id` >>
     metis_tac[ALL_DISTINCT_PERM, PERM_SYM]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) pre =
   FILTER (\i. ~is_pseudo i.inst_opcode) good` by
    (irule distinct_marker_prefix >> qexistsl [`a`,
       `FILTER (\i. ~is_pseudo i.inst_opcode) post`,
       `FILTER (\i. ~is_pseudo i.inst_opcode) rest`] >>
     `pre ++ a::post = good ++ a::rest` by metis_tac[] >>
     pop_assum (mp_tac o AP_TERM ``FILTER (\i. ~is_pseudo i.inst_opcode)``) >>
     simp[FILTER_APPEND] >> strip_tac >>
     qpat_x_assum `ALL_DISTINCT (FILTER _ _)` mp_tac >>
     asm_rewrite_tac[FILTER_APPEND, FILTER] >>
     qpat_x_assum `_ ++ [a] ++ _ = _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  `MEM x good` by
    (qpat_x_assum `FILTER _ pre = _` (mp_tac o AP_TERM ``MEM (x:instruction)``) >>
     simp[MEM_FILTER]) >> metis_tac[]
QED

Theorem flag_path_environment:
  !is src dst vs.
    (!ws i. flag_fails src ws i ==> flag_fails dst ws i) /\
    flag_path src vs is ==> flag_path dst vs is
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> simp[Once flag_path_def] >> strip_tac >>
  simp[Once flag_path_def] >> metis_tac[]
QED

Theorem calls_flagged_environment:
  !is src dst.
    (!ws i. flag_fails src ws i ==> flag_fails dst ws i) /\
    calls_flagged src is ==> calls_flagged dst is
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt gen_tac >> simp[calls_flagged_def] >> strip_tac >>
  conj_tac
  >- (strip_tac >> Cases_on `h.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[] >> metis_tac[flag_path_environment]) >>
  metis_tac[]
QED

Theorem output_producer_before_filter_position:
  !bi dst P k v p.
    output_producer_before bi (FILTER P dst) /\
    k < LENGTH dst /\ P (EL k dst) /\
    MEM (Var v) (EL k dst).inst_operands /\
    producing_inst bi v = SOME p /\ ~is_pseudo p.inst_opcode ==>
    ?m. m < k /\ P (EL m dst) /\ (EL m dst).inst_id = p.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `pre = FILTER P (TAKE k dst)` >>
  qabbrev_tac `post = FILTER P (DROP (SUC k) dst)` >>
  `FILTER P dst = pre ++ EL k dst::post` by
    (qspec_then `k` (qspec_then `dst` mp_tac) TAKE_DROP_SUC >>
     simp[] >> disch_then (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
     simp[FILTER_APPEND, Abbr `pre`, Abbr `post`]) >>
  `?j. j < LENGTH pre /\ (EL j pre).inst_id = p.inst_id` by
    (qpat_x_assum `output_producer_before _ _` mp_tac >>
     simp[output_producer_before_def] >> strip_tac >>
     first_x_assum (qspecl_then [`LENGTH pre`, `v`, `p`] mp_tac) >>
     simp[EL_APPEND1, EL_APPEND2] >> strip_tac >>
     qexists_tac `m` >> gvs[EL_APPEND1]) >>
  `MEM (EL j pre) (TAKE k dst) /\ P (EL j pre)` by
    (metis_tac[MEM_EL, MEM_FILTER]) >>
  qpat_x_assum `MEM _ (TAKE _ _)` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  qexists_tac `n` >> gvs[EL_TAKE, Abbr `pre`]
QED

Theorem producing_inst_distinct_outputs:
  !is p v.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) is)) /\
    MEM p is /\ MEM v p.inst_outputs ==>
    producing_inst is v = SOME p
Proof
  Induct >> simp[producing_inst_def] >> rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  `~MEM v h.inst_outputs` by metis_tac[MEM_FLAT, MEM_MAP] >>
  simp[] >> first_x_assum irule >> simp[]
QED

Theorem dft_block_producer_position:
  !bb order p v k.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    MEM p bb.bb_instructions /\ ~is_pseudo p.inst_opcode /\
    MEM v p.inst_outputs /\
    k < LENGTH (dft_block order bb).bb_instructions /\
    ~is_pseudo (EL k (dft_block order bb).bb_instructions).inst_opcode /\
    MEM (Var v) (EL k (dft_block order bb).bb_instructions).inst_operands ==>
    ?m. m < k /\
      ~is_pseudo (EL m (dft_block order bb).bb_instructions).inst_opcode /\
      (EL m (dft_block order bb).bb_instructions).inst_id = p.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `producing_inst bb.bb_instructions v = SOME p` by
    (irule producing_inst_distinct_outputs >> simp[]) >>
  drule_all dft_block_schedule_order >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  drule output_producer_before_filter_position >>
  disch_then (qspecl_then [`k`, `v`, `p`] mp_tac) >> simp[]
QED

Theorem dft_block_producer_position_identity:
  !bb order p v k.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    MEM p bb.bb_instructions /\ ~is_pseudo p.inst_opcode /\
    ~is_flippable p.inst_opcode /\ MEM v p.inst_outputs /\
    k < LENGTH (dft_block order bb).bb_instructions /\
    ~is_pseudo (EL k (dft_block order bb).bb_instructions).inst_opcode /\
    MEM (Var v) (EL k (dft_block order bb).bb_instructions).inst_operands ==>
    ?m. m < k /\ EL m (dft_block order bb).bb_instructions = p
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_block_producer_position >> strip_tac >>
  qexists_tac `m` >> simp[] >>
  irule from_block_nonflippable_identity >> simp[] >>
  qexists_tac `bb.bb_instructions` >> simp[] >>
  irule dft_block_from_orig >> simp[MEM_FILTER] >>
  qexists_tac `order` >> simp[] >>
  irule EL_MEM >> decide_tac
QED

Theorem dft_block_outputs_perm:
  !bb order.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    PERM (MAP (\i. i.inst_outputs) bb.bb_instructions)
      (MAP (\i. i.inst_outputs) (dft_block order bb).bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `PERM
    (MAP (\i. i.inst_outputs) (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
    (MAP (\i. i.inst_outputs) (FILTER (\i. ~is_pseudo i.inst_opcode)
       (dft_block order bb).bb_instructions))` by
    (irule dftHelpersTheory.PERM_TRANSFER_inst_id_inst_outputs >>
     simp[all_distinct_map_filter] >> reverse conj_tac
     >- metis_tac[dft_block_perm_ids, PERM_SYM] >>
     rpt gen_tac >> strip_tac >>
     irule from_block_same_inst_id_outputs_filtered_local >> simp[] >>
     qexists_tac `bb.bb_instructions` >>
     gvs[MEM_FILTER, all_distinct_map_filter] >>
     conj_tac
     >- (simp[from_block_def] >> metis_tac[]) >>
     irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]) >>
  `PERM bb.bb_instructions
    (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
     FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    metis_tac[PERM_SPLIT] >>
  `PERM (dft_block order bb).bb_instructions
    (FILTER (\i. is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions ++
     FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)` by
    metis_tac[PERM_SPLIT] >>
  drule (Q.ISPEC `\i:instruction. i.inst_outputs` PERM_MAP) >>
  strip_tac >>
  qpat_x_assum `PERM bb.bb_instructions _`
    (mp_tac o MATCH_MP (Q.ISPEC `\i:instruction. i.inst_outputs` PERM_MAP)) >>
  simp[MAP_APPEND, dft_block_phis] >>
  strip_tac >> fs[MAP_APPEND, dft_block_phis] >>
  `PERM
    (MAP (\i. i.inst_outputs) (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ++
     MAP (\i. i.inst_outputs) (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
    (MAP (\i. i.inst_outputs) (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ++
     MAP (\i. i.inst_outputs) (FILTER (\i. ~is_pseudo i.inst_opcode)
       (dft_block order bb).bb_instructions))` by
    (irule PERM_CONG >> simp[]) >>
  metis_tac[PERM_TRANS, PERM_SYM]
QED

Theorem dft_block_outputs_distinct:
  !bb order.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (dft_block order bb).bb_instructions))
Proof
  rpt strip_tac >> drule_all dft_block_outputs_perm >>
  disch_then (qspec_then `order` mp_tac) >>
  metis_tac[PERM_FLAT, ALL_DISTINCT_PERM]
QED

Theorem copy_chain_root:
  !is vs x. MEM x vs ==> copy_chain vs is x
Proof
  Induct >> simp[copy_chain_def]
QED

Theorem copy_chain_snoc:
  !pre vs i x. copy_chain vs (pre ++ [i]) x <=>
    copy_chain vs pre x \/ ?u. copy_chain vs pre u /\ cc_copy i u x
Proof
  rpt gen_tac >> simp[copy_chain_append, copy_chain_def] >> metis_tac[]
QED

Theorem copy_chain_last:
  !is vs x. copy_chain vs is x <=>
    MEM x vs \/ ?pre i post u.
      is = pre ++ i::post /\ copy_chain vs pre u /\ cc_copy i u x
Proof
  Induct_on `is` using SNOC_INDUCT
  >- simp[copy_chain_def] >>
  rpt gen_tac >> rewrite_tac[SNOC_APPEND, copy_chain_snoc] >>
  eq_tac
  >- (strip_tac
      >- (first_x_assum (drule o iffLR) >> strip_tac
          >- simp[] >>
          disj2_tac >> qexistsl [`pre`, `i`, `post ++ [x]`, `u`] >>
          simp[APPEND_ASSOC]) >>
      disj2_tac >> qexistsl [`is`, `x`, `[]`, `u`] >> simp[]) >>
  strip_tac
  >- (disj1_tac >> metis_tac[copy_chain_root]) >>
  rewrite_tac[GSYM copy_chain_snoc] >>
  qpat_x_assum `_ ++ [_] = _` SUBST1_TAC >>
  irule copy_chain_insert >> goal_assum (drule_at Any) >>
  simp[copy_chain_root]
QED

Theorem copy_chain_bounded_transport:
  !k dst a r v src x C.
    ALL_DISTINCT dst /\ a < LENGTH dst /\ k < LENGTH dst /\
    EL a dst = r /\ MEM v r.inst_outputs /\
    MEM (Var x) (EL k dst).inst_operands /\ copy_chain [v] src x /\
    C (EL k dst) /\
    (!i u z. MEM i src /\ cc_copy i u z ==> C i) /\
    (!p w t.
      (p = r \/ ?u z. MEM p src /\ cc_copy p u z) /\
      MEM w p.inst_outputs /\ t < LENGTH dst /\ C (EL t dst) /\
      MEM (Var w) (EL t dst).inst_operands ==>
      ?s. s < t /\ EL s dst = p) ==>
    a < k /\ copy_chain [v] (TAKE (k-a-1) (DROP (a+1) dst)) x
Proof
  completeInduct_on `k` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `copy_chain _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [copy_chain_last]) >>
  simp_tac bool_ss [MEM] >> strip_tac
  >- (`?s. s < k /\ EL s dst = r` by metis_tac[] >>
      `s = a` by metis_tac[ALL_DISTINCT_EL_IMP, arithmeticTheory.LESS_TRANS] >>
      conj_tac >- decide_tac >> irule copy_chain_root >> simp[]) >>
  `MEM i src` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x i.inst_outputs` by
    (qpat_x_assum `cc_copy _ _ _` mp_tac >> simp[cc_copy_def]) >>
  `?t. t < k /\ EL t dst = i` by metis_tac[] >>
  `t < LENGTH dst` by decide_tac >>
  `MEM (Var u) (EL t dst).inst_operands` by
    (qpat_x_assum `cc_copy _ _ _` mp_tac >> simp[cc_copy_def]) >>
  `a < t /\ copy_chain [v] (TAKE (t-a-1) (DROP (a+1) dst)) u` by
    (first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
     disch_then irule >> simp[] >> qexistsl [`C`, `pre`] >> simp[] >>
     metis_tac[MEM_APPEND, MEM]) >>
  conj_tac >- decide_tac >>
  qpat_x_assum `!m. m < k ==> _` kall_tac >>
  qpat_x_assum `!p w t. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `copy_chain [v] window x` >>
  `t-a-1 < LENGTH window` by simp[Abbr `window`] >>
  `TAKE (t-a-1) window = TAKE (t-a-1) (DROP (a+1) dst)` by
    simp[Abbr `window`, TAKE_TAKE, arithmeticTheory.MIN_DEF] >>
  `EL (t-a-1) window = i` by
    (`t-a-1 + (a+1) = t` by decide_tac >>
     simp[Abbr `window`, EL_TAKE, EL_DROP]) >>
  qspec_then `t-a-1` (qspec_then `window` mp_tac) TAKE_DROP_SUC >>
  simp[] >> disch_then (fn th => once_rewrite_tac[GSYM th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule copy_chain_insert >> qexistsl [`u`, `x`] >>
  simp[copy_chain_root] >>
  qpat_x_assum `copy_chain _ (TAKE _ (DROP _ _)) _` mp_tac >> simp[]
QED

Theorem dft_block_copy_chain:
  !bb order r q v src x.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    MEM r bb.bb_instructions /\ ~is_pseudo r.inst_opcode /\
    ~is_flippable r.inst_opcode /\ MEM v r.inst_outputs /\
    MEM q bb.bb_instructions /\ ~is_pseudo q.inst_opcode /\
    ~is_flippable q.inst_opcode /\ MEM (Var x) q.inst_operands /\
    EVERY (\i. MEM i bb.bb_instructions) src /\ copy_chain [v] src x ==>
    ?left mid right.
      (dft_block order bb).bb_instructions = left ++ r::mid ++ q::right /\
      copy_chain [v] mid x
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `dst = _` >>
  `MEM r dst /\ MEM q dst` by
    (simp[Abbr `dst`] >> metis_tac[dft_block_nonflippable_mem]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) dst)` by
    metis_tac[dft_block_well_formed_gen] >>
  `ALL_DISTINCT dst` by
    (irule (INST_TYPE [beta |-> ``:num``] ALL_DISTINCT_MAP) >>
     qexists_tac `\i. i.inst_id` >> simp[]) >>
  qpat_x_assum `MEM r dst` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `a < LENGTH dst` >>
  qpat_x_assum `MEM q dst` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `k < LENGTH dst` >>
  qpat_x_assum `r = EL a dst` (assume_tac o SYM) >>
  qpat_x_assum `q = EL k dst` (assume_tac o SYM) >>
  `a < k /\ copy_chain [v] (TAKE (k-a-1) (DROP (a+1) dst)) x` by
    (irule copy_chain_bounded_transport >> simp[] >>
     qexistsl [`\i. ~is_pseudo i.inst_opcode`, `src`] >> simp[] >>
     conj_tac >- simp[cc_copy_def, venomInstTheory.is_pseudo_def] >>
     rpt gen_tac >> strip_tac >>
     `MEM p bb.bb_instructions /\ ~is_pseudo p.inst_opcode /\
      ~is_flippable p.inst_opcode` by
       (gvs[cc_copy_def, EVERY_MEM] >>
        simp[venomInstTheory.is_pseudo_def, is_flippable_def,
             venomEffectsTheory.is_commutative_def,
             passSharedDefsTheory.is_comparator_def] >> metis_tac[]) >>
     simp[Abbr `dst`] >>
     irule dft_block_producer_position_identity >> simp[] >>
     qexists_tac `w` >> gvs[]) >>
  qexistsl [`TAKE a dst`, `TAKE (k-a-1) (DROP (a+1) dst)`,
            `DROP (k+1) dst`] >> simp[] >>
  `k-a-1 < LENGTH (DROP (a+1) dst)` by simp[] >>
  `k-a-1 + (a+1) = k` by decide_tac >>
  `SUC (k-a-1) + (a+1) = k+1` by decide_tac >>
  qspec_then `k-a-1` (qspec_then `DROP (a+1) dst` mp_tac) TAKE_DROP_SUC >>
  simp[EL_DROP, DROP_DROP] >> strip_tac >>
  qspec_then `a` (qspec_then `dst` mp_tac) TAKE_DROP_SUC >>
  simp[arithmeticTheory.ADD1] >> metis_tac[APPEND_ASSOC]
QED

Theorem dft_block_writer_prefix:
  !bb order left call right pre post w.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::right /\
    (dft_block order bb).bb_instructions = pre ++ call::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    MEM w left /\ ~is_pseudo w.inst_opcode /\
    write_effects w.inst_opcode <> {} ==>
    ?y. MEM y pre /\ y.inst_id = w.inst_id
Proof
  rpt gen_tac >> strip_tac >>
  `~is_pseudo call.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  qpat_x_assum `MEM w left` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `a < LENGTH left` >>
  qpat_x_assum `w = EL a left` (assume_tac o SYM) >>
  qabbrev_tac `out = FILTER (\i. ~is_pseudo i.inst_opcode)
    (dft_block order bb).bb_instructions` >>
  `out = FILTER (\i. ~is_pseudo i.inst_opcode) pre ++ call::
         FILTER (\i. ~is_pseudo i.inst_opcode) post` by
    simp[Abbr `out`, FILTER_APPEND] >>
  `?m. m < LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) pre) /\
       (EL m out).inst_id = (EL a bb.bb_instructions).inst_id` by
    (irule dft_block_writer_before_call >>
     simp[Abbr `out`, EL_APPEND1, EL_APPEND2] >>
     conj_tac
     >- (qexistsl [`bb`, `order`] >> simp[]) >>
     qexists_tac `LENGTH left` >> simp[EL_APPEND1, EL_APPEND2]) >>
  qexists_tac `EL m out` >> simp[] >>
  `MEM (EL m out) (FILTER (\i. ~is_pseudo i.inst_opcode) pre)` by
    (gvs[EL_APPEND1] >> irule EL_MEM >> simp[]) >>
  gvs[MEM_FILTER, EL_APPEND1, APPEND_ASSOC]
QED

Theorem dft_block_interval_safe:
  !bb order left call mid chk right pre mid' post bad.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::mid ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ call::mid' ++ chk::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    EVERY (\i. ~bad i) mid /\
    (!i. bad (flip_operands i) = bad i) /\
    (!i. bad i ==> ~is_pseudo i.inst_opcode /\ write_effects i.inst_opcode <> {}) /\
    (!x. MEM x (pre ++ call::mid') /\ ~is_pseudo x.inst_opcode ==>
      ?y. MEM y (left ++ call::mid) /\ y.inst_id = x.inst_id) ==>
    EVERY (\i. ~bad i) mid'
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)` by
    metis_tac[dft_block_well_formed_gen] >>
  `ALL_DISTINCT (dft_block order bb).bb_instructions` by
    (irule (INST_TYPE [beta |-> ``:num``] ALL_DISTINCT_MAP) >>
     qexists_tac `\i. i.inst_id` >> simp[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM x mid'` >>
  `~is_pseudo x.inst_opcode` by metis_tac[] >>
  `from_block bb.bb_instructions x` by
    (irule dft_block_from_orig >> qexists_tac `order` >>
     simp[MEM_FILTER] >> metis_tac[MEM_APPEND, MEM]) >>
  `?y. MEM y (left ++ call::mid) /\ y.inst_id = x.inst_id` by
    metis_tac[MEM_APPEND, MEM] >>
  `MEM y bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
  `bad y` by
    (qpat_x_assum `from_block _ _` mp_tac >>
     pure_rewrite_tac[from_block_def] >> strip_tac >>
     `j.inst_id = y.inst_id` by metis_tac[flip_operands_inst_id] >>
     `j = y` by
       (irule (INST_TYPE [beta |-> ``:num``] all_distinct_map_mem_inj) >>
        qexistsl [`\i. i.inst_id`, `bb.bb_instructions`] >>
        simp_tac bool_ss [] >> metis_tac[]) >>
     metis_tac[]) >>
  `~is_pseudo y.inst_opcode /\ write_effects y.inst_opcode <> {}` by
    metis_tac[] >>
  `y <> call` by
    (strip_tac >>
     `MEM call (dft_block order bb).bb_instructions /\
      MEM x (dft_block order bb).bb_instructions` by
       metis_tac[MEM_APPEND, MEM] >>
     `x = call` by metis_tac[all_distinct_map_mem_inj] >>
     gvs[ALL_DISTINCT_APPEND]) >>
  `MEM y left` by
    (gvs[MEM_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `?z. MEM z pre /\ z.inst_id = y.inst_id` by
    (irule dft_block_writer_prefix >> simp[] >>
     qexistsl [`bb`, `call`, `left`, `order`,
               `mid' ++ chk::post`, `mid ++ chk::right`] >> simp[]) >>
  `MEM z (dft_block order bb).bb_instructions /\
   MEM x (dft_block order bb).bb_instructions` by
    metis_tac[MEM_APPEND, MEM] >>
  `z = x` by metis_tac[all_distinct_map_mem_inj] >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem dft_block_check_prefix:
  !bb order left chk right pre post x.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ chk::post /\
    ((inst_wf chk /\ chk.inst_opcode = ASSERT) \/ right = []) /\
    MEM x pre /\ ~is_pseudo x.inst_opcode ==>
    ?y. MEM y left /\ y.inst_id = x.inst_id
Proof
  rpt gen_tac >> strip_tac
  >- (irule dft_block_assert_prefix >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)` by
    metis_tac[dft_block_well_formed_gen] >>
  `ALL_DISTINCT (dft_block order bb).bb_instructions` by
    (irule (INST_TYPE [beta |-> ``:num``] ALL_DISTINCT_MAP) >>
     qexists_tac `\i. i.inst_id` >> simp[]) >>
  `from_block bb.bb_instructions x` by
    (irule dft_block_from_orig >> qexists_tac `order` >>
     simp[MEM_FILTER] >> metis_tac[MEM_APPEND, MEM]) >>
  `?y. MEM y bb.bb_instructions /\ y.inst_id = x.inst_id` by
    (qpat_x_assum `from_block _ _` mp_tac >>
     pure_rewrite_tac[from_block_def] >>
     metis_tac[flip_operands_inst_id]) >>
  `y <> chk` by
    (strip_tac >>
     `MEM chk (dft_block order bb).bb_instructions /\
      MEM x (dft_block order bb).bb_instructions` by
       metis_tac[MEM_APPEND, MEM] >>
     `x = chk` by metis_tac[all_distinct_map_mem_inj] >>
     gvs[ALL_DISTINCT_APPEND]) >>
  qexists_tac `y` >> gvs[]
QED

Theorem dft_block_check_interval_safe:
  !bb order left call mid chk right pre mid' post bad.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::mid ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ call::mid' ++ chk::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    ((inst_wf chk /\ chk.inst_opcode = ASSERT) \/ right = []) /\
    EVERY (\i. ~bad i) mid /\
    (!i. bad (flip_operands i) = bad i) /\
    (!i. bad i ==> ~is_pseudo i.inst_opcode /\ write_effects i.inst_opcode <> {}) ==>
    EVERY (\i. ~bad i) mid'
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM x (pre ++ call::mid') /\ ~is_pseudo x.inst_opcode ==>
    ?y. MEM y (left ++ call::mid) /\ y.inst_id = x.inst_id` by
    (rpt gen_tac >> strip_tac >>
     irule dft_block_check_prefix >> metis_tac[APPEND_ASSOC]) >>
  irule dft_block_interval_safe >> simp[] >>
  qexistsl [`bb`, `call`, `chk`, `left`, `mid`, `order`, `post`, `pre`, `right`] >>
  fs[MEM_APPEND] >> metis_tac[]
QED

Theorem flip_operands_invoke_iff:
  !i. ((flip_operands i).inst_opcode = INVOKE <=> i.inst_opcode = INVOKE)
Proof
  `!i. i.inst_opcode = INVOKE ==> (flip_operands i).inst_opcode = INVOKE` by
    (rpt strip_tac >>
     simp[flip_operands_def, passSharedDefsTheory.is_comparator_def] >>
     BasicProvers.every_case_tac >> simp[]) >>
  metis_tac[flip_operands_involution]
QED

Theorem call_check_bad_effects:
  (!i. i.inst_opcode = INVOKE ==>
    ~is_pseudo i.inst_opcode /\ write_effects i.inst_opcode <> {}) /\
  (!i. write_effects i.inst_opcode <> {} ==> ~is_pseudo i.inst_opcode)
Proof
  conj_tac
  >- simp[venomInstTheory.is_pseudo_def, venomEffectsTheory.write_effects_def,
          venomEffectsTheory.all_effects_def] >>
  gen_tac >> Cases_on `i.inst_opcode` >>
  simp[venomInstTheory.is_pseudo_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.empty_effects_def]
QED

Theorem dft_block_check_interval_guards:
  !bb order left call mid chk right pre mid' post.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::mid ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ call::mid' ++ chk::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    ((inst_wf chk /\ chk.inst_opcode = ASSERT) \/ right = []) /\
    EVERY (\i. i.inst_opcode <> INVOKE) mid ==>
    EVERY (\i. i.inst_opcode <> INVOKE) mid' /\
    (EVERY (\i. write_effects i.inst_opcode = {}) mid ==>
     EVERY (\i. write_effects i.inst_opcode = {}) mid')
Proof
  rpt gen_tac >> strip_tac >> (conj_tac
  >- (ho_match_mp_tac dft_block_check_interval_safe >> simp[flip_operands_invoke_iff] >>
      qexistsl [`bb`, `order`, `left`, `call`, `mid`, `chk`, `right`, `pre`, `post`] >>
      simp[] >> metis_tac[call_check_bad_effects])) >>
  strip_tac >>
  `EVERY (\i. ~(write_effects i.inst_opcode <> {})) mid'` suffices_by simp[] >>
  ho_match_mp_tac dft_block_check_interval_safe >>
  simp[cj 2 (REWRITE_RULE [eff_equiv_def] (cj 2 flip_operands_eff_equiv))] >>
  qexistsl [`bb`, `order`, `left`, `call`, `mid`, `chk`, `right`, `pre`, `post`] >>
  simp[] >> metis_tac[call_check_bad_effects]
QED

Theorem calls_flagged_splits:
  !bbs is.
    calls_flagged bbs is <=>
    !pre call post.
      is = pre ++ call::post /\
      (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) ==>
      ?v. call.inst_outputs = [v] /\ flag_path bbs [v] post
Proof
  gen_tac >> Induct >- simp[calls_flagged_def] >>
  gen_tac >> simp[calls_flagged_def] >> eq_tac
  >- (strip_tac >> rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >> Cases_on `pre`
      >- (gvs[] >> Cases_on `call.inst_outputs` >> gvs[] >>
          rename1 `case outs of [] => _ | _::_ => _` >>
          Cases_on `outs` >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  strip_tac >> conj_tac
  >- (strip_tac >>
      first_x_assum (qspecl_then [`[]`, `h`, `is`] mp_tac) >>
      simp[] >> strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`h::pre`, `call`, `post`] mp_tac) >> simp[]
QED

Theorem distinct_outputs_suffix_flag_path:
  !is pre call post bbs v.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) is)) /\
    is = pre ++ call::post /\ MEM v call.inst_outputs /\
    check_witness bbs [v] post ==> flag_path bbs [v] post
Proof
  rpt gen_tac >> strip_tac >>
  irule check_witness_flag_path >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM]
QED

Theorem block_terminator_suffix:
  !bb pre chk post.
    bb_well_formed bb /\ bb.bb_instructions = pre ++ chk::post /\
    is_terminator chk.inst_opcode ==> post = []
Proof
  rpt strip_tac >>
  `LENGTH pre = PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `bb_well_formed bb` mp_tac >>
     pure_rewrite_tac[bb_well_formed_def] >> strip_tac >>
     qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH pre` mp_tac) >>
     asm_rewrite_tac[] >> simp[EL_APPEND_EQN]) >>
  gvs[] >> Cases_on `post` >> gvs[]
QED

Theorem flag_fails_check_shape:
  !bbs vs chk.
    flag_fails bbs vs chk ==>
    ~is_pseudo chk.inst_opcode /\ ~is_flippable chk.inst_opcode /\
    (chk.inst_opcode = ASSERT \/ is_terminator chk.inst_opcode)
Proof
  rpt gen_tac >> Cases_on `chk.inst_opcode` >>
  simp[flag_fails_def, venomInstTheory.is_pseudo_def,
       venomInstTheory.is_terminator_def, is_flippable_def,
       venomEffectsTheory.is_commutative_def,
       passSharedDefsTheory.is_comparator_def]
QED

Theorem flag_fails_unconditional_terminator:
  !bbs chk. flag_fails bbs [] chk ==> is_terminator chk.inst_opcode
Proof
  rpt gen_tac >> Cases_on `chk.inst_opcode` >>
  simp[flag_fails_def, venomInstTheory.is_terminator_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem flag_fails_conditional_operand:
  !bbs x chk.
    flag_fails bbs [x] chk /\ ~flag_fails bbs [] chk ==>
    MEM (Var x) chk.inst_operands
Proof
  rpt gen_tac >> Cases_on `chk.inst_opcode` >>
  asm_simp_tac (srw_ss()) [flag_fails_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> asm_simp_tac (srw_ss()) [])
QED

Theorem distinct_split_suffix:
  !pre x post left right.
    ALL_DISTINCT (pre ++ x::post) /\
    pre ++ x::post = left ++ x::right ==> post = right
Proof
  Induct >> Cases_on `left` >> simp_tac list_ss [] >> rpt strip_tac >>
  metis_tac[MEM_APPEND, MEM, APPEND_ASSOC, APPEND]
QED


Theorem dft_block_conditional_check:
  !bb order left call mid chk right pre post v x bbs.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    EVERY inst_wf bb.bb_instructions /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::mid ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ call::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    MEM v call.inst_outputs /\
    EVERY (\i. i.inst_opcode <> INVOKE) mid /\
    EVERY (\i. write_effects i.inst_opcode = empty_effects) mid /\
    copy_chain [v] mid x /\ flag_fails bbs [x] chk /\
    ~flag_fails bbs [] chk ==> flag_path bbs [v] post
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM call bb.bb_instructions /\ MEM chk bb.bb_instructions` by
    metis_tac[MEM_APPEND, MEM] >>
  `~is_pseudo call.inst_opcode /\ ~is_flippable call.inst_opcode` by
    (qpat_x_assum `call.inst_opcode = _ \/ _` strip_assume_tac >>
     simp[venomInstTheory.is_pseudo_def, is_flippable_def,
      venomEffectsTheory.is_commutative_def,
      passSharedDefsTheory.is_comparator_def]) >>
  drule flag_fails_check_shape >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (Var x) chk.inst_operands` by metis_tac[flag_fails_conditional_operand] >>
  `EVERY (\i. MEM i bb.bb_instructions) mid` by
    (simp[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `?a mid' z. (dft_block order bb).bb_instructions =
     a ++ call::mid' ++ chk::z /\ copy_chain [v] mid' x` by
    (irule dft_block_copy_chain >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
     (dft_block order bb).bb_instructions))` by
    metis_tac[dft_block_outputs_distinct] >>
  `ALL_DISTINCT (dft_block order bb).bb_instructions` by
    (irule (INST_TYPE [beta |-> ``:num``] ALL_DISTINCT_MAP) >>
     qexists_tac `\i. i.inst_id` >> metis_tac[dft_block_well_formed_gen]) >>
  `post = mid' ++ chk::z` by
    metis_tac[distinct_split_suffix, APPEND_ASSOC, APPEND] >>
  `inst_wf chk` by metis_tac[EVERY_MEM] >>
  Q.SUBGOAL_THEN `(inst_wf chk /\ chk.inst_opcode = ASSERT) \/ right = []` assume_tac
  >- metis_tac[block_terminator_suffix, APPEND_ASSOC, APPEND] >>
  drule_all dft_block_check_interval_guards >> strip_tac >>
  `EVERY (\i. write_effects i.inst_opcode = empty_effects) mid'` by
    (qpat_x_assum `EVERY _ mid ==> _` mp_tac >>
     simp[GSYM venomEffectsTheory.empty_effects_def]) >>
  irule distinct_outputs_suffix_flag_path >>
  conj_tac >- (qexistsl [`call`, `(dft_block order bb).bb_instructions`, `pre`] >> metis_tac[]) >>
  simp[check_witness_def] >>
  qexistsl [`mid'`, `chk`, `z`] >> simp[] >> metis_tac[]
QED

Theorem last_split_suffix:
  !pre call post chk.
    LAST (pre ++ call::post) = chk /\ call <> chk ==>
    ?mid. post = mid ++ [chk]
Proof
  rpt gen_tac >> Cases_on `post` >> simp[LAST_APPEND] >> strip_tac >>
  qexists_tac `BUTLAST (h::t)` >> metis_tac[APPEND_BUTLAST_LAST, NOT_CONS_NIL]
QED

Theorem dft_block_unconditional_check:
  !fn bb order left call mid chk right pre post bbs vs.
    wf_function fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    bb.bb_instructions = left ++ call::mid ++ chk::right /\
    (dft_block order bb).bb_instructions = pre ++ call::post /\
    (call.inst_opcode = CALL \/ call.inst_opcode = STATICCALL) /\
    EVERY (\i. i.inst_opcode <> INVOKE) mid /\
    flag_fails bbs [] chk ==> flag_path bbs vs post
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_terminator chk.inst_opcode` by metis_tac[flag_fails_unconditional_terminator] >>
  `right = []` by metis_tac[block_terminator_suffix, APPEND_ASSOC, APPEND] >>
  `call <> chk` by
    (strip_tac >> qpat_x_assum `call.inst_opcode = _ \/ _` strip_assume_tac >>
     gvs[venomInstTheory.is_terminator_def]) >>
  `LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions` by
    metis_tac[dft_block_same_last] >>
  `LAST bb.bb_instructions = chk` by simp[LAST_APPEND] >>
  `?mid'. post = mid' ++ [chk]` by metis_tac[last_split_suffix] >>
  `(dft_block order bb).bb_instructions = pre ++ call::mid' ++ chk::[]` by
    metis_tac[APPEND_ASSOC, APPEND] >>
  Q.SUBGOAL_THEN `(inst_wf chk /\ chk.inst_opcode = ASSERT) \/ right = []` assume_tac
  >- simp[] >>
  drule_all dft_block_check_interval_guards >> strip_tac >>
  asm_rewrite_tac[] >> irule unconditional_check_flag_path >> simp[]
QED

Theorem flip_operands_call_iff[local]:
  !i. ((flip_operands i).inst_opcode = CALL \/
       (flip_operands i).inst_opcode = STATICCALL) <=>
      (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL)
Proof
  `!i. (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) ==>
       ((flip_operands i).inst_opcode = CALL \/
        (flip_operands i).inst_opcode = STATICCALL)` by
    (rpt strip_tac >>
     simp[flip_operands_def, passSharedDefsTheory.is_comparator_def] >>
     BasicProvers.every_case_tac >> simp[]) >>
  metis_tac[flip_operands_involution]
QED

Theorem dft_block_calls_flagged:
  !fn bb order.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    calls_flagged fn.fn_blocks bb.bb_instructions ==>
    calls_flagged fn.fn_blocks (dft_block order bb).bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `EVERY inst_wf bb.bb_instructions` by
    metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    (qpat_x_assum `ssa_form fn` mp_tac >>
     pure_rewrite_tac[ssa_form_def, venomInstTheory.fn_insts_def] >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `bb` >>
     Q.SPEC_TAC (`fn.fn_blocks`, `bbs`) >> Induct >>
     simp[venomInstTheory.fn_insts_blocks_def] >>
     rpt gen_tac >> strip_tac >> Cases_on `bb = h` >>
     simp[] >> gvs[ALL_DISTINCT_APPEND]) >>
  simp[Once calls_flagged_splits] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_pseudo call.inst_opcode /\ ~is_flippable call.inst_opcode` by
    (qpat_x_assum `call.inst_opcode = _ \/ _` strip_assume_tac >>
     simp[venomInstTheory.is_pseudo_def, is_flippable_def,
       venomEffectsTheory.is_commutative_def,
       passSharedDefsTheory.is_comparator_def]) >>
  `from_block bb.bb_instructions call` by
    (irule dft_block_from_orig >> qexists_tac `order` >>
     simp[MEM_FILTER] >> metis_tac[MEM_APPEND, MEM]) >>
  `MEM call bb.bb_instructions` by
    (qpat_x_assum `from_block _ _` mp_tac >>
     simp[from_block_def] >> strip_tac >> gvs[] >>
     `j.inst_opcode = CALL \/ j.inst_opcode = STATICCALL` by
       metis_tac[flip_operands_call_iff] >>
     fs[is_flippable_def, venomEffectsTheory.is_commutative_def,
       passSharedDefsTheory.is_comparator_def]) >>
  qpat_x_assum `MEM call bb.bb_instructions` mp_tac >>
  rewrite_tac[MEM_SPLIT] >> strip_tac >>
  rename1 `bb.bb_instructions = left ++ call::tail` >>
  `?v. call.inst_outputs = [v] /\ flag_path fn.fn_blocks [v] tail` by
    metis_tac[calls_flagged_splits] >>
  qexists_tac `v` >> conj_tac >- simp[] >>
  `(dft_block order bb).bb_instructions = pre ++ call::post` by
    metis_tac[APPEND, APPEND_ASSOC] >>
  drule flag_path_check_witness >> simp[check_witness_def] >> strip_tac
  >- (`bb.bb_instructions = left ++ call::pre' ++ chk::post'` by
        simp[APPEND_ASSOC] >>
      drule_all dft_block_unconditional_check >> simp[]) >>
  `bb.bb_instructions = left ++ call::pre' ++ chk::post'` by
    simp[APPEND_ASSOC] >>
  Cases_on `flag_fails fn.fn_blocks [] chk`
  >- (drule_all dft_block_unconditional_check >> simp[]) >>
  `MEM v call.inst_outputs` by simp[] >>
  drule_all dft_block_conditional_check >> simp[]
QED

(* CALL and STATICCALL read all effects, so they depend on every
   earlier writer.  An
   ASSERT has no effects, and no outputs (inst_wf), so it is a DFS entry; entries are
   processed in block order, so everything emitted before it comes from
   before it in the input.  SSA keeps the flag and its ASSIGN copies from
   being redefined in between. *)
Theorem dft_blocks_call_checks_ok:
  !fn bbs'.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    EVERY (\bb. non_pseudo_defs_before_uses bb.bb_instructions) fn.fn_blocks /\
    LIST_REL (\bb bb'. bb' = bb \/ ?order. bb' = dft_block order bb)
      fn.fn_blocks bbs' /\
    call_checks_ok fn ==>
    call_checks_ok (fn with fn_blocks := bbs')
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\bb. bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions) fn.fn_blocks` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     conj_tac >- metis_tac[wf_function_def] >>
     conj_tac >- metis_tac[wf_fn_block_inst_ids_distinct] >>
     qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `!vs i. flag_fails fn.fn_blocks vs i ==> flag_fails bbs' vs i` by
    (rpt strip_tac >> drule_all dft_blocks_flag_fails >> simp[]) >>
  simp[call_checks_ok_def, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM bb' bbs'` >>
  `?bb. MEM bb fn.fn_blocks /\
    (bb' = bb \/ ?order. bb' = dft_block order bb)` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `MEM bb' bbs'` mp_tac >>
     simp[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  `calls_flagged fn.fn_blocks bb.bb_instructions /\
    non_pseudo_defs_before_uses bb.bb_instructions` by
    (conj_tac
     >- (qpat_x_assum `call_checks_ok fn` mp_tac >>
         simp[call_checks_ok_def, EVERY_MEM] >> disch_then drule >> simp[]) >>
     qpat_x_assum `EVERY (\bb. non_pseudo_defs_before_uses _) _` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  irule calls_flagged_environment >> qexists_tac `fn.fn_blocks` >> simp[] >>
  gvs[] >> drule_all dft_block_calls_flagged >> simp[]
QED
