(* Top-level WF & SSA preservation for ao_transform_function.
 *
 * TOP-LEVEL:
 *   ao_transform_preserves_wf  — wf_function preserved
 *   ao_transform_preserves_ssa — ssa_form preserved, given output freshness
 *   fn_inst_wf_fn_insts        — fn_inst_wf as EVERY over fn_insts
 *   ao_phases123_preserve_wf, ao_phases123_cmp_fresh_disjoint,
 *   ao_phases1234_preserve_wf_ssa
 *                              — side conditions of the phase 4/5 lemmas
 *)

Theory aoPreservation
Ancestors
  algebraicOptDefs aoPhase1Wf aoWf aoPhase3Wf aoPhase3Ids aoPhase3Ssa
  aoPhase4Wf aoPhase4Ssa aoPhase5Wf aoPeepholeSim
  passSimulationDefs passSimulationProps venomWf venomInst
Libs
  BasicProvers

Theorem fn_inst_wf_fn_insts:
  !fn. fn_inst_wf fn <=> EVERY inst_wf (fn_insts fn)
Proof
  simp[fn_inst_wf_compute, fn_insts_def, fn_insts_blocks_every]
QED

(* ===== Top-level WF preservation ===== *)

Theorem ao_transform_preserves_wf:
  !fn. wf_function fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function (ao_transform_function fn)
Proof
  rpt strip_tac >>
  simp[ao_transform_function_def, LET_THM] >>
  irule ao_phase5_preserves_wf >>
  irule ao_phase4_preserves_wf >>
  simp[fn_max_inst_id_bound] >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all dfgAnalysisPropsTheory.dfg_build_function_uses_sound >>
      simp[])
  >- (qabbrev_tac `fn0 = function_map_transform
        (block_map_transform ao_handle_offset_inst) fn` >>
      `wf_function fn0` by
        (simp[Abbr `fn0`] >> irule ao_phase1_preserves_wf >> simp[]) >>
      `EVERY inst_wf (fn_insts fn0)` by
        (simp[Abbr `fn0`] >>
         irule ao_phase1_preserves_inst_wf >> simp[]) >>
      `wf_function (function_map_transform
         (ao_transform_block (fn_max_inst_id fn0)
           (dfg_build_function fn0) (range_analyze fn0)
           (ao_compute_fn_iszero_targets fn0)) fn0)` by
        (irule ao_phase3_preserves_wf >>
         simp[fn_max_inst_id_bound] >>
         fs[fn_insts_def, fn_insts_blocks_every, Abbr `fn0`,
            function_map_transform_def]) >>
      simp[GSYM block_map_transform_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      fs[Abbr `fn0`, function_map_transform_def])
QED

(* ===== Phase 1 instruction-level facts ===== *)

(* phase 1 keeps every instruction id, hence the fresh-var namespace *)
Triviality phase1_fresh_vars[local]:
  !fn.
    ao_fn_fresh_vars
      (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
    ao_fn_fresh_vars fn
Proof
  gen_tac >>
  simp[ao_fn_fresh_vars_def, fn_max_inst_id_def, fn_insts_block_map, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, ao_handle_offset_inst_preserves_id]
QED

Triviality phase1_inst_ids[local]:
  !fn. fn_inst_ids_distinct fn ==>
    fn_inst_ids_distinct
      (function_map_transform (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  `!g. fn_inst_ids_distinct g <=> ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts g))`
    by simp[fn_inst_ids_distinct_def, map_inst_id_fn_insts] >>
  fs[fn_insts_block_map, listTheory.MAP_MAP_o, combinTheory.o_DEF,
     ao_handle_offset_inst_preserves_id]
QED

Triviality phase1_freshness[local]:
  !fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    (!inst v.
       MEM inst (fn_insts
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn)) /\
       MEM v inst.inst_outputs ==>
       v NOTIN ao_fn_fresh_vars
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn))
Proof
  rpt strip_tac >>
  gvs[fn_insts_block_map, listTheory.MEM_MAP, ao_handle_offset_inst_outputs,
      phase1_fresh_vars] >>
  metis_tac[]
QED

Triviality phase1_operand_freshness[local]:
  !fn.
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    (!inst v.
       MEM inst (fn_insts
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn)) /\
       MEM (Var v) inst.inst_operands ==>
       v NOTIN ao_fn_fresh_vars
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn))
Proof
  rpt strip_tac >>
  gvs[fn_insts_block_map, listTheory.MEM_MAP, phase1_fresh_vars] >>
  drule ao_handle_offset_inst_var_operand >> metis_tac[]
QED

(* function_map_transform of a 1:1 block map, in record-with form *)
Triviality fmt_block_map[local]:
  !f fn.
    function_map_transform (block_map_transform f) fn =
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions := MAP f bb.bb_instructions) fn.fn_blocks
Proof
  rpt gen_tac >>
  `block_map_transform f =
   \bb. bb with bb_instructions := MAP f bb.bb_instructions` by
    simp[FUN_EQ_THM, block_map_transform_def] >>
  asm_simp_tac std_ss [function_map_transform_def]
QED

(* ao_transform_function in terms of function_map_transform (phases stacked) *)
Triviality ao_transform_function_unfold[local]:
  !fn.
    ao_transform_function fn =
    (let fn0 = function_map_transform
                 (block_map_transform ao_handle_offset_inst) fn in
     let fn1 = function_map_transform
                 (ao_transform_block (fn_max_inst_id fn0) (dfg_build_function fn0)
                   (range_analyze fn0) (ao_compute_fn_iszero_targets fn0)) fn0 in
     let fn2 = ao_cmp_flip_function (fn_max_inst_id fn1)
                 (dfg_build_function fn0) (dfg_build_function fn1) fn1 in
     ao_or_truthy_function (dfg_build_function fn0) (dfg_build_function fn2) fn2)
Proof
  gen_tac >>
  simp[ao_transform_function_def, LET_THM] >>
  simp[fmt_block_map] >>
  simp[function_map_transform_def]
QED

(* ===== Top-level SSA preservation ===== *)

Theorem ao_transform_preserves_ssa:
  !fn. ssa_form fn /\ wf_function fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    ssa_form (ao_transform_function fn)
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  simp[ao_transform_function_unfold, LET_THM] >>
  irule ao_phase5_preserves_ssa >>
  qabbrev_tac `fn0 = function_map_transform
    (block_map_transform ao_handle_offset_inst) fn` >>
  (* phase 1 facts *)
  `wf_function fn0` by
    (simp[Abbr `fn0`] >> irule ao_phase1_preserves_wf >> simp[]) >>
  `ssa_form fn0` by
    (simp[Abbr `fn0`] >> irule ao_phase1_preserves_ssa >> simp[]) >>
  `fn_inst_ids_distinct fn0` by
    (simp[Abbr `fn0`] >> metis_tac[phase1_inst_ids]) >>
  `!inst v. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs ==>
            v NOTIN ao_fn_fresh_vars fn0` by
    (simp[Abbr `fn0`] >> metis_tac[phase1_freshness]) >>
  qabbrev_tac `mid = fn_max_inst_id fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  (* phase 3 facts *)
  `ssa_form (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_preserves_ssa >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> simp[Abbr `mid`]) >>
  `fn_inst_ids_distinct
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_inst_ids_distinct >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     simp[Abbr `mid`] >> metis_tac[fn_max_inst_id_bound]) >>
  (* phase 4 *)
  irule ao_phase4_preserves_ssa >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  (* remaining: disjointness of inserted fresh vars from phase-3 outputs *)
  rpt strip_tac >>
  rename1 `MEM (aid, out, f, c) inserts` >>
  drule_all scan_inserts_fresh_form >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  qspecl_then [`mid`,`dfg`,`ra`,`targets`,`fn0`] mp_tac
    ao_phase3_outputs_fresh >>
  impl_tac >- (conj_tac >- simp[Abbr `mid`] >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> simp[] >>
  irule ao_fresh_id_var_fresh >> simp[]
QED

(* ===== Phases 1-3 preserve wf + ssa + inst_wf =====
   Used by the main composition theorem (algebraicOptCorrectness) to discharge the
   well-formedness side conditions of the phase-4 simulation lemma.
   The ssa preservation requires ao_fresh_names_disjoint fn, matching the
   public-API precondition (mirrors mem2var's m2v_fresh_names_disjoint). *)
Theorem ao_phases123_preserve_wf:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn ==>
    wf_function fn1 /\ ssa_form fn1 /\ EVERY inst_wf (fn_insts fn1)
Proof
  gen_tac >> simp[LET_THM] >> strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  (* Capture the phase-1 result fn0 exactly as it appears in the goal, so the
     abbreviation folds reliably regardless of simp normalization. *)
  qmatch_goalsub_abbrev_tac `fn_max_inst_id fn0` >>
  `fn0 = function_map_transform
     (block_map_transform ao_handle_offset_inst) fn` by
    simp[Abbr `fn0`, fmt_block_map] >>
  (* phase 1 facts *)
  `wf_function fn0` by
    (pop_assum SUBST1_TAC >> irule ao_phase1_preserves_wf >> simp[]) >>
  `ssa_form fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> irule ao_phase1_preserves_ssa >>
     simp[]) >>
  `fn_inst_ids_distinct fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> metis_tac[phase1_inst_ids]) >>
  `EVERY inst_wf (fn_insts fn0)` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> irule ao_phase1_preserves_inst_wf >>
     simp[]) >>
  `!inst v. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs ==>
            v NOTIN ao_fn_fresh_vars fn0` by
    (fs[ao_fresh_names_disjoint_def] >> qpat_x_assum `fn0 = _` SUBST1_TAC >>
     metis_tac[phase1_freshness]) >>
  qmatch_goalsub_abbrev_tac `ao_transform_block mid dfg ra targets` >>
  `wf_function
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_preserves_wf >> rpt conj_tac
     >- (simp[Abbr `mid`] >> metis_tac[fn_max_inst_id_bound])
     >- first_assum ACCEPT_TAC
     >- fs[fn_insts_def, fn_insts_blocks_every]) >>
  `ssa_form
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_preserves_ssa >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> simp[Abbr `mid`]) >>
  `EVERY inst_wf (fn_insts
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0))` by
    (simp[Abbr `targets`] >> irule ao_phase3_preserves_inst_wf >>
     qpat_x_assum `fn0 = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  fs[Abbr `fn0`, function_map_transform_def, fmt_block_map]
QED

(* Phases 1-3 keep every operand out of the comparator iszero fresh-var
   namespace of fn1.  Consumed by the phase-4 simulation lemma
   (ao_phase4_correct) in the main composition.  Requires
   ao_fresh_names_disjoint fn since the fact is false if the source program
   already references an ao_<id>_iz name.
   Phase 4 names its helpers above fn_max_inst_id fn1, inside
   ao_fn_fresh_vars fn1, and ao_phase3_operands_fresh keeps every fn1
   operand out of that set. *)
Theorem ao_phases123_cmp_fresh_disjoint:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn ==>
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars (fn_max_inst_id fn1) fn1)
Proof
  gen_tac >> simp[LET_THM] >> strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  qmatch_goalsub_abbrev_tac `fn_max_inst_id fn0` >>
  `fn0 = function_map_transform
     (block_map_transform ao_handle_offset_inst) fn` by
    simp[Abbr `fn0`, fmt_block_map] >>
  (* phase 1 facts about fn0 *)
  `fn_inst_ids_distinct fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> metis_tac[phase1_inst_ids]) >>
  `!inst v. MEM inst (fn_insts fn0) /\ MEM (Var v) inst.inst_operands ==>
            v NOTIN ao_fn_fresh_vars fn0` by
    (fs[ao_fresh_names_disjoint_def] >> qpat_x_assum `fn0 = _` SUBST1_TAC >>
     metis_tac[phase1_operand_freshness]) >>
  `!inst v. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs ==>
            v NOTIN ao_fn_fresh_vars fn0` by
    (fs[ao_fresh_names_disjoint_def] >> qpat_x_assum `fn0 = _` SUBST1_TAC >>
     metis_tac[phase1_freshness]) >>
  (* drop the unfolding equality so later simps keep fn0 folded *)
  qpat_x_assum `fn0 = function_map_transform _ _` kall_tac >>
  qmatch_goalsub_abbrev_tac `ao_transform_block mid dfg ra targets` >>
  (* targets chains only reference source operands/outputs, hence are clean *)
  `!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==>
          w NOTIN ao_fn_fresh_vars fn0` by
    (simp[Abbr `targets`] >> ho_match_mp_tac ao_fn_iszero_targets_clean >>
     rpt strip_tac >> metis_tac[]) >>
  (* the goal body is the record-reduced form of this function_map_transform;
     prove the latter, which matches ao_phase3_operands_fresh directly *)
  `!inst v.
     MEM inst (fn_insts
       (function_map_transform (ao_transform_block mid dfg ra targets) fn0)) /\
     MEM (Var v) inst.inst_operands ==>
     v NOTIN ao_cmp_fresh_vars
       (fn_max_inst_id
         (function_map_transform (ao_transform_block mid dfg ra targets) fn0))
       (function_map_transform (ao_transform_block mid dfg ra targets) fn0)`
    suffices_by simp[function_map_transform_def, Abbr `fn0`] >>
  rpt strip_tac >> fs[ao_cmp_fresh_vars_def] >>
  qspecl_then [`mid`,`dfg`,`ra`,`targets`,`fn0`] mp_tac
    ao_phase3_operands_fresh >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `mid`]) >>
  disch_then drule_all >> simp[] >>
  irule ao_fresh_id_var_fresh >> simp[]
QED

(* ===== Phases 1-4 preserve wf + ssa =====
   Packages the phase-1-through-4 output (fn2 = comparator-flip result) wf and
   ssa facts for the main composition (algebraicOptProof), which needs them to
   discharge the phase-5 (OR-truthy) simulation side conditions.
   The ssa proof reuses the phase-4 inserted-fresh-var disjointness argument
   (scan_inserts_fresh_form + ao_phase3_outputs_fresh), hence
   ao_fresh_names_disjoint fn. *)
Theorem ao_phases1234_preserve_wf_ssa:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    let dfg1 = dfg_build_function fn1 in
    let mid1 = fn_max_inst_id fn1 in
    let fn2 = ao_cmp_flip_function mid1 dfg dfg1 fn1 in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn ==>
    wf_function fn2 /\ ssa_form fn2
Proof
  gen_tac >> simp[LET_THM] >> strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  (* capture the phase-1 result fn0 (unambiguous: it is the mid argument of the
     phase-3 ao_transform_block) and relate it to a function_map_transform *)
  qmatch_goalsub_abbrev_tac `ao_transform_block (fn_max_inst_id fn0) _ _ _` >>
  `fn0 = function_map_transform
     (block_map_transform ao_handle_offset_inst) fn` by
    simp[Abbr `fn0`, fmt_block_map] >>
  (* phase 1 facts *)
  `wf_function fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> irule ao_phase1_preserves_wf >> simp[]) >>
  `ssa_form fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> irule ao_phase1_preserves_ssa >> simp[]) >>
  `fn_inst_ids_distinct fn0` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> metis_tac[phase1_inst_ids]) >>
  `EVERY inst_wf (fn_insts fn0)` by
    (qpat_x_assum `fn0 = _` SUBST1_TAC >> irule ao_phase1_preserves_inst_wf >>
     simp[]) >>
  `!inst v. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs ==>
            v NOTIN ao_fn_fresh_vars fn0` by
    (fs[ao_fresh_names_disjoint_def] >> qpat_x_assum `fn0 = _` SUBST1_TAC >>
     metis_tac[phase1_freshness]) >>
  qpat_x_assum `fn0 = function_map_transform _ _` kall_tac >>
  qmatch_goalsub_abbrev_tac `ao_transform_block mid dfg ra targets` >>
  (* rewrite the goal's (collapsed) phase-3 result as a function_map_transform *)
  qmatch_goalsub_abbrev_tac `ao_cmp_flip_function _ _ _ fn1c` >>
  `fn1c = function_map_transform (ao_transform_block mid dfg ra targets) fn0` by
    simp[Abbr `fn1c`, Abbr `fn0`, function_map_transform_def] >>
  pop_assum SUBST_ALL_TAC >>
  (* phase 3 facts *)
  `ssa_form
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_preserves_ssa >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> simp[Abbr `mid`]) >>
  `wf_function
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    (irule ao_phase3_preserves_wf >> rpt conj_tac
     >- (simp[Abbr `mid`] >> metis_tac[fn_max_inst_id_bound])
     >- first_assum ACCEPT_TAC
     >- fs[fn_insts_def, fn_insts_blocks_every]) >>
  `fn_inst_ids_distinct
     (function_map_transform (ao_transform_block mid dfg ra targets) fn0)` by
    fs[wf_function_def] >>
  (* phase 4 *)
  conj_tac
  >- (irule ao_phase4_preserves_wf >> simp[fn_max_inst_id_bound] >>
      rpt strip_tac >>
      drule_all dfgAnalysisPropsTheory.dfg_build_function_uses_sound >> simp[]) >>
  irule ao_phase4_preserves_ssa >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  rename1 `MEM (aid, out, f, c) inserts` >>
  drule_all scan_inserts_fresh_form >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  qspecl_then [`mid`,`dfg`,`ra`,`targets`,`fn0`] mp_tac
    ao_phase3_outputs_fresh >>
  impl_tac >- (conj_tac >- simp[Abbr `mid`] >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> simp[] >>
  irule ao_fresh_id_var_fresh >> simp[]
QED

