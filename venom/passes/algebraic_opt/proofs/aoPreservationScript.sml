(* Top-level WF & SSA preservation for ao_transform_function.
 *
 * TOP-LEVEL:
 *   ao_preserves_wf_function  — wf_function preserved
 *   ao_preserves_ssa_form     — ssa_form preserved
 *   ao_phases123_preserve_wf  — phases 1-3 preserve wf + ssa + inst_wf
 *)

Theory aoPreservation
Ancestors
  algebraicOptDefs aoPhase1Wf aoWf aoPhase3Wf aoPhase3Ids aoPhase3Ssa
  aoPhase4Wf aoPhase4Ssa aoPeepholeSim
  passSimulationDefs passSimulationProps venomWf venomInst
Libs
  BasicProvers

(* ao_fresh_id_{gt,ge,inj}, foldl_max_*, fn_max_inst_id_bound,
   all_distinct_{bound,pred}_split reused from aoWf (transitive ancestor). *)

(* ao_fresh_var is injective on our suffixes *)
Theorem ao_fresh_var_full_inj:
  !id1 s1 id2 s2.
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
    ao_fresh_var id1 s1 = ao_fresh_var id2 s2 ==>
    id1 = id2 /\ s1 = s2
Proof
  rpt strip_tac >> gvs[] >>
  fs[ao_fresh_var_def, stringTheory.STRCAT_11,
     ASCIInumbersTheory.toString_inj]
QED

Triviality fn_insts_blocks_every[local]:
  !blocks p. EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.EVERY_APPEND]
QED

(* ===== Top-level WF preservation ===== *)

Theorem ao_preserves_wf_function:
  !fn. wf_function fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function (ao_transform_function fn)
Proof
  rpt strip_tac >>
  simp[ao_transform_function_def, LET_THM] >>
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

(* ===== Top-level SSA preservation ===== *)


(* ===== Phase 1 instruction-level facts ===== *)

Triviality fn_insts_block_map[local]:
  !f fn.
    fn_insts (function_map_transform (block_map_transform f) fn) =
    MAP f (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[function_map_transform_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, block_map_transform_def, listTheory.MAP_APPEND]
QED

Triviality map_inst_id_fn_insts[local]:
  !fn. MAP (\i. i.inst_id) (fn_insts fn) =
       FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)
Proof
  gen_tac >> simp[fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED

(* phase 1 keeps every instruction id, hence the fresh-var namespace *)
Triviality phase1_fresh_vars[local]:
  !fn.
    ao_fn_fresh_vars
      (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
    ao_fn_fresh_vars fn
Proof
  gen_tac >>
  simp[ao_fn_fresh_vars_def, fn_insts_block_map, listTheory.MAP_MAP_o,
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

(* phase 1 introduces no new Var operand: it only reorders ADD's [Label;Lit] *)
Triviality ao_handle_offset_inst_operand_var[local]:
  !inst w. MEM (Var w) (ao_handle_offset_inst inst).inst_operands ==>
           MEM (Var w) inst.inst_operands
Proof
  rw[ao_handle_offset_inst_def] >> every_case_tac >> gvs[]
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
  drule ao_handle_offset_inst_operand_var >> metis_tac[]
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
     ao_cmp_flip_function (fn_max_inst_id fn1) (dfg_build_function fn1) fn1)
Proof
  gen_tac >>
  simp[ao_transform_function_def, LET_THM] >>
  simp[fmt_block_map] >>
  simp[function_map_transform_def]
QED

(* ===== Top-level SSA preservation ===== *)

Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn /\ wf_function fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    ssa_form (ao_transform_function fn)
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  simp[ao_transform_function_unfold, LET_THM] >>
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
    (irule ao_phase3_preserves_ssa >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
  drule_all scan_inserts_cmp_id_comparator >> strip_tac >>
  `~MEM (ao_fresh_var c "iz")
     (FLAT (MAP (\i. i.inst_outputs)
       (fn_insts (function_map_transform
         (ao_transform_block mid dfg ra targets) fn0))))` by
    (irule ao_phase3_no_cmp_iz >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `~MEM (ao_fresh_var _ _) _` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
QED

(* ===== Phases 1-3 preserve wf + ssa + inst_wf =====
   Used by the main composition theorem (algebraicOptProof) to discharge the
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
    (irule ao_phase3_preserves_ssa >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
   Proved via ao_phase3_no_cmp_operand_iz applied to the phase-1 result fn0,
   whose operand/output/target cleanliness is inherited from
   ao_fresh_names_disjoint fn (phase 1 introduces no new Var operands). *)
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
      v NOTIN ao_cmp_fresh_vars fn1)
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
     prove the latter, which matches ao_phase3_no_cmp_operand_iz directly *)
  `!inst v.
     MEM inst (fn_insts
       (function_map_transform (ao_transform_block mid dfg ra targets) fn0)) /\
     MEM (Var v) inst.inst_operands ==>
     v NOTIN ao_cmp_fresh_vars
       (function_map_transform (ao_transform_block mid dfg ra targets) fn0)`
    suffices_by simp[function_map_transform_def, Abbr `fn0`] >>
  rpt strip_tac >> fs[ao_cmp_fresh_vars_def] >>
  qspecl_then [`mid`,`dfg`,`ra`,`targets`,`fn0`,`i.inst_id`] mp_tac
    ao_phase3_no_cmp_operand_iz >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  `MEM (Var v) (FLAT (MAP (\i. i.inst_operands)
     (fn_insts (function_map_transform
        (ao_transform_block mid dfg ra targets) fn0))))` by
    (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  gvs[]
QED

val _ = export_theory();
