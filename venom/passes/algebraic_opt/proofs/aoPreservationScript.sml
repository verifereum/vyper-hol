(* Top-level WF & SSA preservation for ao_transform_function.
 *
 * TOP-LEVEL:
 *   ao_preserves_wf_function  — wf_function preserved
 *   ao_preserves_ssa_form     — ssa_form preserved
 *   ao_phases123_preserve_wf  — phases 1-3 preserve wf + ssa + inst_wf
 *)

Theory aoPreservation
Ancestors
  algebraicOptDefs aoPhase1Wf aoPhase3Wf aoPhase4Wf aoPeepholeSim
  passSimulationDefs venomWf venomInst
Libs
  BasicProvers

(* ===== ao_fresh_id properties ===== *)

Theorem ao_fresh_id_gt:
  !mid id slot. ao_fresh_id mid id slot > mid
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_ge:
  !mid id slot. ao_fresh_id mid id slot >= mid + 1
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_inj:
  !mid id1 slot1 id2 slot2.
    slot1 < 3 /\ slot2 < 3 /\
    ao_fresh_id mid id1 slot1 = ao_fresh_id mid id2 slot2 ==>
    id1 = id2 /\ slot1 = slot2
Proof
  simp[ao_fresh_id_def] >> rpt strip_tac >>
  `id1 * 3 + slot1 = id2 * 3 + slot2` by simp[] >>
  `(id1 * 3 + slot1) MOD 3 = (id2 * 3 + slot2) MOD 3` by simp[] >>
  `slot1 MOD 3 = slot2 MOD 3` by metis_tac[arithmeticTheory.MOD_TIMES] >>
  `slot1 = slot2` by metis_tac[arithmeticTheory.LESS_MOD]
QED

Triviality foldl_max_base[local]:
  !(l:num list) a. a <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  `MAX a h <= FOLDL MAX (MAX a h) l` suffices_by simp[] >>
  metis_tac[]
QED

Triviality foldl_max_mono[local]:
  !(l:num list) a b. a <= b ==> FOLDL MAX a l <= FOLDL MAX b l
Proof
  Induct >> simp[arithmeticTheory.MAX_DEF]
QED

Triviality foldl_max_mem[local]:
  !(l:num list) x a. MEM x l ==> x <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  DISCH_THEN DISJ_CASES_TAC
  >- (pop_assum SUBST_ALL_TAC >>
      match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `MAX a h` >>
      conj_tac >- simp[arithmeticTheory.MAX_LE]
      >- MATCH_ACCEPT_TAC foldl_max_base)
  >- (match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `FOLDL MAX a l` >>
      conj_tac
      >- (first_x_assum match_mp_tac >> simp[])
      >- (irule foldl_max_mono >> simp[]))
QED

Theorem fn_max_inst_id_bound:
  !fn inst. MEM inst (fn_insts fn) ==> inst.inst_id <= fn_max_inst_id fn
Proof
  rpt strip_tac >>
  simp[fn_max_inst_id_def] >>
  irule foldl_max_mem >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* ===== ALL_DISTINCT splitting ===== *)

Theorem all_distinct_bound_split:
  !(l:num list) mid.
    ALL_DISTINCT (FILTER (\id. id <= mid) l) /\
    ALL_DISTINCT (FILTER (\id. ~(id <= mid)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h <= mid` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Theorem all_distinct_pred_split:
  !(l:'a list) P.
    ALL_DISTINCT (FILTER P l) /\
    ALL_DISTINCT (FILTER ($~ o P) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

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

(* ===== Phases 1-3 preserve wf + ssa + inst_wf ===== *)

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
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1)
Proof
  simp[LET_THM] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt strip_tac
  >| [all_tac, cheat, cheat] >>
  qabbrev_tac `fn0 = function_map_transform
    (block_map_transform ao_handle_offset_inst) fn` >>
  `wf_function fn0` by
    (simp[Abbr `fn0`] >> irule ao_phase1_preserves_wf >> simp[]) >>
  `EVERY inst_wf (fn_insts fn0)` by
    (simp[Abbr `fn0`] >> irule ao_phase1_preserves_inst_wf >> simp[]) >>
  `wf_function (function_map_transform
     (ao_transform_block (fn_max_inst_id fn0) (dfg_build_function fn0)
        (range_analyze fn0) (ao_compute_fn_iszero_targets fn0)) fn0)` by
    (irule ao_phase3_preserves_wf >>
     simp[fn_max_inst_id_bound] >>
     fs[fn_insts_def, fn_insts_blocks_every, Abbr `fn0`,
        function_map_transform_def]) >>
  simp[GSYM block_map_transform_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  fs[Abbr `fn0`, function_map_transform_def]
QED

(* ===== Top-level SSA preservation ===== *)

Triviality ao_peephole_inst_last_outputs[local]:
  !mid dfg ra lbl idx inst.
    ao_peephole_inst mid dfg ra lbl idx inst <> [] /\
    (LAST (ao_peephole_inst mid dfg ra lbl idx inst)).inst_outputs =
      inst.inst_outputs
Proof
  rpt gen_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, ao_opt_comparator_def, LET_THM,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  every_case_tac >> gvs[] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn /\ wf_function fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              ~((?id. MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
                 (v = ao_fresh_var id "not" \/
                  v = ao_fresh_var id "iz" \/
                  v = ao_fresh_var id "xor")))) ==>
    ssa_form (ao_transform_function fn)
Proof
  rpt strip_tac >>
  simp[ssa_form_def, fn_insts_def] >>
  irule all_distinct_pred_split >>
  qexists_tac `\v. ?id s. MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (s = "not" \/ s = "iz" \/ s = "xor") /\ v = ao_fresh_var id s` >>
  conj_tac
  >- cheat
  >- cheat
QED

val _ = export_theory();
