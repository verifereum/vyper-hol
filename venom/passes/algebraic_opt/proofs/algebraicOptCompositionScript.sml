(* Algebraic optimization correctness: main composition theorem.
 *
 * The transform ao_transform_function has 4 phases:
 *   Phase 1: offset canonicalization (fn → fn0)
 *   Phase 2: iszero chain analysis (computes targets)
 *   Phase 3: main rewrite pass (fn0 → fn1)
 *   Phase 4: comparator flip (fn1 → final)
 *
 * Each phase has an independent correctness theorem.
 * Phases 1-2 are proved here; phases 3-4 and WF preservation
 * are cheated (the original cheats from the monolithic proof).
 *)

Theory algebraicOptComposition
Ancestors
  algebraicOptDefs algebraicOptWf algebraicOptProofs
  stateEquiv stateEquivProps execEquivProps
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  passSimulationProps passSimulationDefs
  analysisSimDefs rangeAnalysisDefs
  aoResolveObligation aoCmpFlipObligation
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def"]

(* ===== Phase 1: offset canonicalization ===== *)

Theorem ao_phase1_correct:
  !fuel ctx fn s.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s
Proof
  simp[LET_THM, run_blocks_offset_eq]
QED

(* ===== Phase 2: iszero chain analysis ===== *)

Theorem ao_phase2_correct:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (!inst x. MEM inst (fn_insts fn) /\
              MEM x inst.inst_outputs ==> lookup_var x s = NONE) ==>
    ao_targets_wf targets /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn0 = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `targets = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  rpt conj_tac
  >- metis_tac[ao_compute_fn_iszero_targets_wf, markerTheory.Abbrev_def]
  >- (simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
      `?inst. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs` by
        (simp[Abbr `targets`] >> metis_tac[ao_fn_targets_key_is_output]) >>
      `ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain` by
        fs[Abbr `targets`] >>
      drule ao_fn_targets_chain_tail_var >> strip_tac >>
      `?w. EL (k + 1) chain = Var w` by
        (first_x_assum (qspec_then `k + 1` mp_tac) >> simp[]) >>
      `ALOOKUP (ao_compute_fn_iszero_targets fn0) w <> NONE` by
        (drule ao_fn_targets_chain_var_is_key >>
         disch_then (qspecl_then [`k + 1`, `w`] mp_tac) >> simp[]) >>
      `?inst'. MEM inst' (fn_insts fn0) /\ MEM w inst'.inst_outputs` by
        (Cases_on `ALOOKUP (ao_compute_fn_iszero_targets fn0) w` >> fs[] >>
         metis_tac[ao_fn_targets_key_is_output]) >>
      `lookup_var w s = NONE` by
        (qpat_x_assum `MEM inst' (fn_insts fn0)` mp_tac >>
         simp[Abbr `fn0`, fn_insts_def] >> strip_tac >>
         drule fn_insts_blocks_map_offset >> strip_tac >>
         `MEM w inst0.inst_outputs` by
           fs[ao_handle_offset_inst_outputs] >>
         `MEM inst0 (fn_insts fn)` by fs[fn_insts_def] >>
         res_tac) >>
      fs[eval_operand_def])
  >- (simp[ao_chains_defined_at_def] >> rpt strip_tac >>
      `?inst. MEM inst (fn_insts fn0) /\ MEM v inst.inst_outputs` by
        (simp[Abbr `targets`] >> metis_tac[ao_fn_targets_key_is_output]) >>
      `lookup_var v s = NONE` by
        (qpat_x_assum `MEM inst (fn_insts fn0)` mp_tac >>
         simp[Abbr `fn0`, fn_insts_def] >> strip_tac >>
         drule fn_insts_blocks_map_offset >> strip_tac >>
         `MEM v inst0.inst_outputs` by
           fs[ao_handle_offset_inst_outputs] >>
         `MEM inst0 (fn_insts fn)` by fs[fn_insts_def] >>
         res_tac) >>
      fs[eval_operand_def, lookup_var_def])
QED

(* ===== Phase 3: main rewrite pass ===== *)
(* Cheated: contains original cheats (ao_chains_defined + block_inv preservation) *)

Theorem ao_phase3_correct:
  !fuel ctx fn fn0 fn1 targets dfg ra mid s.
    let fv = ao_fn_fresh_vars fn in
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    mid = fn_max_inst_id fn0 /\
    fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (!inst x. MEM inst (fn_insts fn) /\
              MEM x inst.inst_outputs ==> lookup_var x s = NONE) /\
    ao_targets_wf targets /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s /\
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn1 s)
Proof
  cheat
QED

(* ===== Phase 4: comparator flip ===== *)
(* Cheated: contains original cheat (cmp_flip_iszero_inv setup) *)

Theorem ao_phase4_correct:
  !fuel ctx fn1 s.
    let dfg1 = dfg_build_function fn1 in
    let dead = ao_cmp_flip_dead_vars dfg1 fn1 in
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1) /\
    fn_inst_ids_distinct fn1 /\
    (!inst. MEM inst (fn_insts fn1) ==> inst.inst_opcode <> INVOKE) /\
    (!inst v. MEM inst (fn_insts fn1) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN ao_fn_fresh_vars fn1) ==>
    (?e. run_blocks fuel ctx fn1 s = Error e) \/
    lift_result (state_equiv dead) (execution_equiv dead) (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)
Proof
  cheat
QED

(* ===== WF Preservation: phases 1-3 preserve structure ===== *)
(* Cheated: contains original cheat (fn_inst_ids_distinct from algebraicOptWf) *)

Theorem ao_phases123_preserve_wf:
  !fn fn0 fn1 mid dfg ra targets.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1) /\
    fn_inst_ids_distinct fn1 /\
    (!inst. MEM inst (fn_insts fn1) ==> inst.inst_opcode <> INVOKE) /\
    (!inst v. MEM inst (fn_insts fn1) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN ao_fn_fresh_vars fn1)
Proof
  cheat
QED

(* ===== Main composition ===== *)
(* Proved from the phase theorems above via:
   phase1 (equality) >> phase2 (soundness) >> phase3 (sim) >>
   wf_preservation >> phase4 (sim) >> lift_result_trans + lift_result_mono. *)

Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv' = ao_fn_total_fresh_vars fn in
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (!inst x. MEM inst (fn_insts fn) /\
              MEM x inst.inst_outputs ==> lookup_var x s = NONE) /\
    range_sound (df_widen_at NONE (range_analyze
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks))
      s.vs_current_bb 0) s /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `mid = fn_max_inst_id fn0` >>
  qabbrev_tac `fn1 = fn0 with fn_blocks :=
    MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks` >>
  (* Phase 1: fn ≡ fn0 *)
  `run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s` by
    (qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
     simp[markerTheory.Abbrev_def,
          SIMP_RULE std_ss [LET_THM] ao_phase1_correct]) >>
  (* Phase 2: from ao_phase2_correct *)
  `ao_targets_wf targets /\ ao_iszero_chain_inv targets s /\
   ao_chains_defined_at targets s` by
    (mp_tac (Q.SPECL [`fn`, `fn0`, `targets`, `s`] ao_phase2_correct) >>
     impl_tac
     >- (simp[Abbr `fn0`, Abbr `targets`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])
     >> simp[]) >>
  (* Phase 3: from ao_phase3_correct *)
  `(?e. run_blocks fuel ctx fn0 s = Error e) \/
   lift_result (state_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn1 s)` by
    (mp_tac (Q.SPECL [`fuel`,`ctx`,`fn`,`fn0`,`fn1`,`targets`,`dfg`,`ra`,`mid`,`s`]
               ao_phase3_correct) >>
     simp[LET_THM, Abbr `fn0`, Abbr `fn1`, Abbr `targets`, Abbr `dfg`,
          Abbr `ra`, Abbr `mid`] >>
     disch_then match_mp_tac >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  (* WF preservation *)
  `wf_function fn1 /\ ssa_form fn1 /\
   EVERY inst_wf (fn_insts fn1) /\ fn_inst_ids_distinct fn1 /\
   (!inst. MEM inst (fn_insts fn1) ==> inst.inst_opcode <> INVOKE) /\
   (!inst v. MEM inst (fn_insts fn1) /\
     MEM (Var v) inst.inst_operands ==> v NOTIN ao_fn_fresh_vars fn1)` by
    (mp_tac (Q.SPECL [`fn`,`fn0`,`fn1`,`mid`,`dfg`,`ra`,`targets`]
               ao_phases123_preserve_wf) >>
     impl_tac
     >- (simp[Abbr `fn0`, Abbr `fn1`, Abbr `targets`, Abbr `dfg`,
              Abbr `ra`, Abbr `mid`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])
     >> simp[]) >>
  (* Phase 4: *)
  qabbrev_tac `dfg1 = dfg_build_function fn1` >>
  qabbrev_tac `dead = ao_cmp_flip_dead_vars dfg1 fn1` >>
  `(?e. run_blocks fuel ctx fn1 s = Error e) \/
   lift_result (state_equiv dead) (execution_equiv dead)
     (execution_equiv dead) (run_blocks fuel ctx fn1 s)
     (run_blocks fuel ctx
        (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)` by
    (mp_tac (Q.SPECL [`fuel`,`ctx`,`fn1`,`s`] ao_phase4_correct) >>
     simp[LET_THM, Abbr `dfg1`, Abbr `dead`] >>
     disch_then match_mp_tac >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  (* Case split: fn0 error or lift_result *)
  Cases_on `?e. run_blocks fuel ctx fn0 s = Error e`
  >- (DISJ1_TAC >> gvs[]) >>
  gvs[] >>
  (* fn1 can't error: contradicts lift_result + no fn error *)
  `~(?e. run_blocks fuel ctx fn1 s = Error e)` by
    (strip_tac >>
     Cases_on `run_blocks fuel ctx fn s` >> gvs[lift_result_def]) >>
  gvs[] >>
  (* Rewrite goal target *)
  `ao_transform_function fn =
   ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1` by
    simp[ao_transform_function_def, LET_THM,
         Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`,
         Abbr `mid`, Abbr `targets`, Abbr `dfg1`] >>
  `ao_fn_total_fresh_vars fn =
   ao_fn_fresh_vars fn UNION dead` by
    simp[ao_fn_total_fresh_vars_def, LET_THM,
         Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`,
         Abbr `mid`, Abbr `targets`, Abbr `dead`, Abbr `dfg1`] >>
  qpat_x_assum `ao_transform_function fn = _` SUBST1_TAC >>
  qpat_x_assum `ao_fn_total_fresh_vars fn = _` SUBST1_TAC >>
  (* Compose via lift_result_trans + lift_result_mono *)
  irule (UNDISCH_ALL lift_result_trans) >>
  conj_tac >- metis_tac[state_equiv_trans] >>
  conj_tac >- metis_tac[execution_equiv_trans] >>
  qexists_tac `run_blocks fuel ctx fn1 s` >>
  conj_tac
  >- (irule lift_result_mono >>
      qexistsl_tac [`state_equiv (ao_fn_fresh_vars fn)`,
                    `execution_equiv (ao_fn_fresh_vars fn)`] >>
      rpt strip_tac >> simp[] >>
      metis_tac[state_equiv_subset, execution_equiv_subset,
                pred_setTheory.SUBSET_UNION])
  >- (irule lift_result_mono >>
      qexistsl_tac [`state_equiv dead`, `execution_equiv dead`] >>
      rpt strip_tac >> simp[] >>
      metis_tac[state_equiv_subset, execution_equiv_subset,
                pred_setTheory.SUBSET_UNION])
QED

val _ = export_theory();
