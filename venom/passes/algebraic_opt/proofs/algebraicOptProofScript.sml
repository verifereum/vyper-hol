(* Algebraic optimization correctness: main composition theorem.
 *
 *)

Theory algebraicOptProof
Ancestors
  algebraicOptDefs
  aoPhase1Proof aoPhase2Proof aoPhase3Proof aoPhase4Proof
  aoPreservation aoTargetProps
  stateEquiv stateEquivProps execEquivProps
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  passSimulationProps passSimulationDefs
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def"]

(* ===== Main composition ===== *)

Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv' = ao_fn_total_fresh_vars fn in
    wf_function fn /\ wf_ssa fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn /\
    FDOM s.vs_vars = {} /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
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
  (* Phase 3: fn0 → fn1 simulation *)
  `(?e. run_blocks fuel ctx fn0 s = Error e) \/
   lift_result (state_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn1 s)` by
    (mp_tac (SIMP_RULE std_ss [LET_THM] ao_phase3_correct) >>
     disch_then (qspecl_then [`fuel`,`ctx`,`fn`,`s`] mp_tac) >>
     simp[Abbr `fn0`, Abbr `fn1`, Abbr `targets`, Abbr `dfg`,
          Abbr `ra`, Abbr `mid`] >>
     disch_then match_mp_tac >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  (* WF preservation (phases 1-3) *)
  `wf_function fn1 /\ ssa_form fn1 /\ EVERY inst_wf (fn_insts fn1)` by
    (mp_tac (SIMP_RULE std_ss [LET_THM] ao_phases123_preserve_wf) >>
     disch_then (qspec_then `fn` mp_tac) >>
     simp[Abbr `fn0`, Abbr `fn1`, Abbr `targets`, Abbr `dfg`,
          Abbr `ra`, Abbr `mid`] >>
     metis_tac[]) >>
  (* cmp iszero fresh-var operand disjointness (phases 1-3) *)
  `!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
     v NOTIN ao_cmp_fresh_vars fn1` by
    (mp_tac (SIMP_RULE std_ss [LET_THM] ao_phases123_cmp_fresh_disjoint) >>
     disch_then (qspec_then `fn` mp_tac) >>
     simp[Abbr `fn0`, Abbr `fn1`, Abbr `targets`, Abbr `dfg`,
          Abbr `ra`, Abbr `mid`] >>
     metis_tac[]) >>
  (* Phase 4: fn1 → cmp_flip simulation *)
  qabbrev_tac `dfg1 = dfg_build_function fn1` >>
  qabbrev_tac `dead = ao_cmp_flip_dead_vars dfg1 fn1` >>
  `(?e. run_blocks fuel ctx fn1 s = Error e) \/
   lift_result (state_equiv dead) (execution_equiv dead)
     (execution_equiv dead) (run_blocks fuel ctx fn1 s)
     (run_blocks fuel ctx
        (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)` by
    (mp_tac (SIMP_RULE std_ss [LET_THM] ao_phase4_correct) >>
     disch_then (qspecl_then [`fuel`,`ctx`,`fn1`,`s`] mp_tac) >>
     simp[Abbr `dfg1`, Abbr `dead`] >>
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
