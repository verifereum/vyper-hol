(* Phase 4: Comparator flip correctness — function-level lift.
 *
 * Uses block_sim_function_with_pred2_bb to lift ao_cmp_flip_block_sim
 * to run_blocks via the framework's fuel induction.
 *
 * TOP-LEVEL: ao_phase4_correct
 *)

Theory aoPhase4Proof
Ancestors
  algebraicOptDefs aoCmpFlipSim
  aoCmpFlipObligation
  venomExecSemantics venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_cmp_flip_dead_vars_def",
                  "cmp_flip_iszero_inv_def",
                  "ao_cmp_flip_scan_def"]

(* run_blocks does not depend on vs_inst_idx *)
(* run_blocks_inst_idx_irrel is provided by passSimulationProps *)

(* cmp_flip_iszero_inv reflexive when no vars defined *)
Triviality iszero_inv_refl_empty[local]:
  !flips insts s.
    FDOM s.vs_vars = {} ==>
    cmp_flip_iszero_inv flips insts s s
Proof
  rw[cmp_flip_iszero_inv_def] >>
  rpt strip_tac >>
  gvs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* ao_cmp_flip_function is function_map_transform when non-NULL *)
Triviality cmp_flip_is_map_transform[local]:
  !mid dfg fn flips removes inserts.
    ao_cmp_flip_scan dfg (fn_insts fn) = (flips, removes, inserts) /\
    ~NULL flips ==>
    ao_cmp_flip_function mid dfg fn =
    function_map_transform
      (\bb. bb with bb_instructions :=
        FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                  bb.bb_instructions))
      fn
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_function_def, function_map_transform_def, LET_THM]
QED

(* lookup_block on MEM block *)
Triviality lookup_block_mem_some[local]:
  !bb fn.
    wf_function fn /\ MEM bb fn.fn_blocks ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule venomExecPropsTheory.MEM_lookup_block >>
  gvs[wf_function_def, fn_labels_def]
QED

(* ===== Main theorem ===== *)

Theorem ao_phase4_correct:
  !fuel ctx fn1 s.
    let dfg1 = dfg_build_function fn1 in
    let dead = ao_cmp_flip_dead_vars dfg1 fn1 in
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1) /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    FDOM s.vs_vars = {} ==>
    (?e. run_blocks fuel ctx fn1 s = Error e) \/
    lift_result (state_equiv dead) (execution_equiv dead) (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  (* NULL case: function unchanged *)
  Cases_on `NULL (FST (ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)))`
  >- (`ao_cmp_flip_function (fn_max_inst_id fn1) (dfg_build_function fn1) fn1 = fn1`
        by (irule ao_cmp_flip_null_sim >> first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[] >> DISJ2_TAC >>
      irule lift_result_refl >>
      simp_tac std_ss [state_equiv_refl, execution_equiv_refl])
  >> (* Non-NULL case: reduce to vs_inst_idx=0 then use framework *)
  ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel] >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)` >>
  Cases_on `r` >>
  rename1 `ao_cmp_flip_scan _ _ = (flips, removes, inserts)` >>
  `~NULL flips` by gvs[] >>
  qabbrev_tac `mid = fn_max_inst_id fn1` >>
  qabbrev_tac `bt = \bb:basic_block. bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
              bb.bb_instructions)` >>
  `ao_cmp_flip_function mid (dfg_build_function fn1) fn1 =
   function_map_transform bt fn1` by
    (simp_tac std_ss [Abbr `bt`] >>
     irule cmp_flip_is_map_transform >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  qabbrev_tac `s0 = s with vs_inst_idx := 0` >>
  qspecl_then
    [`cmp_flip_iszero_inv flips (fn_insts fn1)`,
     `state_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)`,
     `execution_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)`,
     `bt`, `fn1`]
    mp_tac (SIMP_RULE std_ss [LET_THM] block_sim_function_with_pred2_bb) >>
  impl_tac
  >- (rpt conj_tac
      (* 1. P s s ==> R_ok s s *)
      >- simp_tac std_ss [state_equiv_refl]
      (* 2. R_ok ==> R_term *)
      >- (rpt strip_tac >> gvs[state_equiv_def, execution_equiv_def])
      (* 3. R_ok preserves control state *)
      >- simp_tac std_ss [state_equiv_def, execution_equiv_def]
      (* 4. bt preserves labels *)
      >- simp[Abbr `bt`]
      (* 5. P-preservation *)
      >- (rpt strip_tac >>
          `FST (ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)) =
           flips` by gvs[] >>
          `lookup_block bb.bb_label fn1.fn_blocks = SOME bb` by
            (irule lookup_block_mem_some >> simp[]) >>
          mp_tac (SIMP_RULE std_ss [LET_THM] ao_cmp_flip_block_ok_inv) >>
          disch_then (qspecl_then [`mid`, `fn1`,
            `bb.bb_label`, `bb`, `bt bb`, `fuel`, `ctx`,
            `s1`, `s2`, `s1'`, `s2'`] mp_tac) >>
          gvs[] >>
          disch_then irule >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (gvs[listTheory.EVERY_MEM] >> NO_TAC) >>
          TRY (gvs[wf_function_def, listTheory.EVERY_MEM] >> NO_TAC) >>
          TRY (irule lookup_block_mem_some >> simp[] >> NO_TAC) >>
          TRY (qpat_x_assum `_ = function_map_transform _ _` (fn th =>
                 REWRITE_TAC [th]) >>
               simp[function_map_transform_def, lookup_block_map, Abbr `bt`] >>
               NO_TAC) >>
          gvs[])
      (* 6. Block sim *)
      >- (rpt strip_tac >>
          `FST (ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)) =
           flips` by gvs[] >>
          `lookup_block bb.bb_label fn1.fn_blocks = SOME bb` by
            (irule lookup_block_mem_some >> simp[]) >>
          mp_tac (SIMP_RULE std_ss [LET_THM] ao_cmp_flip_block_sim) >>
          disch_then (qspecl_then [`mid`, `fn1`,
            `bb.bb_label`, `bb`, `bt bb`, `fuel`, `ctx`,
            `s1`, `s2`] mp_tac) >>
          impl_tac
          >- (gvs[] >>
              rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              TRY (gvs[listTheory.EVERY_MEM] >> NO_TAC) >>
              TRY (gvs[wf_function_def, listTheory.EVERY_MEM] >> NO_TAC) >>
              TRY (qpat_x_assum `_ = function_map_transform _ _` (fn th =>
                     REWRITE_TAC [th]) >>
                   simp[function_map_transform_def, lookup_block_map,
                        Abbr `bt`] >>
                   NO_TAC) >>
              gvs[])
          >> strip_tac >> simp[]))
  >> disch_then (qspecl_then [`fuel`, `ctx`, `s0`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (irule iszero_inv_refl_empty >> simp[Abbr `s0`])
      >> simp[Abbr `s0`])
  >> simp_tac std_ss []
QED

