(* Phase 5: OR-truthy rewrite correctness — function-level lift.
 *
 * Uses block_sim_function_with_pred2_bb to lift ao_or_truthy_block_sim /
 * ao_or_truthy_block_ok_inv to run_blocks via the framework's fuel induction.
 *
 * TOP-LEVEL: ao_phase5_correct
 *)

Theory aoPhase5Proof
Ancestors
  algebraicOptDefs aoOrTruthySim
  venomExecSemantics venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_or_truthy_dead_vars_def",
                  "ao_or_truthy_scan_def",
                  "ao_or_truthy_apply_inst_def"]

(* ao_or_truthy_function is the identity when the scan finds nothing. *)
Triviality or_truthy_null_id[local]:
  !fn.
    NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) ==>
    ao_or_truthy_function (dfg_build_function fn) fn = fn
Proof
  rpt strip_tac >> simp[ao_or_truthy_function_def, LET_THM]
QED

(* When non-NULL, ao_or_truthy_function is a function_map_transform. *)
Triviality or_truthy_is_map_transform[local]:
  !fn.
    ~NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) ==>
    ao_or_truthy_function (dfg_build_function fn) fn =
    function_map_transform
      (\bb. bb with bb_instructions :=
        MAP (ao_or_truthy_apply_inst
               (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))
            bb.bb_instructions)
      fn
Proof
  rpt strip_tac >>
  simp[ao_or_truthy_function_def, function_map_transform_def, LET_THM]
QED

(* or_truthy_inv is reflexive when no vars are defined. *)
Triviality or_truthy_inv_refl_empty[local]:
  !ids insts s. FDOM s.vs_vars = {} ==> or_truthy_inv ids insts s s
Proof
  rw[or_truthy_inv_def] >> gvs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* ===== Main theorem ===== *)

Theorem ao_phase5_correct:
  !fuel ctx fn1 s.
    let dfg1 = dfg_build_function fn1 in
    let dead = ao_or_truthy_dead_vars dfg1 fn1 in
    ssa_form fn1 /\ fn_inst_ids_distinct fn1 /\
    FDOM s.vs_vars = {} ==>
    (?e. run_blocks fuel ctx fn1 s = Error e) \/
    lift_result (state_equiv dead) (execution_equiv dead) (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_or_truthy_function dfg1 fn1) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  Cases_on `NULL (ao_or_truthy_scan (dfg_build_function fn1) (fn_insts fn1))`
  >- (`ao_or_truthy_function (dfg_build_function fn1) fn1 = fn1` by
        (irule or_truthy_null_id >> first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[] >> DISJ2_TAC >>
      irule lift_result_refl >>
      simp_tac std_ss [state_equiv_refl, execution_equiv_refl])
  >> ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel] >>
  qabbrev_tac `bt = \bb:basic_block. bb with bb_instructions :=
    MAP (ao_or_truthy_apply_inst
           (ao_or_truthy_scan (dfg_build_function fn1) (fn_insts fn1)))
        bb.bb_instructions` >>
  `ao_or_truthy_function (dfg_build_function fn1) fn1 =
   function_map_transform bt fn1` by
    (simp_tac std_ss [Abbr `bt`] >> irule or_truthy_is_map_transform >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  qabbrev_tac `s0 = s with vs_inst_idx := 0` >>
  qspecl_then
    [`or_truthy_inv (ao_or_truthy_scan (dfg_build_function fn1) (fn_insts fn1))
                    (fn_insts fn1)`,
     `state_equiv (ao_or_truthy_dead_vars (dfg_build_function fn1) fn1)`,
     `execution_equiv (ao_or_truthy_dead_vars (dfg_build_function fn1) fn1)`,
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
          qspecl_then [`fn1`, `bb`, `bt bb`, `fuel`, `ctx`,
            `s1`, `s2`, `s1'`, `s2'`] mp_tac ao_or_truthy_block_ok_inv >>
          impl_tac >- simp[Abbr `bt`] >> simp[])
      (* 6. Block sim *)
      >- (rpt strip_tac >>
          qspecl_then [`fn1`, `bb`, `bt bb`, `fuel`, `ctx`, `s1`, `s2`]
            mp_tac ao_or_truthy_block_sim >>
          impl_tac >- simp[Abbr `bt`] >> simp[]))
  >> disch_then (qspecl_then [`fuel`, `ctx`, `s0`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (irule or_truthy_inv_refl_empty >> simp[Abbr `s0`])
      >> simp[Abbr `s0`])
  >> simp_tac std_ss []
QED

val _ = export_theory();
