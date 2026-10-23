(* Bounded probes of the actual O1 driver. No general pass certificate. *)
Theory o1DriverBoundary
Ancestors
  unitTransformDefs venomPipelineDriver venomPipelineRunner
  stateEquivProps dftDefs passSimulationDefs venomPassSchedule

Theorem unit_result_rel_refl_terminal:
  ((?s. res = Halt s) \/ (?a s. res = Abort a s)) ==>
  unit_result_rel res res
Proof
  Cases_on `res` >> simp[terminates_def, unit_result_rel_def,
                         observable_equiv_refl]
QED

Theorem unit_result_rel_trans:
  unit_result_rel x y /\ unit_result_rel y z ==> unit_result_rel x z
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >>
  simp[unit_result_rel_def] >> metis_tac[observable_equiv_trans]
QED

Theorem ctx_transform_correct_refl:
  (!fuel. terminates (run_context fuel ctx s) ==>
     (?t. run_context fuel ctx s = Halt t) \/
     (?a t. run_context fuel ctx s = Abort a t)) ==>
  ctx_transform_correct ctx ctx s
Proof
  rw[ctx_transform_correct_def] >> qexists_tac `fuel` >>
  irule unit_result_rel_refl_terminal >> metis_tac[]
QED

Theorem ctx_transform_correct_trans:
  ctx_transform_correct a b s /\ ctx_transform_correct b c s ==>
  ctx_transform_correct a c s
Proof
  rw[ctx_transform_correct_def] >>
  first_x_assum drule >> strip_tac >>
  drule unit_result_rel_terminates >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[unit_result_rel_trans]
QED

Theorem checked_identity_pipeline:
  (!fuel. terminates (run_context fuel unit.cu_context s) ==>
     (?t. run_context fuel unit.cu_context s = Halt t) \/
     (?a t. run_context fuel unit.cu_context s = Abort a t)) ==>
  checked_unit_transform_correct
    (\p u. SOME <|po_unit := u; po_final_assembly := p.rpol_final_assembly|>)
    rpolicy unit s
Proof
  simp[checked_unit_transform_correct_def, ctx_transform_correct_refl]
QED

Theorem empty_stages_boundary:
  run_pipeline_stages rpolicy [] unit supply = SOME (unit,supply)
Proof
  simp[run_pipeline_stages_def, ctx_transform_correct_refl]
QED

Theorem o1_actual_stage_tags:
  pipeline_spec_tags o1_pipeline_spec =
    [VP_SimplifyCFG; VP_DretDesugar; VP_MakeSSA; VP_LowerDload;
     VP_ConcretizeMemLoc; VP_FmpLowering; VP_MakeSSA; VP_SimplifyCFG;
     VP_SingleUseExpansion; VP_DFT; VP_CFGNormalization]
Proof
  simp[pipeline_spec_tags_def, pipeline_stage_tags_def,
       o1_pipeline_spec_def, o1_fn_passes_def, fn_pass_tag_def]
QED

(* x is needed only by RETURN. DFT schedules the failing ASSERT before its
   producer; the abort states differ but the allowed result relation holds. *)
Definition probe_assert_fn_def:
  probe_assert_fn = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
       [instruction 0 ASSIGN [Lit 7w] ["x"];
        instruction 1 ASSERT [Lit 0w] [];
        instruction 2 RETURN [Var "x"; Lit 0w] []] |>]
End
Definition probe_assert_ctx_def:
  probe_assert_ctx = mk_venom_context [probe_assert_fn] (SOME "main")
End
Definition probe_assert_start_def:
  probe_assert_start = init_venom_state "entry"
End

Theorem dft_assert_schedule_probe:
  MAP (\i. i.inst_id) (HD (dft_fn probe_assert_fn).fn_blocks).bb_instructions =
    [1;0;2]
Proof
  EVAL_TAC
QED

Theorem dft_assert_abort_probe:
  run_context 5 probe_assert_ctx probe_assert_start =
    Abort Revert_abort
      (revert_state (set_returndata []
        ((update_var "x" 7w probe_assert_start) with vs_inst_idx := 1))) /\
  run_context 5 (dft_ctx probe_assert_ctx) probe_assert_start =
    Abort Revert_abort (revert_state (set_returndata [] probe_assert_start))
Proof
  EVAL_TAC
QED

Theorem dft_assert_abort_boundary:
  unit_result_rel
    (run_context 5 probe_assert_ctx probe_assert_start)
    (run_context 5 (dft_ctx probe_assert_ctx) probe_assert_start) /\
  run_context 5 probe_assert_ctx probe_assert_start <>
    run_context 5 (dft_ctx probe_assert_ctx) probe_assert_start
Proof
  simp[dft_assert_abort_probe, unit_result_rel_def] >> EVAL_TAC
QED

Theorem probe_assert_terminal_runs:
  !fuel. terminates (run_context fuel probe_assert_ctx probe_assert_start) ==>
    (?s. run_context fuel probe_assert_ctx probe_assert_start = Halt s) \/
    (?a s. run_context fuel probe_assert_ctx probe_assert_start = Abort a s)
Proof
  Cases >> EVAL_TAC >> simp[]
QED

Theorem checked_identity_assert_instance:
  checked_unit_transform_correct
    (\p u. SOME <|po_unit := u; po_final_assembly := p.rpol_final_assembly|>)
    rpolicy (unit with cu_context := probe_assert_ctx) probe_assert_start
Proof
  irule checked_identity_pipeline >> simp[probe_assert_terminal_runs]
QED

(* The initial generic identity conjecture is false for the public relation:
   terminates includes OK and IntRet, whereas unit_result_rel excludes them.
   Main-entry terminality must be proved from the entry-shape invariant. *)
Theorem nonterminal_identity_obstruction:
  terminates (OK s) /\ ~unit_result_rel (OK s) (OK s) /\
  terminates (IntRet ret s) /\ ~unit_result_rel (IntRet ret s) (IntRet ret s)
Proof
  simp[terminates_def, unit_result_rel_def]
QED

val _ = List.app (fn (name, th) =>
  if List.all (fn tag => tag = "DISK_THM")
       (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("oracle in o1DriverBoundary: " ^ name))
  (DB.thms "o1DriverBoundary");
