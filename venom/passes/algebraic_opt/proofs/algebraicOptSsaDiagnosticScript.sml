Theory algebraicOptSsaDiagnostic
Ancestors
  algebraicOptDefs algebraicOptOutputShapeProofs venomInst venomWf
  venomFnScheduleRunner irSupply passSharedDefs
Libs
  listTheory

(* These equations diagnose partial pattern matching, not a counterexample:
   ARB is a fixed unspecified constant and must not be chosen freely. *)
Theorem ao_empty_comparator:
  inst.inst_operands = [] ==>
  ao_opt_comparator dfg ra lbl idx fr inst = (ARB : instruction list)
Proof
  simp[ao_opt_comparator_def]
QED

Theorem ao_empty_gt_peephole:
  inst.inst_operands = [] /\ inst.inst_outputs <> [] /\
  inst.inst_opcode = GT ==>
  ao_peephole_inst dfg ra lbl idx fr inst = (ARB : instruction list)
Proof
  simp[ao_peephole_inst_def, ao_empty_comparator]
QED

Theorem ao_empty_gt_transform:
  inst.inst_operands = [] /\ inst.inst_outputs <> [] /\
  inst.inst_opcode = GT ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
  MAP ao_post_flip_inst (ARB : instruction list)
Proof
  strip_tac >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
  `ao_pre_flip_inst inst = inst` by simp[ao_pre_flip_inst_def] >>
  simp[ao_transform_inst_def, ao_opt_producer_def, ao_empty_gt_peephole]
QED

Definition ao_malformed_fn_def:
  ao_malformed_fn = mk_raw_function "probe"
    [<| bb_label := "entry"; bb_instructions :=
       [<| inst_id := 0; inst_opcode := GT;
           inst_operands := []; inst_outputs := ["x"] |>;
        <| inst_id := 1; inst_opcode := STOP;
           inst_operands := []; inst_outputs := [] |>] |>]
End

Definition ao_malformed_supply_def:
  ao_malformed_supply =
    <| irs_next_inst := 2; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1]; irs_used_vars := ["x"];
       irs_used_labels := ["probe";"entry"] |>
End

Theorem ao_malformed_fn_admissible:
  wf_function ao_malformed_fn /\
  ssa_form ao_malformed_fn /\
  ir_supply_covers_fn ao_malformed_supply ao_malformed_fn
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem ao_malformed_fn_exposure:
  ao_transform_inst dfg ra "entry" 0 targets fr
    (HD (fn_insts ao_malformed_fn)) =
  MAP ao_post_flip_inst (ARB : instruction list)
Proof
  irule ao_empty_gt_transform >>
  EVAL_TAC
QED

Theorem ao_arb_empty_ssa:
  (ARB : instruction list) = [] ==>
  ssa_form (FST (ao_transform_function_supply ao_malformed_supply ao_malformed_fn))
Proof
  strip_tac >>
  simp[ao_transform_function_supply_def, ao_malformed_fn_def, mk_raw_function_def,
       ao_handle_offset_inst_def, ao_transform_blocks_supply_def,
       ao_transform_block_supply_def, ao_transform_insts_supply_def,
       ao_transform_inst_def, ao_resolve_iszero_inst_def,
       ao_opt_producer_def, ao_pre_flip_inst_def, ao_peephole_inst_def,
       ao_empty_comparator] >>
  Cases_on `ao_alloc_fresh ao_malformed_supply` >> simp[] >>
  Cases_on `ao_alloc_fresh r` >>
  simp[ao_cmp_flip_function_supply_def, fn_insts_def, fn_insts_blocks_def,
       ao_cmp_flip_scan_def, is_comparator_def, ssa_form_def]
QED

Theorem ao_arb_duplicate_not_ssa:
  (ARB : instruction list) =
    [<| inst_id := 10; inst_opcode := ASSIGN;
        inst_operands := []; inst_outputs := ["x"] |>;
     <| inst_id := 11; inst_opcode := ASSIGN;
        inst_operands := []; inst_outputs := ["x"] |>] ==>
  ~ssa_form (FST (ao_transform_function_supply ao_malformed_supply ao_malformed_fn))
Proof
  strip_tac >>
  simp[ao_transform_function_supply_def, ao_malformed_fn_def, mk_raw_function_def,
       ao_handle_offset_inst_def, ao_transform_blocks_supply_def,
       ao_transform_block_supply_def, ao_transform_insts_supply_def,
       ao_transform_inst_def, ao_resolve_iszero_inst_def,
       ao_opt_producer_def, ao_pre_flip_inst_def, ao_peephole_inst_def,
       ao_empty_comparator, ao_post_flip_inst_def] >>
  Cases_on `ao_alloc_fresh ao_malformed_supply` >> simp[] >>
  Cases_on `ao_alloc_fresh r` >>
  simp[ao_cmp_flip_function_supply_def, fn_insts_def, fn_insts_blocks_def,
       ao_cmp_flip_scan_def, is_comparator_def, ssa_form_def]
QED
