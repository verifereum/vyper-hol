Theory o1MakeSsaStepCounterexample
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassDispatcher unitShapeDefs venomInst dretDesugarDefs

Definition row_boundary_fn_def:
  row_boundary_fn = mk_raw_function "main"
    [<| bb_label := "main";
        bb_instructions := [mk_inst 0 ALLOCA [Lit 32w] ["p"];
                            mk_inst 1 STOP [] []] |>]
End

Definition row_boundary_unit_def:
  row_boundary_unit =
    <| cu_context := mk_venom_context [row_boundary_fn] (SOME "main");
       cu_data_segment := [] |>
End

Definition row_boundary_supply_def:
  row_boundary_supply = init_ir_supply row_boundary_unit
End

Theorem row_boundary_eval:
  make_ssa_current_fn row_boundary_supply row_boundary_fn =
    (row_boundary_fn, row_boundary_supply)
Proof
  EVAL_TAC
QED

Definition row_boundary_out_def:
  row_boundary_out = <| fpo_function := row_boundary_fn;
    fpo_label_map := []; fpo_supply := row_boundary_supply |>
End

Theorem row_boundary_step:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA)
    row_boundary_unit row_boundary_supply row_boundary_fn row_boundary_out
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_make_ssa,
       row_boundary_eval, row_boundary_out_def] >> EVAL_TAC
QED

Theorem row_boundary_shape:
  o1_ctx_shape row_boundary_unit.cu_context
Proof
  `reachable_fn row_boundary_fn = row_boundary_fn` by
    (irule reachable_fn_single_block >>
     simp[row_boundary_fn_def, mk_raw_function_def, mk_inst_def]) >>
  `!x. ~retpc_var row_boundary_fn x` by
    (simp[retpc_var_def] >> irule copy_phi_var_no_seed >> EVAL_TAC >> rw[] >> simp[]) >>
  `!x. ~gas_var row_boundary_fn x` by
    (simp[gas_var_def] >> irule copy_phi_var_no_seed >> EVAL_TAC >> rw[] >> simp[]) >>
  `call_checks_ok row_boundary_fn` by
    (irule call_checks_ok_no_calls >> EVAL_TAC) >>
  simp[o1_ctx_shape_def, row_boundary_unit_def, mk_venom_context_def,
       o1_fn_shape_def, fn_shape_ok_def, opaque_use_ok_def,
       retpc_shape_ok_def] >>
  simp[row_boundary_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, fn_invoke_ok_def, fn_label_refs_ok_def,
       no_dret_def, DISJ_IMP_THM, FORALL_AND_THM, mk_inst_def] >>
  EVAL_TAC >> rw[] >> gvs[] >>
  Cases_on `inst = mk_inst 0 ALLOCA [Lit 32w] ["p"]` >-
    gvs[mk_inst_def] >>
  Cases_on `inst = mk_inst 1 STOP [] []` >> gvs[mk_inst_def]
QED

Theorem row_boundary_rows:
  ir_supply_inst_ok row_boundary_supply /\
  o1_fn_row 2 row_boundary_fn /\
  ~o1_fn_row 3 row_boundary_out.fpo_function
Proof
  EVAL_TAC
QED
