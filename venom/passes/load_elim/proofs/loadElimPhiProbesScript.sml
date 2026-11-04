Theory loadElimPhiProbes
Ancestors
  loadElimDefs venomExecSemantics venomState venomWf venomInst finite_map

Definition probe_inst_def:
  probe_inst id op ops outs =
    <| inst_id := id; inst_opcode := op; inst_operands := ops;
       inst_outputs := outs |>
End

Definition singleton_probe_fn_def:
  singleton_probe_fn = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions :=
          [probe_inst 0 SLOAD [Lit 0w] ["x"];
           probe_inst 1 SLOAD [Lit 0w] ["y"];
           probe_inst 2 STOP [] []] |>]
End

Theorem singleton_probe_wf:
  wf_function singleton_probe_fn /\ fn_inst_wf singleton_probe_fn /\
  wf_ssa singleton_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       singleton_probe_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem singleton_transfer_probe:
  !ctx. ctx.lctx_config = storage_config ==>
    load_transfer ctx (probe_inst 0 SLOAD [Lit 0w] ["x"]) NONE =
    SOME (FEMPTY |+
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg [])
        (probe_inst 0 SLOAD [Lit 0w] ["x"]), [Var "x"]))
Proof
  simp[load_transfer_def, storage_config_def, probe_inst_def,
       unwrap_load_lattice_def]
QED
