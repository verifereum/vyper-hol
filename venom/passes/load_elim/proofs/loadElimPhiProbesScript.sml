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

Definition singleton_probe_ctx_def:
  singleton_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function singleton_probe_fn) storage_config
End

Theorem singleton_analysis_probe:
  load_elim_inst singleton_probe_ctx []
    (df_at NONE (load_analyze singleton_probe_ctx singleton_probe_fn) "e" 1)
    (probe_inst 1 SLOAD [Lit 0w] ["y"]) =
  mk_assign_inst (probe_inst 1 SLOAD [Lit 0w] ["y"]) (Var "x")
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Definition diamond_probe_fn_def:
  diamond_probe_fn = mk_raw_function "diamond"
    [<| bb_label := "e"; bb_instructions :=
         [probe_inst 0 JNZ [Lit 1w; Label "l"; Label "r"] []] |>;
     <| bb_label := "l"; bb_instructions :=
         [probe_inst 1 SLOAD [Lit 0w] ["x"];
          probe_inst 2 JMP [Label "j"] []] |>;
     <| bb_label := "r"; bb_instructions :=
         [probe_inst 3 SLOAD [Lit 0w] ["y"];
          probe_inst 4 JMP [Label "j"] []] |>;
     <| bb_label := "j"; bb_instructions :=
         [probe_inst 5 JMP [Label "s"] []] |>;
     <| bb_label := "s"; bb_instructions :=
         [probe_inst 6 SLOAD [Lit 0w] ["z"];
          probe_inst 7 STOP [] []] |>]
End

Definition diamond_probe_ctx_def:
  diamond_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function diamond_probe_fn) storage_config
End

Theorem diamond_probe_wf:
  wf_function diamond_probe_fn /\ fn_inst_wf diamond_probe_fn /\
  wf_ssa diamond_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       diamond_probe_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem diamond_cfg_probe:
  cfg_analyze diamond_probe_fn =
    <| cfg_succs := FEMPTY |++ [("e",["r";"l"]); ("l",["j"]);
         ("r",["j"]); ("j",["s"]); ("s",[])];
       cfg_preds := FEMPTY |++ [("e",[]); ("l",["e"]); ("r",["e"]);
         ("j",["l";"r"]); ("s",["j"])];
       cfg_reachable := FEMPTY |++ [("e",T);("l",T);("r",T);("j",T);("s",T)];
       cfg_dfs_post := ["s";"j";"r";"l";"e"];
       cfg_dfs_pre := ["e";"r";"j";"s";"l"] |>
Proof
  EVAL_TAC >> simp[fmap_EXT, FLOOKUP_DEF, FUN_EQ_THM] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[SF DISJ_ss, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

