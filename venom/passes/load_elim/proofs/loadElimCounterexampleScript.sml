Theory loadElimCounterexample
Ancestors
  loadElimDefs venomExecSemantics venomState venomInst loadElimByteHelpers

Definition ce_bb_def:
  ce_bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 MLOAD [Lit 0w] ["x"];
     mk_inst 1 MSTORE [Lit 0w; Var "x"] [];
     mk_inst 2 MEMTOP [] ["y"];
     mk_inst 3 STOP [] []] |>
End

Definition ce_fn_def:
  ce_fn = mk_raw_function "ce" [ce_bb]
End

Definition ce_s_def:
  ce_s = init_venom_state "entry"
End

Definition ce_ctx_def:
  ce_ctx = mk_venom_context [] NONE
End

Definition ce_target_def:
  ce_target = mk_raw_function "ce"
    [ce_bb with bb_instructions :=
      [mk_inst 0 MLOAD [Lit 0w] ["x"];
       mk_inst 2 MEMTOP [] ["y"];
       mk_inst 3 STOP [] []]]
End

Definition ce_cfg_def:
  ce_cfg = cfg_analyze ce_fn
End

Theorem ce_cfg_compute:
  ce_cfg = <| cfg_succs := FEMPTY |+ ("entry", []);
              cfg_preds := FEMPTY |+ ("entry", []);
              cfg_dfs_pre := ["entry"];
              cfg_dfs_post := ["entry"];
              cfg_reachable := FEMPTY |+ ("entry", T) |>
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED
Theorem ce_source_run:
  run_blocks 2 ce_ctx ce_fn ce_s =
    Halt (ce_s with <| vs_vars := FEMPTY |+ ("x",0w) |+ ("y",32w);
                       vs_memory := REPLICATE 32 0w;
                       vs_inst_idx := 3; vs_halted := T |>)
Proof
  EVAL_TAC >>
  simp[wordsTheory.w2n_n2w, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  rewrite_tac[GSYM (EVAL ``REPLICATE 32 (0w:8 word)``)] >>
  simp[word_of_bytes_zero_256, word_to_bytes_aux_zero,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem ce_target_run:
  run_blocks 2 ce_ctx ce_target ce_s =
    Halt (ce_s with <| vs_vars := FEMPTY |+ ("x",0w) |+ ("y",0w);
                       vs_inst_idx := 2; vs_halted := T |>)
Proof
  EVAL_TAC >>
  simp[wordsTheory.w2n_n2w, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  rewrite_tac[GSYM (EVAL ``REPLICATE 32 (0w:8 word)``)] >>
  simp[word_of_bytes_zero_256, word_to_bytes_aux_zero,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem ce_bp_compute:
  bp_analyze ce_cfg ce_fn = FEMPTY
Proof
  EVAL_TAC
QED

Definition ce_dfg_def:
  ce_dfg = <| dfg_uses := FEMPTY |+ ("x", [mk_inst 1 MSTORE [Lit 0w; Var "x"] []]);
    dfg_defs := FEMPTY |+ ("x", mk_inst 0 MLOAD [Lit 0w] ["x"])
                       |+ ("y", mk_inst 2 MEMTOP [] ["y"]);
    dfg_ids := FEMPTY |+ (0, mk_inst 0 MLOAD [Lit 0w] ["x"])
                     |+ (1, mk_inst 1 MSTORE [Lit 0w; Var "x"] [])
                     |+ (2, mk_inst 2 MEMTOP [] ["y"])
                     |+ (3, mk_inst 3 STOP [] []) |>
End

Theorem ce_dfg_compute:
  dfg_build_function ce_fn = ce_dfg
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_COMMUTES]
QED

Definition ce_loc_def:
  ce_loc = <| ml_offset := SOME 0; ml_size := SOME 32;
              ml_alloca := NONE; ml_volatile := F |>
End

Theorem ce_mem_alias_compute:
  memory_alias_analyze FEMPTY ce_fn = FEMPTY |+ (ce_loc, [ce_loc; ce_loc; ce_loc])
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_other_alias_compute:
  storage_alias_analyze FEMPTY ce_fn = FEMPTY /\
  transient_alias_analyze FEMPTY ce_fn = FEMPTY
Proof
  EVAL_TAC
QED

Definition ce_mem_ctx_def:
  ce_mem_ctx = mk_load_context FEMPTY
    (FEMPTY |+ (ce_loc, [ce_loc; ce_loc; ce_loc])) ce_dfg memory_config
End

Definition ce_known_def:
  ce_known = SOME (FEMPTY |+ (LK_Loc ce_loc, [Var "x"]))
End

Definition ce_mem_result_def:
  ce_mem_result = <|
    ds_inst := FEMPTY |+ (("entry",0), SOME FEMPTY)
                     |+ (("entry",1), ce_known)
                     |+ (("entry",2), ce_known)
                     |+ (("entry",3), ce_known)
                     |+ (("entry",4), ce_known);
    ds_boundary := FEMPTY |+ ("entry",SOME FEMPTY) |>
End

Theorem ce_mem_analyze:
  load_analyze ce_mem_ctx ce_fn = ce_mem_result
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem ce_mem_actions:
  collect_phi_actions 3 ce_mem_ctx ce_cfg ce_mem_result ce_fn = []
Proof
  EVAL_TAC
QED

Definition ce_fn1_def:
  ce_fn1 = mk_raw_function "ce"
    [ce_bb with bb_instructions :=
      [mk_inst 0 MLOAD [Lit 0w] ["x"];
       mk_inst 1 NOP [] [];
       mk_inst 2 MEMTOP [] ["y"];
       mk_inst 3 STOP [] []]]
End

Theorem ce_mem_round:
  load_elim_one ce_mem_ctx ce_cfg ce_fn = ce_fn1
Proof
  simp[load_elim_one_def, ce_mem_analyze] >>
  `fn_max_inst_id ce_fn = 3` by EVAL_TAC >>
  simp[ce_mem_actions] >>
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC
QED

Theorem ce_transient_round:
  load_elim_one
    (mk_load_context FEMPTY FEMPTY (dfg_build_function ce_fn1) transient_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_storage_round:
  load_elim_one
    (mk_load_context FEMPTY FEMPTY (dfg_build_function ce_fn1) storage_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_dload_round:
  load_elim_one
    (mk_load_context FEMPTY (FEMPTY |+ (ce_loc,[ce_loc;ce_loc;ce_loc]))
      (dfg_build_function ce_fn1) dload_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_calldata_round:
  load_elim_one
    (mk_load_context FEMPTY (FEMPTY |+ (ce_loc,[ce_loc;ce_loc;ce_loc]))
      (dfg_build_function ce_fn1) calldataload_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_clear_nops:
  clear_nops_function ce_fn1 = ce_target
Proof
  EVAL_TAC
QED

Theorem ce_transform:
  load_elim_function ce_fn = ce_target
Proof
  simp[load_elim_function_def, GSYM ce_cfg_def,
       ce_bp_compute, ce_mem_alias_compute, ce_other_alias_compute,
       ce_dfg_compute, GSYM ce_mem_ctx_def, ce_mem_round,
       ce_transient_round, ce_storage_round, ce_dload_round,
       ce_calldata_round, ce_clear_nops]
QED
