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
