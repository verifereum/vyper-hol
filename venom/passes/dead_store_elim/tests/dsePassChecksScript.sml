(* Concrete checks for Dead Store Elimination (DSE) definitions and pass execution:
   - bp_segment_from_ops uses exact iao_size (CALL max outsize stays non-fixed)
   - bp_get_read_location treats DRET/RETFMP (vyper#5297) and key-space
     SELFDESTRUCT as ml_undefined barriers
   - all_dead_stores rejects zero-size writes (ml_size = SOME 0)
   - dse_function eliminates dead stores and preserves concrete execution *)
Theory dsePassChecks
Ancestors
  deadStoreElimDefs deadStoreElimEquiv passSimulationDefs basePtrDefs
  memLocDefs venomInst venomExecSemantics venomState cfgDefs vfmTypes
  byte While combin finite_map list rich_list pred_set words

Triviality w2n_32_256[local]:
  w2n (32w:256 word) = 32
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Triviality w2n_0_256[local]:
  w2n (0w:256 word) = 0
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Triviality wta_32_is_word_to_bytes[local]:
  !w be. word_to_bytes_aux 32 (w:256 word) be = word_to_bytes w be
Proof
  simp[byteTheory.word_to_bytes_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Triviality take_word_to_bytes_32[local]:
  !w be rest.
    TAKE 32 (word_to_bytes (w:256 word) be ++ rest) = word_to_bytes w be
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32` by
    (simp[byteTheory.LENGTH_word_to_bytes] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality drop_word_to_bytes_32[local]:
  !w be. DROP 32 (word_to_bytes (w:256 word) be) = []
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32` by
    (simp[byteTheory.LENGTH_word_to_bytes] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  simp[listTheory.DROP_LENGTH_TOO_LONG]
QED

Definition dse_test_call_inst_def:
  dse_test_call_inst =
    <|inst_id := 0; inst_opcode := CALL;
      inst_operands := [Lit 100w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 64w; Lit 32w];
      inst_outputs := ["ok"]|>
End

Definition dse_test_mstore_inst_def:
  dse_test_mstore_inst =
    <|inst_id := 1; inst_opcode := MSTORE;
      inst_operands := [Lit 64w; Lit 42w];
      inst_outputs := []|>
End

Theorem call_write_location_not_fixed:
  (bp_get_write_location FEMPTY dse_test_call_inst AddrSp_Memory).ml_size = NONE /\
  ~ml_is_fixed (bp_get_write_location FEMPTY dse_test_call_inst AddrSp_Memory) /\
  (bp_get_write_location FEMPTY dse_test_mstore_inst AddrSp_Memory).ml_size = SOME 32 /\
  ml_is_fixed (bp_get_write_location FEMPTY dse_test_mstore_inst AddrSp_Memory)
Proof
  EVAL_TAC >> simp[w2n_32_256]
QED

Theorem dret_retfmp_selfdestruct_read_barriers:
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Memory = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Transient = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Memory = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Transient = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 SELFDESTRUCT [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 SELFDESTRUCT [Lit 0w] []) AddrSp_Transient = ml_undefined
Proof
  EVAL_TAC
QED

Definition dse_zero_copy_fn_def:
  dse_zero_copy_fn =
    mk_raw_function "zero_copy"
      [<|bb_label := "entry";
         bb_instructions :=
           [<|inst_id := 0; inst_opcode := CODECOPY;
              inst_operands := [Lit 0w; Lit 0w; Lit 0w]; inst_outputs := []|>;
            <|inst_id := 1; inst_opcode := STOP;
              inst_operands := []; inst_outputs := []|>]|>]
End

Theorem zero_size_write_not_dead_store:
  (bp_get_write_location FEMPTY
     (EL 0 (HD dse_zero_copy_fn.fn_blocks).bb_instructions)
     AddrSp_Memory).ml_size = SOME 0 /\
  ~all_dead_stores {0} (cfg_analyze dse_zero_copy_fn) FEMPTY FEMPTY
     AddrSp_Memory dse_zero_copy_fn
Proof
  `(bp_get_write_location FEMPTY
     (EL 0 (HD dse_zero_copy_fn.fn_blocks).bb_instructions)
     AddrSp_Memory).ml_size = SOME 0` by (EVAL_TAC >> simp[w2n_0_256]) >>
  simp[] >> strip_tac >> fs[all_dead_stores_def] >>
  qpat_x_assum `MEM bb _` mp_tac >>
  qpat_x_assum `inst_idx < _` mp_tac >>
  qpat_x_assum `(EL inst_idx _).inst_id = 0` mp_tac >>
  simp[dse_zero_copy_fn_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst_idx` >> gvs[dse_zero_copy_fn_def, mk_raw_function_def] >>
  Cases_on `n` >> gvs[]
QED

Definition dse_overwrite_fn_def:
  dse_overwrite_fn =
    mk_raw_function "overwrite"
      [<|bb_label := "entry";
         bb_instructions :=
           [<|inst_id := 0; inst_opcode := MSTORE;
              inst_operands := [Lit 0w; Lit 10w]; inst_outputs := []|>;
            <|inst_id := 1; inst_opcode := MSTORE;
              inst_operands := [Lit 0w; Lit 20w]; inst_outputs := []|>;
            <|inst_id := 2; inst_opcode := SSTORE;
              inst_operands := [Lit 0w; Lit 30w]; inst_outputs := []|>;
            <|inst_id := 3; inst_opcode := SSTORE;
              inst_operands := [Lit 0w; Lit 40w]; inst_outputs := []|>;
            <|inst_id := 4; inst_opcode := TSTORE;
              inst_operands := [Lit 0w; Lit 1w]; inst_outputs := []|>;
            <|inst_id := 5; inst_opcode := TSTORE;
              inst_operands := [Lit 0w; Lit 2w]; inst_outputs := []|>;
            <|inst_id := 6; inst_opcode := MLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["mres"]|>;
            <|inst_id := 7; inst_opcode := SLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["sres"]|>;
            <|inst_id := 8; inst_opcode := TLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["tres"]|>;
            <|inst_id := 9; inst_opcode := STOP;
              inst_operands := []; inst_outputs := []|>]|>]
End

Definition dse_overwrite_analysis_def:
  dse_overwrite_analysis sp fn =
    let insts = (HD fn.fn_blocks).bb_instructions in
    if sp = AddrSp_Memory /\
       EXISTS (\i. i.inst_id = 0 /\ i.inst_opcode = MSTORE) insts then {0:num}
    else if sp = AddrSp_Storage /\
       EXISTS (\i. i.inst_id = 2 /\ i.inst_opcode = SSTORE) insts then {2:num}
    else if sp = AddrSp_Transient /\
       EXISTS (\i. i.inst_id = 4 /\ i.inst_opcode = TSTORE) insts then {4:num}
    else {}
End

Theorem dse_overwrite_pass_and_exec:
  MAP (\i. i.inst_id)
    (HD (dse_function dse_overwrite_analysis dse_overwrite_fn).fn_blocks).bb_instructions =
    [1; 3; 5; 6; 7; 8; 9] /\
  lift_result dse_all_equiv dse_all_equiv dse_all_equiv
    (run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry"))
    (run_blocks 1 ARB (dse_function dse_overwrite_analysis dse_overwrite_fn)
       (init_venom_state "entry")) /\
  (case run_blocks 1 ARB
          (dse_function dse_overwrite_analysis dse_overwrite_fn)
          (init_venom_state "entry") of
     Halt s =>
       lookup_var "mres" s = SOME 20w /\
       lookup_var "sres" s = SOME 40w /\
       lookup_var "tres" s = SOME 2w
   | _ => F)
Proof
  `dse_function_space dse_overwrite_analysis AddrSp_Memory dse_overwrite_fn =
     clear_nops_function (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn)` by
    (simp[dse_function_space_def, dse_iterate_def] >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     simp[dse_overwrite_analysis_def, dse_overwrite_fn_def, mk_raw_function_def] >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     EVAL_TAC) >>
  qabbrev_tac `fn1 = clear_nops_function (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn)` >>
  `dse_function_space dse_overwrite_analysis AddrSp_Storage fn1 =
     clear_nops_function (dse_single_pass {2} AddrSp_Storage fn1)` by
    (simp[dse_function_space_def, dse_iterate_def, Abbr `fn1`] >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     CONV_TAC (LAND_CONV EVAL) >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     EVAL_TAC) >>
  qabbrev_tac `fn2 = clear_nops_function (dse_single_pass {2} AddrSp_Storage fn1)` >>
  `dse_function_space dse_overwrite_analysis AddrSp_Transient fn2 =
     clear_nops_function (dse_single_pass {4} AddrSp_Transient fn2)` by
    (simp[dse_function_space_def, dse_iterate_def, Abbr `fn2`, Abbr `fn1`] >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     CONV_TAC (LAND_CONV EVAL) >>
     once_rewrite_tac[WhileTheory.OWHILE_THM] >>
     EVAL_TAC) >>
  `dse_function dse_overwrite_analysis dse_overwrite_fn =
     clear_nops_function (dse_single_pass {4} AddrSp_Transient fn2)` by
    simp[dse_function_def] >>
  simp[Abbr `fn2`, Abbr `fn1`] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``clear_nops_function x``) t
    then EVAL t else raise UNCHANGED)) >>
  EVAL_TAC >>
  simp[dse_all_equiv_def, dse_equiv_def, combinTheory.UPDATE_EQ,
       wta_32_is_word_to_bytes, drop_word_to_bytes_32,
       take_word_to_bytes_32, vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED
