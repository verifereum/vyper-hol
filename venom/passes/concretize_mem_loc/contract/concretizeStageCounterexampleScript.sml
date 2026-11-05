(* Concrete forced-placement diagnostic, evaluated through the production pass. *)
Theory concretizeStageCounterexample
Ancestors
  concretizeMemLocDefs venomPassDispatcher venomExecSemantics
Libs wordsLib



Definition overlap_fn_def:
  overlap_fn = (mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
       mk_inst 2 ALLOCA [Lit 32w] ["q"];
       mk_inst 3 MSTORE [Var "p"; Lit 1w] [];
       mk_inst 4 MSTORE [Var "q"; Lit 2w] [];
       mk_inst 5 MLOAD [Var "p"] ["x"];
       mk_inst 6 SSTORE [Lit 0w; Var "x"] [];
       mk_inst 7 STOP [] []] |>]) with
     fn_forced_alloc_positions := FEMPTY |+ (1,0) |+ (2,0)
End

Definition overlap_ctx_def:
  overlap_ctx = mk_venom_context [overlap_fn] (SOME "main")
End

Definition overlap_target_fn_def:
  overlap_target_fn = THE (concretize_function_fuel_in_context
    (concretize_memloc_fuel overlap_fn) overlap_ctx [] overlap_fn)
End

Theorem overlap_layout:
  OPTION_MAP (\f. MAP (\i. (i.inst_opcode,i.inst_operands))
    (HD f.fn_blocks).bb_instructions)
    (concretize_function_fuel_in_context (concretize_memloc_fuel overlap_fn)
      overlap_ctx [] overlap_fn) =
  SOME [(ASSIGN,[Lit (0w:256 word)]); (ASSIGN,[Lit 0w]);
    (MSTORE,[Var "p"; Lit 1w]); (MSTORE,[Var "q"; Lit 2w]);
    (MLOAD,[Var "p"]); (SSTORE,[Lit 0w; Var "x"]); (STOP,[])]
Proof
  EVAL_TAC
QED

Definition overlap_target_ctx_def:
  overlap_target_ctx = mk_venom_context [overlap_target_fn] (SOME "main")
End

Definition overlap_storage_result_def:
  overlap_storage_result result =
    case result of Halt s => SOME (sload 0w s) | _ => NONE
End

Theorem overlap_last_byte[local]:
  set_byte (31w:256 word) (1w:8 word) (0w:256 word) T = 1w /\
  set_byte (31w:256 word) (2w:8 word) (0w:256 word) T = 2w
Proof
  conj_tac >> simp[byteTheory.set_byte_def, byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  rewrite_tac[byteTheory.word_slice_alt_def] >> CONV_TAC WORD_EVAL_CONV
QED

Theorem overlap_zero_byte[local]:
  !k n. w2n (k:256 word) < 31 /\ n < 8 ==>
    set_byte k (0w:8 word) ((n2w (2 ** n)):256 word) T = n2w (2 ** n)
Proof
  rpt strip_tac >>
  simp[byteTheory.set_byte_def, byteTheory.byte_index_def,
       byteTheory.word_slice_alt_zero] >>
  rw_tac (std_ss ++ fcpLib.FCP_ss)
    [byteTheory.word_slice_alt_def, wordsTheory.WORD_EQ,
     wordsTheory.word_or_def, wordsTheory.word_index,
     bitTheory.BIT_TWO_POW] >> decide_tac
QED

Theorem overlap_runs:
  overlap_storage_result
    (run_context 10 overlap_ctx (init_venom_state "main")) = SOME 1w /\
  overlap_storage_result
    (run_context 10 overlap_target_ctx (init_venom_state "main")) = SOME 2w
Proof
  EVAL_TAC >>
  simp[overlap_last_byte,
    Q.SPECL [`k`,`0`] overlap_zero_byte,
    Q.SPECL [`k`,`1`] overlap_zero_byte]
QED
