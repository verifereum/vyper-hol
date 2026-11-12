Theory abiEncodeSnapshotTest
Ancestors
  exprLowering compileEnv context vyperAST venomExecSemantics venomState
  venomInst words finite_map
Libs
  wordsLib

Definition abi_snapshot_test_state_def:
  abi_snapshot_test_state = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition abi_snapshot_test_args_def:
  abi_snapshot_test_args ce = compile_abi_encode_args compile_expr
    (ce with <| ce_vars := FEMPTY |+ ("x", MemLoc 0 96);
                ce_var_type := K (SOME (ArrayT (BaseT (UintT 256)) (Dynamic 2)));
                ce_struct_fields := FEMPTY |>)
    [Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "x";
     Pop (BaseT (UintT 256)) (NameTarget "x")]
    abi_snapshot_test_state
End

Definition abi_snapshot_test_builtin_def:
  abi_snapshot_test_builtin ce = compile_expr
    (ce with <| ce_vars := FEMPTY |+ ("x", MemLoc 0 96);
                ce_var_type := K (SOME (ArrayT (BaseT (UintT 256)) (Dynamic 2)));
                ce_struct_fields := FEMPTY |>)
    (BaseT (BytesT (Dynamic 160)))
    (TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
      (BaseT (BytesT (Dynamic 160)))
      [Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "x";
       Pop (BaseT (UintT 256)) (NameTarget "x")])
    abi_snapshot_test_state
End

(* abi_encode(x, x.pop()) must capture [1,2] before pop changes x to [1].
   Execute the argument prefix emitted by the full builtin dispatch. *)
Theorem abi_encode_arguments_preserve_array_before_pop:
  case exec_block 1 ARB
    <| bb_label := "entry";
       bb_instructions :=
         TAKE (LENGTH (SND (abi_snapshot_test_args ce)).cs_current_insts)
           (FLAT (MAP (\bb. bb.bb_instructions)
                   (REVERSE (SND (abi_snapshot_test_builtin ce)).cs_blocks)) ++
            (SND (abi_snapshot_test_builtin ce)).cs_current_insts) ++
         [mk_inst (SND (abi_snapshot_test_args ce)).cs_next_id STOP [] []] |>
    (mstore 0 2w (mstore 32 1w (mstore 64 2w
      ((init_venom_state "entry") with vs_alloca_next := 96)))) of
    Halt s =>
      eval_operand (HD (FST (abi_snapshot_test_args ce))) s = SOME 96w /\
      eval_operand (HD (TL (FST (abi_snapshot_test_args ce)))) s = SOME 2w /\
      mload 96 s = 2w /\ mload 128 s = 1w /\ mload 160 s = 2w /\
      mload 0 s = 1w
  | _ => F
Proof
  EVAL_TAC
QED
