Theory abiDecodeBoundsTest
Ancestors
  builtinAbi venomExecSemantics venomState context words finite_map
Libs
  wordsLib

Definition abi_decode_bounds_test_state_def:
  abi_decode_bounds_test_state = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

(* The offset previously wrapped the payload end to zero and decoded an
   empty bytestring. EVM memory-expansion failure is absent from Venom. *)
Theorem bounded_decode_wrapping_offset_reverts:
  case exec_block 1 ARB
    <| bb_label := "entry";
       bb_instructions :=
         (SND (lower_abi_decode (Lit 96w)
           (DecComplex T [(DecBytestring 1,32,64)]) 32 96 64
           abi_decode_bounds_test_state)).cs_current_insts |>
    (mstore 96 64w (mstore 128 (n2w (2 ** 256 - 160))
      (mstore 160 0w ((init_venom_state "entry") with vs_alloca_next := 256)))) of
    Abort Revert_abort _ => T
  | _ => F
Proof
  EVAL_TAC
QED

(* A bounded head read must fail before reading an unrelated memory word. *)
Theorem bounded_decode_head_past_end_reverts_before_load:
  case exec_block 1 ARB
    <| bb_label := "entry";
       bb_instructions :=
         (SND (compile_abi_decode_to_buf (Lit 256w) (Lit 640w) MLOAD (Lit 0w)
           (Lit 192w) (DecBytestring 1) abi_decode_bounds_test_state)).cs_current_insts |>
    (init_venom_state "entry") of
    Abort Revert_abort s => s.vs_inst_idx = 6
  | _ => F
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean ABI bounds regression: " ^ name)
  end) (DB.thms "abiDecodeBoundsTest");
