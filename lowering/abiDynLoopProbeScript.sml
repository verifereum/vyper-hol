(* Finite multiblock decoder probes, not a recursive decoder theorem. *)
Theory abiDynLoopProbe
Ancestors abiSourceLayoutProbe typedKwargBufferProps venomExecSemantics
  vyperCompiler abiEncoder emitHelper
Libs wordsLib

Definition loop_probe_code_def:
  loop_probe_code =
    SND (emit_void STOP []
      (SND (compile_abi_decode_dyn_loop (Var "dst") (Var "src")
        CALLDATALOAD (Lit 0w) (DecBytestring 10) 32 64
        (Var "index") (Var "count") kwarg_probe_state)))
End

Definition loop_probe_fn_def:
  loop_probe_fn = mk_raw_function "entry"
    (REVERSE loop_probe_code.cs_blocks ++
      [<| bb_label := loop_probe_code.cs_current_bb;
          bb_instructions := loop_probe_code.cs_current_insts |>])
End

Definition loop_probe_ctx_def:
  loop_probe_ctx = mk_venom_context [loop_probe_fn] (SOME "entry")
End

Definition loop_probe_input_def:
  loop_probe_input n bs =
    update_var "dst" 256w (update_var "src" 68w
      (update_var "index" 512w (update_var "count" (n2w n)
        (mstore 768 99w (mstore 256 (n2w n) (mstore 512 0w
          ((init_venom_state "entry") with vs_call_ctx :=
            (empty_call_context with cc_calldata := REPLICATE 68 0w ++ bs))))))))
End

Theorem loop_probe_zero:
  case run_blocks 4 loop_probe_ctx loop_probe_fn
    (loop_probe_input 0 (probe_word 0)) of
    Halt ss => ss.vs_current_bb = "@dec_dyn_exit_2" /\
      mload 512 ss = 0w /\ mload 256 ss = 0w
  | _ => F
Proof
  EVAL_TAC
QED

Definition loop_probe_two_bytes_def:
  loop_probe_two_bytes = probe_word 2 ++ probe_word 64 ++ probe_word 96 ++
    probe_word 0 ++ probe_word 2 ++ [42w;43w] ++ REPLICATE 30 0w
End

Theorem loop_probe_two:
  case run_blocks 8 loop_probe_ctx loop_probe_fn
    (loop_probe_input 2 loop_probe_two_bytes) of
    Halt ss => ss.vs_current_bb = "@dec_dyn_exit_2" /\
      mload 512 ss = 2w /\
      val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
        (ArrayV (DynArrayV [BytesV [];BytesV [42w;43w]])) 256 ss.vs_memory /\
      lookup_var "dst" ss = SOME 256w /\
      lookup_var "src" ss = SOME 68w /\
      lookup_var "index" ss = SOME 512w /\
      lookup_var "count" ss = SOME 2w /\
      ss.vs_call_ctx = (loop_probe_input 2 loop_probe_two_bytes).vs_call_ctx
  | _ => F
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

(* Finite prefix runner preserving the actual execution result. *)
Definition loop_probe_prefix_def:
  loop_probe_prefix 0 ss = OK ss /\
  loop_probe_prefix (SUC n) ss =
    case lookup_block ss.vs_current_bb loop_probe_fn.fn_blocks of
      NONE => Error "missing probe block"
    | SOME bb => case run_block 0 loop_probe_ctx bb ss of
        OK next => loop_probe_prefix n next
      | other => other
End
Definition loop_probe_header_inv_def:
  loop_probe_header_inv i ss <=>
    i <= 2 /\ ss.vs_current_bb = "@dec_dyn_hdr_0" /\
    mload 512 ss = n2w i /\ mload 256 ss = 2w /\
    kwarg_array_prefix (BaseTV (BytesT (Dynamic 10)))
      [BytesV [];BytesV [42w;43w]] 288 i ss.vs_memory /\
    lookup_var "dst" ss = SOME 256w /\
    lookup_var "src" ss = SOME 68w /\
    lookup_var "index" ss = SOME 512w /\
    lookup_var "count" ss = SOME 2w /\
    mload 768 ss = 99w /\
    ss.vs_call_ctx = (loop_probe_input 2 loop_probe_two_bytes).vs_call_ctx
End

Theorem loop_probe_header_zero:
  case loop_probe_prefix 1 (loop_probe_input 2 loop_probe_two_bytes) of
    OK ss => loop_probe_header_inv 0 ss
  | _ => F
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

Theorem loop_probe_header_one:
  case loop_probe_prefix 3 (loop_probe_input 2 loop_probe_two_bytes) of
    OK ss => loop_probe_header_inv 1 ss
  | _ => F
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

Theorem loop_probe_header_two:
  case loop_probe_prefix 5 (loop_probe_input 2 loop_probe_two_bytes) of
    OK ss => loop_probe_header_inv 2 ss
  | _ => F
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

(* Each prefix follows labels from the actual machine state. This nested
   probe checks all three boundaries in one execution, without rerunning
   earlier blocks to reconstruct each projected memory field. *)
Theorem loop_probe_header_transitions:
  case loop_probe_prefix 1 (loop_probe_input 2 loop_probe_two_bytes) of
    OK h0 => loop_probe_header_inv 0 h0 /\
      (case loop_probe_prefix 2 h0 of
        OK h1 => loop_probe_header_inv 1 h1 /\
          (case loop_probe_prefix 2 h1 of
            OK h2 => loop_probe_header_inv 2 h2 /\
              (case loop_probe_prefix 1 h2 of
                OK ex => ex.vs_current_bb = "@dec_dyn_exit_2" /\
                  mload 512 ex = 2w /\ mload 768 ex = 99w /\
                  val_in_memory
                    (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
                    (ArrayV (DynArrayV [BytesV [];BytesV [42w;43w]]))
                    256 ex.vs_memory
              | _ => F)
          | _ => F)
      | _ => F)
  | _ => F
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``loop_probe_header_inv``]) >>
  rpt conj_tac >> EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

(* Generic header-step contract still needed: with i < count, a coherent
   source encoding and decoder layout, available generated blocks and fresh
   temporaries, executing header then the child's (possibly multiblock)
   decoder returns to hdr with prefix i+1. The live dst/src/index operands
   must survive all child instructions; the count must be reloaded from
   unchanged calldata, not assumed invariant merely because cnt is live.
   Prove scratch/destination separation, child-copy framing, available-block
   preservation and label freshness before lifting to nested-loop induction.
   loop_probe_header_inv is validated above only at the concrete boundaries;
   it is not a general recursive-decoder preservation theorem. *)

val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in abiDynLoopProbe: " ^ name))
  (DB.thms "abiDynLoopProbe");
