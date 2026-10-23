Theory eventBoundaryProbe
Ancestors vyperCompiler stmtLowering abiEncoder valueEncoding vyperEvent venomExecSemantics vyperTyping
Libs wordsLib

(* Diagnostics only: no general compiler simulation is claimed. *)
Theorem topic_word_distinction:
  event_topic_word (BaseT (BytesT (Fixed 20)))
    (BytesV (1w :: REPLICATE 19 0w)) = 1w << 248 /\
  event_topic_word (BaseT AddressT)
    (BytesV (1w :: REPLICATE 19 0w)) = 1w << 152
Proof
  EVAL_TAC >> simp[]
QED

Definition probe_encode_def:
  probe_encode info =
    compile_abi_encode_to_buf (Lit 1024w) (Lit 256w) info
      (initial_compile_state "entry")
End

(* Word topics emit no instructions and retain the already typed word. *)
Theorem topic_word_identity:
  compile_encode_log_topic (Lit (1w << 248)) F
    (initial_compile_state "entry") =
  (Lit (1w << 248), initial_compile_state "entry")
Proof
  EVAL_TAC >> simp[]
QED

(* A concrete dynamic bytestring has a three-instruction topic program. *)
Theorem bytestring_topic_shape:
  LENGTH (SND (compile_encode_log_topic (Lit 256w) T
    (initial_compile_state "entry"))).cs_current_insts = 3
Proof
  EVAL_TAC >> simp[]
QED

Theorem dynamic_static_blocks:
  LENGTH (SND (probe_encode
    (AbiDynArray AbiPrimWord 32 32 F))).cs_blocks = 3
Proof
  EVAL_TAC >> simp[]
QED

Theorem dynamic_dynamic_blocks:
  LENGTH (SND (probe_encode
    (AbiDynArray (AbiBytestring 5) 32 64 T))).cs_blocks = 3
Proof
  EVAL_TAC >> simp[]
QED

Theorem nested_dynamic_blocks:
  LENGTH (SND (probe_encode
    (AbiDynArray (AbiDynArray AbiPrimWord 32 32 F) 32 96 T))).cs_blocks = 6
Proof
  EVAL_TAC >> simp[]
QED

(* Close the open continuation with STOP, but run the actual generated CFG. *)
Definition probe_context_def:
  probe_context info =
    FST (extract_context "entry"
      (SND (emit_void STOP [] (SND (probe_encode info)))))
End

Definition probe_run_def:
  probe_run info ss =
    let ctx = probe_context info in
    run_function 1000 ctx (HD ctx.ctx_functions) ss
End

Definition probe_input_def:
  probe_input =
    (mstore 288 7w (mstore 256 1w (init_venom_state "entry")))
      with vs_alloca_next := 0
End

Theorem dynamic_word_trace:
  case probe_run (AbiDynArray AbiPrimWord 32 32 F) probe_input of
    Halt ss => mload 1024 ss = 1w /\ mload 1056 ss = 7w
  | _ => F
Proof
  EVAL_TAC >> simp[]
QED

Definition probe_nested_input_def:
  probe_nested_input payload =
    (mstore 320 payload (mstore 288 1w
      (mstore 256 1w (init_venom_state "entry"))))
      with vs_alloca_next := 0
End

Theorem nested_dynamic_trace:
  case probe_run
    (AbiDynArray (AbiDynArray AbiPrimWord 32 32 F) 32 96 T)
    (probe_nested_input 7w) of
    Halt ss => mload 1024 ss = 1w /\ mload 1056 ss = 32w /\
      mload 1088 ss = 1w /\ mload 1120 ss = 7w /\
      mload 256 ss = 1w /\ mload 288 ss = 1w /\ mload 320 ss = 7w
  | _ => F
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_function``]) >>
  EVAL_TAC
QED

Theorem dynamic_bytestring_trace:
  case probe_run
    (AbiDynArray (AbiBytestring 5) 32 64 T)
    ((probe_nested_input (1w << 248)) with vs_alloca_next := 0) of
    Halt ss => mload 1024 ss = 1w /\ mload 1056 ss = 32w /\
      mload 1088 ss = 1w /\ mload 1120 ss = 1w << 248 /\
      mload 320 ss = 1w << 248
  | _ => F
Proof
  EVAL_TAC >> simp[]
QED

(* SSA pointer survival alone is insufficient: aliasing mutates its payload. *)
Theorem pointer_survival_not_payload_survival:
  let ss = update_var "p" 256w (mstore 256 7w (init_venom_state "entry")) in
  eval_operand (Var "p") (mstore 256 9w ss) = SOME 256w /\
  mload 256 ss = 7w /\ mload 256 (mstore 256 9w ss) = 9w
Proof
  EVAL_TAC >> simp[]
QED

Definition probe_args_def:
  probe_args cenv = compile_log_eval_all
    (cenv with ce_vars := FEMPTY |+ ("a", MemLoc 256 32) |+
      ("b", MemLoc 288 32))
    [Name (BaseT (BytesT (Fixed 20))) "a";
     Name (BaseT AddressT) "b"] (initial_compile_state "entry")
End

Theorem args_ast_order:
  !cenv.
    FST (probe_args cenv) =
      [(Var "%0", BaseT (BytesT (Fixed 20)));
       (Var "%1", BaseT AddressT)] /\
    MAP (\i. i.inst_operands) (SND (probe_args cenv)).cs_current_insts =
      [[Lit 256w]; [Lit 288w]]
Proof
  EVAL_TAC >> simp[]
QED

Theorem storage_word_no_realignment:
  !cenv.
    FST (unwrap_value cenv
      (LocatedValue (BaseT (BytesT (Fixed 20)))
        (mk_ptr (Lit 9w) LocStorage)) (initial_compile_state "entry")) =
      Var "%0" /\
    MAP (\i. i.inst_opcode) (SND (unwrap_value cenv
      (LocatedValue (BaseT (BytesT (Fixed 20)))
        (mk_ptr (Lit 9w) LocStorage)) (initial_compile_state "entry"))).cs_current_insts =
      [SLOAD]
Proof
  EVAL_TAC >> simp[]
QED

(* Candidate boundary: tv is produced by evaluate_type, not guessed from v.
   The consumer must separately carry evaluate_type tenv ty = SOME tv and
   type_memory_bytes cenv ty = type_memory_size tv. *)
Definition probe_operand_rep_def:
  probe_operand_rep ty tv v op ss <=>
    value_has_type tv v /\
    ?w. eval_operand op ss = SOME w /\
      if is_word_type ty then w = typed_val_to_w256 tv v
      else w2n w + type_memory_size tv <= 2 ** 256 /\
        val_in_memory tv v (w2n w) ss.vs_memory
End

Definition probe_read_frame_def:
  probe_read_frame regions ops ss ss' <=>
    EVERY (\(off,sz). read_memory off sz ss' = read_memory off sz ss) regions /\
    EVERY (\op. eval_operand op ss' = eval_operand op ss) ops
End

Theorem candidate_bytes20_rep:
  probe_operand_rep (BaseT (BytesT (Fixed 20)))
    (BaseTV (BytesT (Fixed 20))) (BytesV (1w :: REPLICATE 19 0w))
    (Lit (1w << 248)) (init_venom_state "entry")
Proof
  simp[probe_operand_rep_def, value_has_type_def, compileEnvTheory.is_word_type_def,
    venomStateTheory.eval_operand_def, typed_val_to_w256_def] >> EVAL_TAC
QED

Theorem candidate_address_rep:
  probe_operand_rep (BaseT AddressT) (BaseTV AddressT)
    (BytesV (1w :: REPLICATE 19 0w))
    (Lit (1w << 152)) (init_venom_state "entry")
Proof
  simp[probe_operand_rep_def, value_has_type_def, compileEnvTheory.is_word_type_def,
    venomStateTheory.eval_operand_def, typed_val_to_w256_def] >> EVAL_TAC
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("oracle in event boundary probe: " ^ name))
  (DB.thms "eventBoundaryProbe")
