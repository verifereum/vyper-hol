(* Copy-range boundary and actual bytes-decoder execution probes. *)
Theory kwargCopyFrameProps
Ancestors typedKwargBufferProps venomMemProps valueEncodingProps
  abiEncoder venomExecSemantics context emitHelper venomState
  valueEncoding compileEnv localPtrsProps finite_map words list
Libs wordsLib

Theorem copy_keeps_val_in_memory:
  val_in_memory ty v off ss.vs_memory /\ val_wf ty v /\
  off + type_memory_size ty <= LENGTH ss.vs_memory /\
  (off + type_memory_size ty <= dst \/ dst + LENGTH bs <= off) ==>
  val_in_memory ty v off
    (write_memory_with_expansion dst bs ss).vs_memory
Proof
  strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size ty`, `ss.vs_memory`] >> simp[] >>
  `TAKE (type_memory_size ty)
     (DROP off (write_memory_with_expansion dst bs ss).vs_memory) =
   TAKE (type_memory_size ty) (DROP off ss.vs_memory)` by
    (irule write_memory_with_expansion_disjoint_read >> simp[]) >>
  `off + type_memory_size ty <=
    LENGTH (write_memory_with_expansion dst bs ss).vs_memory` by
    (mp_tac (Q.SPECL [`dst`, `bs`, `ss`]
       write_memory_with_expansion_nondecreasing) >> decide_tac) >>
  gvs[mem_bytes_at_def, rich_listTheory.TAKE_APPEND1]
QED

Theorem kwarg_buffer_copy_frame:
  kwarg_buffer_rel func cenv p ty v ss /\
  (!w. lookup_var p ss = SOME w ==>
    w2n w + type_memory_bytes cenv ty <= LENGTH ss.vs_memory /\
    (w2n w + type_memory_bytes cenv ty <= dst \/
     dst + LENGTH bs <= w2n w)) ==>
  kwarg_buffer_rel func cenv p ty v
    (write_memory_with_expansion dst bs ss)
Proof
  rw[kwarg_buffer_rel_def] >> qexistsl_tac [`tv`,`w`] >>
  `val_in_memory tv v (w2n w)
    (write_memory_with_expansion dst bs ss).vs_memory` by
    (irule copy_keeps_val_in_memory >> simp[] >>
     first_x_assum drule >> decide_tac) >>
  gvs[local_backed_def, write_memory_with_expansion_def, lookup_var_def] >>
  metis_tac[]
QED

(* Runtime payload is three bytes, but capacity 33 requires a 96-byte
   copy. Nonzero trailing calldata makes the full padded copy observable.
   The existing value occupies [0,32); the new buffer is [64,160). *)
Definition copy_probe_input_def:
  copy_probe_input =
    ((mstore 0 (99w:bytes32) (init_venom_state "entry")) with
      <| vs_vars := FEMPTY |+ ("dst",64w) |+ ("old",0w);
         vs_call_ctx := empty_call_context with cc_calldata :=
           (word_to_bytes (3w:bytes32) T ++ [42w;43w;44w] ++
            REPLICATE 61 170w) |>)
End

Definition copy_probe_code_def:
  copy_probe_code =
    (SND (compile_abi_decode_to_buf (Var "dst") (Lit 0w)
      CALLDATALOAD (Lit 0w) (DecBytestring 33)
      kwarg_probe_state)).cs_current_insts
End

Theorem bytes_padded_copy_execution:
  ?ss. run_inst_seq copy_probe_code copy_probe_input = OK ss /\
    val_in_memory (BaseTV (BytesT (Dynamic 33)))
      (BytesV [42w;43w;44w]) 64 ss.vs_memory /\
    val_in_memory (BaseTV (UintT 256)) (IntV 99) 0 ss.vs_memory /\
    mem_bytes_at 99 61 ss.vs_memory = REPLICATE 61 170w /\
    LENGTH ss.vs_memory = 160 /\
    lookup_var "dst" ss = SOME 64w /\
    lookup_var "old" ss = SOME 0w /\
    ss.vs_accounts = copy_probe_input.vs_accounts /\
    ss.vs_transient = copy_probe_input.vs_transient /\
    ss.vs_allocas = copy_probe_input.vs_allocas /\
    ss.vs_alloca_next = copy_probe_input.vs_alloca_next
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

(* Memory writes alone cannot change already evaluated operands or
   persistent/transient state. Generated temporary SSA writes require a
   separate compiler freshness argument; the execution probe checks two
   concrete live pointer names rather than assuming it from source names. *)
Theorem copy_state_frame:
  eval_operand op (write_memory_with_expansion dst bs ss) =
    eval_operand op ss /\
  (write_memory_with_expansion dst bs ss).vs_accounts = ss.vs_accounts /\
  (write_memory_with_expansion dst bs ss).vs_transient = ss.vs_transient /\
  (write_memory_with_expansion dst bs ss).vs_allocas = ss.vs_allocas /\
  (write_memory_with_expansion dst bs ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

(* Only three bytes are present after the length word. CALLDATACOPY still
   expands and zero-pads the complete capacity, not just the live payload. *)
Theorem bytes_short_calldata_copy_execution:
  ?ss. run_inst_seq copy_probe_code
    (copy_probe_input with vs_call_ctx := empty_call_context with
      cc_calldata := (word_to_bytes (3w:bytes32) T ++ [42w;43w;44w])) = OK ss /\
    val_in_memory (BaseTV (BytesT (Dynamic 33)))
      (BytesV [42w;43w;44w]) 64 ss.vs_memory /\
    mem_bytes_at 99 61 ss.vs_memory = REPLICATE 61 0w /\
    LENGTH ss.vs_memory = 160
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in kwargCopyFrameProps: " ^ name))
  (DB.thms "kwargCopyFrameProps");
