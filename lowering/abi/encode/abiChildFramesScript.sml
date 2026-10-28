(* TOP-LEVEL: the dynamic-child suffix preserves its encoded payload and
   protected memory windows while writing the head and tail-counter words. *)
Theory abiChildFrames
Ancestors
  abiChildSuffix ssaOperandFrame memoryReadProps venomState venomExecSemantics venomMemProps
  list words arithmetic

Theorem abi_child_suffix_memory_image:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss)
      with vs_vars := ss.vs_vars =
    mstore (w2n dyn_addr) (tail_offset + child_len) (mstore (w2n head_addr) tail_offset ss)
Proof
  simp[abi_child_suffix_state_def, mstore_update_var, update_var_reset_vars,
    GSYM mstore_reset_vars]
QED

Theorem abi_child_suffix_read_frame:
  !var_base head_addr dyn_addr tail_offset child_len ss offset read_len.
    (offset + read_len <= w2n head_addr \/ w2n head_addr + 32 <= offset) /\
    (offset + read_len <= w2n dyn_addr \/ w2n dyn_addr + 32 <= offset) ==>
    read_memory offset read_len
      (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) =
    read_memory offset read_len ss
Proof
  rpt gen_tac >> strip_tac >>
  `!name value st. read_memory offset read_len (update_var name value st) =
    read_memory offset read_len st` by simp[read_memory_def, update_var_def] >>
  asm_simp_tac (srw_ss()) [abi_child_suffix_state_def, read_memory_mstore_disjoint]
QED

Theorem abi_child_suffix_words:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    (w2n head_addr + 32 <= w2n dyn_addr \/ w2n dyn_addr + 32 <= w2n head_addr) ==>
    mload (w2n head_addr)
      (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) = tail_offset /\
    mload (w2n dyn_addr)
      (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) = tail_offset + child_len
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory (w2n head_addr) 32
    (mstore (w2n dyn_addr) (tail_offset + child_len)
      (update_var (compiler_var_name var_base 0) (tail_offset + child_len)
        (mstore (w2n head_addr) tail_offset ss))) =
    read_memory (w2n head_addr) 32
      (update_var (compiler_var_name var_base 0) (tail_offset + child_len)
        (mstore (w2n head_addr) tail_offset ss))` by
    (irule read_memory_mstore_disjoint >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac (srw_ss()) [abi_child_suffix_state_def, mload_mstore_same] >>
  ONCE_REWRITE_TAC [mload_read_memory] >> asm_simp_tac bool_ss [] >>
  rewrite_tac [GSYM mload_read_memory] >> simp[mload_update_var, mload_mstore_same]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI child memory frames: " ^ name)
  end) (DB.thms "abiChildFrames")
