(* TOP-LEVEL: a traversal invariant for arbitrary recursive ABI payloads.
   Remaining source values, completed heads/tails and the parent cursor are
   tied to the actual compiler cut and its reserved operand frontier.
   Helpers initialize the invariant and read off the complete final bytes. *)
Theory abiMemoryFieldsState
Ancestors
  abiMemoryEncoding abiMemoryFieldEntry abiMemoryLeafRun abiFieldOperands
  abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  compileEnv venomState list words arithmetic

Definition abi_memory_fields_operands_def:
  abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss <=>
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    abi_operand_before cs.cs_next_var dyn_ptr /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr
End

Definition abi_memory_fields_data_def:
  abi_memory_fields_data done entries remaining tail_start (dst_addr:bytes32) (dyn_addr:bytes32)
      (root_addr:bytes32) source_capacity source_offset ss <=>
    source_offset <= source_capacity /\ w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr + source_offset) (source_capacity - source_offset)
      ss.vs_memory remaining /\
    abi_fields_layout done (w2n dst_addr) 0 tail_start ss /\
    mload (w2n dyn_addr) ss = n2w (tail_start + abi_field_tail_size done)
End

Definition abi_memory_fields_state_def:
  abi_memory_fields_state full dst src dyn_ptr tail_start dst_addr dyn_addr root_addr source_capacity
      entries source_offset head_offset cs ss <=>
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    ?done remaining. full = done ++ remaining /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_data done entries remaining tail_start dst_addr dyn_addr root_addr
        source_capacity source_offset ss
End

Theorem abi_memory_fields_operands_frame:
  !ctx func cs mid ret encoded_addr payload scratch ss out dst src dyn_ptr dst_addr root_addr dyn_addr.
    abi_encoding_result ctx func cs mid ret encoded_addr payload scratch ss out /\
    cs.cs_next_var <= mid.cs_next_var /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss ==>
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr mid out
Proof
  rpt gen_tac >> strip_tac >> fs[abi_encoding_result_def, abi_memory_fields_operands_def] >>
  rpt conj_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]
QED

Theorem abi_memory_fields_state_initial:
  !full dst src dyn_ptr tail_start dst_addr dyn_addr root_addr source_capacity entries cs ss.
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full /\
    mload (w2n dyn_addr) ss = n2w tail_start ==>
    abi_memory_fields_state full dst src dyn_ptr tail_start dst_addr dyn_addr root_addr source_capacity
      entries 0 0 cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_memory_fields_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`[]`, `full`] >>
  simp[abi_memory_fields_data_def, abi_field_head_size_def]
QED

Theorem abi_memory_fields_state_intro:
  !full done remaining dst src dyn_ptr tail_start dst_addr dyn_addr root_addr source_capacity
      entries source_offset head_offset cs ss.
    full = done ++ remaining /\ head_offset = abi_field_head_size done /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done entries remaining tail_start dst_addr dyn_addr root_addr
      source_capacity source_offset ss ==>
    abi_memory_fields_state full dst src dyn_ptr tail_start dst_addr dyn_addr root_addr source_capacity
      entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_memory_fields_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`done`, `remaining`] >> simp[]
QED

Theorem abi_memory_fields_data_source:
  !done info abi_sz mem_sz is_dyn rest payload fields tail_start dst_addr dyn_addr root_addr
      source_capacity source_offset ss.
    abi_memory_fields_data done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset ss ==>
    source_offset + mem_sz <= source_capacity /\
    w2n root_addr + source_offset < dimword (:256) /\
    abi_memory_encoding info (w2n root_addr + source_offset) mem_sz ss.vs_memory payload /\
    abi_memory_fields rest (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) ss.vs_memory fields /\
    abi_sz = (if is_dyn then 32 else LENGTH payload)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_fields_data_def, abi_memory_fields_cons_cases] >>
  rpt strip_tac >> fs[SUB_SUB] >> decide_tac
QED

Theorem abi_memory_fields_state_complete:
  !full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity source_offset head_offset cs ss.
    abi_memory_fields_state full dst src dyn_ptr (abi_field_head_size full) dst_addr dyn_addr root_addr
      source_capacity [] source_offset head_offset cs ss ==>
    read_memory (w2n dst_addr) (LENGTH (abi_field_bytes (abi_field_head_size full) full)) ss =
      abi_field_bytes (abi_field_head_size full) full /\
    mload (w2n dyn_addr) ss = n2w (LENGTH (abi_field_bytes (abi_field_head_size full) full)) /\
    head_offset = abi_field_head_size full
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_fields_state_def, abi_memory_fields_data_def] >>
  strip_tac >> rename1 `abi_memory_fields [] _ _ _ remaining` >>
  `remaining = []` by (drule abi_memory_fields_length >> simp[]) >> gvs[] >>
  drule abi_fields_layout_contiguous >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive ABI traversal state: " ^ name)
  end) (DB.thms "abiMemoryFieldsState")
