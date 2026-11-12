Theory extRetDynamicArrayPhasePtr
Ancestors
  abiEncoderArrayCode abiEncoderArrayTail abiEncoderChildCode abiDecoderLoopEmit
  abiDecoderIndexInit abiDecoderDynamicLoopSetup abiEncoder compileEnv emitHelper
  words list arithmetic context abiEncoderArrayContext abiEncoderArrayLoopContext
  abiEncoderArrayDynamicMemory abiEncoderArrayPhases freshWrites
Libs monadsyntax

Theorem encoder_dynamic_array_loop_phases:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op =
  do cells <- abi_encode_array_dynamic_init count_op asz;
     labels <- abi_encode_array_header (FST cells) count_op;
     coords <- abi_encode_array_addresses (FST cells) src dst asz msz;
     tail <- abi_encode_array_tail (FST (SND coords)) (SND cells);
     len <- compile_abi_encode_to_buf (SND tail) (SND (FST coords)) ei;
     abi_encode_child_suffix (SND (SND coords)) (SND cells) (FST tail) len;
     abi_decode_loop_suffix (FST cells) (FST (FST coords))
       (FST labels) (SND (SND labels));
     abi_encode_array_dynamic_exit src (SND cells)
  od
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def,
    abi_encode_array_dynamic_init_def, abi_encode_array_header_def,
    abi_encode_array_addresses_def, abi_encode_array_tail_def,
    abi_encode_child_suffix_def, abi_decode_loop_suffix_def,
    abi_encode_array_dynamic_exit_def, abi_decode_index_init_def,
    abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    compile_alloc_buffer_def, FUN_EQ_THM, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem encoder_dynamic_array_loop_trace:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op si = (out,sf) ==>
  ?cells labels coords tail len sh sa sx sb se ss sc.
    abi_encode_array_dynamic_init count_op asz si = (cells,sh) /\
    abi_encode_array_header (FST cells) count_op sh = (labels,sa) /\
    abi_encode_array_addresses (FST cells) src dst asz msz sa = (coords,sx) /\
    abi_encode_array_tail (FST (SND coords)) (SND cells) sx = (tail,sb) /\
    compile_abi_encode_to_buf (SND tail) (SND (FST coords)) ei sb = (len,se) /\
    abi_encode_child_suffix (SND (SND coords)) (SND cells) (FST tail) len se =
      (len,ss) /\
    abi_decode_loop_suffix (FST cells) (FST (FST coords))
      (FST labels) (SND (SND labels)) ss = ((),sc) /\
    abi_encode_array_dynamic_exit src (SND cells) sc = (out,sf)
Proof
  simp_tac bool_ss [encoder_dynamic_array_loop_phases,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[abi_encode_child_suffix_shape]
QED

Theorem encoder_dynamic_array_outer_trace:
  compile_abi_encode_to_buf dst src (AbiDynArray ei 32 msz T) si = (out,sf) ==>
  ?parent count_op encoded old sumv s0 s1 s2 s3 s4 s5 s6 s7.
    compile_alloc_buffer 32 si = (parent,s0) /\
    emit_void MSTORE [parent.buf_operand;Lit 0w] s0 = ((),s1) /\
    emit_op MLOAD [src] s1 = (count_op,s2) /\
    emit_void MSTORE [dst;count_op] s2 = ((),s3) /\
    compile_abi_encode_dyn_loop dst src ei 32 msz count_op s3 = (encoded,s4) /\
    emit_op MLOAD [parent.buf_operand] s4 = (old,s5) /\
    emit_op ADD [old;encoded] s5 = (sumv,s6) /\
    emit_void MSTORE [parent.buf_operand;sumv] s6 = ((),s7) /\
    emit_op MLOAD [parent.buf_operand] s7 = (out,sf)
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM, boolTheory.NOT_CLAUSES,
    boolTheory.COND_CLAUSES] >>
  strip_tac >> rpt (pairarg_tac >> gvs[])
QED

(* All code slices share the endpoints of the actual outer compilation. *)
Theorem encoder_dynamic_array_phase_context:
  compile_abi_encode_to_buf dst src (AbiDynArray ei 32 msz T) si = (out,sf) /\
  fn_has_code si sf func ==>
  ?ops sl encoded slend cells sh labels sa idx send sc coords sx tail sb len se.
    abi_encode_array_prefix src dst si = (ops,sl) /\
    compile_abi_encode_dyn_loop dst src ei 32 msz (SND ops) sl = (encoded,slend) /\
    abi_encode_array_finish (FST ops) encoded slend = (out,sf) /\
    abi_encode_array_dynamic_init (SND ops) 32 sl = (cells,sh) /\
    abi_encode_array_header (FST cells) (SND ops) sh = (labels,sa) /\
    abi_encode_array_addresses (FST cells) src dst 32 msz sa = (coords,sx) /\
    abi_encode_array_tail (FST (SND coords)) (SND cells) sx = (tail,sb) /\
    compile_abi_encode_to_buf (SND tail) (SND (FST coords)) ei sb = (len,se) /\
    abi_encode_child_suffix (SND (SND coords)) (SND cells) (FST tail) len se = (len,send) /\
    idx = FST (FST coords) /\
    abi_decode_loop_suffix (FST cells) idx (FST labels) (SND (SND labels)) send = ((),sc) /\
    abi_encode_array_dynamic_exit src (SND cells) sc = (encoded,slend) /\
    fn_has_code si sl func /\ fn_has_code sl slend func /\ fn_has_code slend sf func /\
    fn_has_code sl sh func /\ fn_has_code sh sa func /\
    fn_has_code sa sx func /\ fn_has_code sx sb func /\
    fn_has_code sb se func /\ fn_has_code se send func /\
    fn_has_code send sc func /\ fn_has_code sc slend func /\
    sl.cs_next_var = si.cs_next_var+2 /\ sl.cs_next_id = si.cs_next_id+4 /\
    sl.cs_next_var <= slend.cs_next_var /\
    sf.cs_next_var = slend.cs_next_var+3 /\
    sx.cs_next_var = sa.cs_next_var+7 /\ sb.cs_next_var = sx.cs_next_var+2 /\
    sb.cs_next_var <= se.cs_next_var /\ send.cs_next_var = se.cs_next_var+1
Proof
  strip_tac >> drule_all abi_encode_array_context >> simp[] >> strip_tac >>
  drule_all abi_encode_array_dynamic_loop_context >> strip_tac >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  gvs[]
QED
