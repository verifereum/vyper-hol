(* Share the actual cursor-load/tail-address phase between members and arrays.
   TOP-LEVEL: abi_scratch_dynamic_child_split exposes the member's head ADD,
   existing array-tail setup, recursive encoder and cursor bookkeeping. *)
Theory abiScratchChildSplit
Ancestors
  abiEncoderChildContext abiEncoderChildCode abiEncoderArrayTail abiEncoderAddressReach
  abiDecoderContract abiDecoderReentry fragExec emitHelperProps compileEnv emitHelper
  venomInst list rich_list words arithmetic
Libs monadsyntax

Theorem abi_scratch_child_prefix_phases:
  abi_encode_child_prefix dst ho dyn_ptr =
    do head <- emit_op ADD [dst;Lit (n2w ho)];
       tail <- abi_encode_array_tail dst dyn_ptr;
       return (head,FST tail,SND tail)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_child_prefix_def, abi_encode_array_tail_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_scratch_child_prefix_split:
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func ==>
  ?head middle tail.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,middle) /\
    abi_encode_array_tail dst dyn_ptr middle = (tail,prepared) /\
    ops = (head,FST tail,SND tail) /\
    fn_has_code st middle func /\ fn_has_code middle prepared func /\
    middle.cs_next_var = st.cs_next_var+1 /\ middle.cs_next_id = st.cs_next_id+1 /\
    abi_decoder_operand_live middle.cs_next_var head
Proof
  simp_tac bool_ss [abi_scratch_child_prefix_phases, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD _ st = (head,middle)` >>
  rename1 `abi_encode_array_tail dst dyn_ptr middle = (tail,prepared)` >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `cs_extends middle prepared` by (irule abi_encoder_straight_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[]
QED

Theorem abi_scratch_dynamic_child_split:
  compile_abi_encode_child dst src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?head middle tail prepared child_len child_end.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,middle) /\
    abi_encode_array_tail dst dyn_ptr middle = (tail,prepared) /\
    compile_abi_encode_to_buf (SND tail) src ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix head dyn_ptr (FST tail) child_len child_end = (child_len,end_st) /\
    out = child_len /\
    fn_has_code st middle func /\ fn_has_code middle prepared func /\
    fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    middle.cs_next_var = st.cs_next_var+1 /\ middle.cs_next_id = st.cs_next_id+1 /\
    middle.cs_next_var <= end_st.cs_next_var /\ middle.cs_next_id <= end_st.cs_next_id /\
    abi_decoder_operand_live middle.cs_next_var head
Proof
  strip_tac >> drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  drule_all abi_scratch_child_prefix_split >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  qexistsl_tac [`head`, `middle`, `tail`, `prepared`, `child_len`, `child_end`] >>
  gvs[] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_CHILD_SPLIT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch dynamic child phases not kernel closed: " ^ n)
  end) (DB.thms "abiScratchChildSplit");
