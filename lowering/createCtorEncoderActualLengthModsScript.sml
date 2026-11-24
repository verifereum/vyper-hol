(* Transfer the saved-list witness to the observed encoder cut. *)
Theory createCtorEncoderActualLengthMods
Ancestors
  createCtorEncoderActualLength createExprSizeExitDefsMods
  createMarkedPath createCtorEncoderLengthMods createCtorEncoderFinish
  createCtorEncoderCutOccurrence createCtorSegmentArrival createCtorOversizedSink
  abiEncoderProps bodyFullExtCallDirectState fragGasOrigin fragGasOriginPtr
  fragExec venomExecProofs relation arithmetic pair
Libs pairLib horizonTypeLib

(* All later segments project to one relation with the same lower ID bound. *)

Theorem ctor_encoder_length_at_marked_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre_mods mods ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post_mods mods keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
      H (INL vs) ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  rows = ZIP (svs,MAP (lowered_value_type ce) args) /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-dst_offset /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\
  RTC (create_marked_edge (\p ms q. ?bb i.
    (p.vs_current_bb,p.vs_inst_idx) <> (en.cs_current_bb,LENGTH en.cs_current_insts) /\
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids st en /\
    gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (t,encmarks) /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  c 0 = en /\ r 0 = t /\ r n = bad /\
  (!k. k < n ==>
    (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
    RTC (create_marked_edge (\p ms q. ?bb i.
      (p.vs_current_bb,p.vs_inst_idx) <>
        ((c (SUC k)).cs_current_bb,LENGTH (c (SUC k)).cs_current_insts) /\
      lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\
      i.inst_id IN frag_ids (c k) (c (SUC k)) /\
      gas_origin_edge F explicit ctx func p ms (OK q)))
      (r k,[]) (r (SUC k),chunk k)) /\
  lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
  get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
  ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value; off; sz]) \/
   (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value; off; sz; salt])) /\
  eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w ==>
  ?Gt tt.
    (pure_frame ce func ee se u t /\ wb_frame ce ee ee se u t) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en t Gt tt /\
    eval_operand alen t = SOME (n2w (LENGTH bytes)) /\ op_taint tt alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) t.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tt.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt)
Proof
  cheat
QED
