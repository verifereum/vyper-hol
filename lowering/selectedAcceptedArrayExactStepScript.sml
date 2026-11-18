(* Exact live-name lookup frame at the installed backedge witness. *)
Theory selectedAcceptedArrayExactStep
Ancestors
  selectedAcceptedArrayStep selectedAcceptedInterfaces calldataMemberResourceFrame
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderExecution
  compileEnv venomState venomExecSemantics words arithmetic list finite_map pred_set
  ptrDiscipline bodyPtrDefs fragGasOriginPtr vyperCalldata
  loweringStateRelDefs codegenRel abiDecoderCoherence

Theorem selected_array_iteration_exact:
  selected_decoder_accepts ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts hid (Var q) src CALLDATALOAD hv cv cmp dn
      st.cs_current_bb exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ALL_DISTINCT [q;hv;cv;cmp;dn] /\
  lookup_var q s = SOME (n2w slot) /\ ptr_covers G tn q s 32 /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  abi_decode_load CALLDATALOAD (n2w sb:bytes32) s = n2w cnt /\ j < cnt /\
  cnt < dimword (:256) /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  lookup_block st.cs_current_bb fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st.cs_current_insts = [] /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  phi_prefix_length bb.bb_instructions = 0 /\ fresh_vars_wrt limit s /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ?k. x = STRING #"%" (toString k) /\
    k < limit.cs_next_var) /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  dec_info_needs_offset di = tv_abi_dynamic tv /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s span /\
  abi_decoder_operand_live live (Var q) /\ abi_decoder_operand_live live (Var root) /\
  abi_decoder_operand_live live src /\ live <= st.cs_next_var /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ~abi_decoder_operand_live live (Var x)) /\
  32+j*type_memory_size tv+type_memory_size tv <= span /\ d+span < dimword (:256) /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= limit.cs_next_var /\
  fn_has_code st ready fn /\ fn_has_code ready last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\ unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb'.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb' ==>
    phi_prefix_length bb'.bb_instructions = 0) /\
  (!child. SND (SND ops) = Var child ==>
    compile_abi_decode_to_buf (Var child) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) ready = ((),last)) /\
  FST ops = Var iv /\
  lookup_block last.cs_current_bb fn.fn_blocks = SOME back_bb /\
  back_bb.bb_instructions = last.cs_current_insts ++
    abi_decode_backedge_insts bid iv nv (Var q) s.vs_current_bb /\
  nv = STRING #"%" (toString k) /\ k < limit.cs_next_var /\
  ~abi_decoder_operand_live live (Var nv) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn L H s /\
  L <= ready.cs_next_id /\ ready.cs_next_id <= last.cs_next_id /\ last.cs_next_id <= H /\
  L <= counter_id /\ counter_id < H /\ counter_id <> oid /\
  FLOOKUP s.vs_allocas counter_id = SOME (slot,32) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+span <= base_addr+cap /\
  LENGTH xs = j /\ EVERY (val_wf tv) xs /\ EVERY (value_has_type tv) xs /\
  (!i. i < j ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem) /\
  cd_decode_elems F s.vs_call_ctx.cc_calldata tv (cd_at F (w2n (n2w sb:bytes32)) 32)
    j (SUC n) = SOME pending ==>
  ?x rest t Gt tt scratch.
    pending = x::rest /\
    cd_decode_elems F s.vs_call_ctx.cc_calldata tv (cd_at F (w2n (n2w sb:bytes32)) 32)
      (SUC j) n = SOME rest /\
    cd_decode F s.vs_call_ctx.cc_calldata tv (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
      (cd_at F (w2n (n2w sb:bytes32)) 32) (j*tv_abi_size tv)) = SOME x /\
    LENGTH (xs ++ [x]) = SUC j /\
    EVERY (val_wf tv) (xs ++ [x]) /\ EVERY (value_has_type tv) (xs ++ [x]) /\
    (!i. i < SUC j ==> !mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
      val_in_memory tv (EL i (xs ++ [x])) (d+32+i*type_memory_size tv) mem) /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 0 /\
    allocas_from lower t /\
    calldata_member_resource_frame ctx fn site limit L H live d span s t scratch /\
    FLOOKUP t.vs_allocas counter_id = SOME (slot,32) /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,cap) /\
    lookup_var q t = SOME (n2w slot) /\ ptr_covers Gt tt q t 32 /\
    lookup_var root t = SOME (n2w d) /\ ptr_covers Gt tt root t span /\
    eval_operand src t = SOME (n2w sb) /\ op_taint tt src = {} /\ op_prov Gt src = NONE /\
    mload slot t = n2w (SUC j) /\ DISJOINT {a | slot <= a /\ a < slot+32} tt.t_mem /\
    mem_bytes_at d (32+j*type_memory_size tv) t.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) s.vs_memory /\
    t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
    (!x. abi_decoder_operand_live live (Var x) ==>
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!x. abi_decoder_operand_live live (Var x) ==> FLOOKUP tt.t_var x = FLOOKUP tn.t_var x) /\
    tt.t_mem SUBSET tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gt,tt))
Proof
  ACCEPT_TAC selected_array_iteration_with_frame
QED
