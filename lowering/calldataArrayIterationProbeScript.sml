(* Bounded interface diagnostic. ML quotations below are terms, NOT theorems.
   No assertion of a complete array decoder or new semantic predicate is made. *)
Theory calldataArrayIterationProbe
Ancestors
  calldataArrayRawCallsite calldataExactInterfaceProbe calldataDynOwned
  robustCopyTransportPtr exprSimProps abiDecoderFrame allocaFrontierBound
  allocaBudgetProps allocaHistory vyperCalldata abiDecoderPhi
  abiDecoderCoherence abiDecoderContract abiDecoderReentry
  loweringStateRelDefs compileEnv fragGasOriginPtr bodyPtrDefs ptrDiscipline
  valueEncodingProps valueEncodingDefs valueEncoding venomState
  venomExecSemantics words finite_map pred_set list arithmetic

(* Fixed ce/env/sf/ty/tv only: all execution parameters are universally bound.
   This repeats the baseline diagnostic schema, retaining EVERY clause, and
   spells out the additional robustness/world frame required by C1.9. *)
val fixed_element_contract = ``
  !st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
  abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ptr_covers G tn child initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?z H u. z.vs_returndata = [] /\
     (?fuel. run_from fuel ctx fn initial = Abort Revert_abort z /\
       mem_safe_run fuel ctx fn initial) /\
     (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
       (initial,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v x sc H u.
    cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v (type_memory_size tv) /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u)) /\
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==>
      val_in_memory tv x d mem) /\
    v.vs_accounts = initial.vs_accounts /\
    v.vs_transient = initial.vs_transient /\
    v.vs_logs = initial.vs_logs /\
    v.vs_outcomes = initial.vs_outcomes /\
    v.vs_requests = initial.vs_requests /\
    v.vs_pending_deletions = initial.vs_pending_deletions /\
    v.vs_tx_ctx = initial.vs_tx_ctx /\
    v.vs_block_ctx = initial.vs_block_ctx /\
    v.vs_fmp = initial.vs_fmp /\
    v.vs_gas_readings = initial.vs_gas_readings``;

(* The nonwrapping premise of the convenience wrapper is NOT valid for every
   source word. This is not a counterexample to any frozen family target. *)
Theorem array_iteration_wrapping_header[local]:
  w2n (n2w (dimword (:256)-16):bytes32) = dimword (:256)-16 /\
  cd_at F (dimword (:256)-16) 32 = 16 /\
  ~(dimword (:256)-16+32 < dimword (:256))
Proof
  simp[cd_at_def, dimword_def, w2n_n2w]
QED

Theorem array_iteration_modular_header[local]:
  !p:bytes32. cd_at F (w2n p) 32 = w2n (p+32w)
Proof
  simp[cd_at_def, word_add_def, w2n_n2w]
QED

Theorem array_iteration_normalized_member[local]:
  cd_member_ptr F cd tv (sb+32) ofs =
  cd_member_ptr F cd tv ((sb+32) MOD dimword (:256)) ofs
Proof
  simp[cd_member_ptr_def, cd_at_def, LET_THM, MOD_PLUS]
QED

Theorem array_iteration_cursor_frontier[local]:
  alloca_frontier_inv ctx fn site (s with vs_inst_idx := n) <=>
  alloca_frontier_inv ctx fn site s
Proof
  simp[alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

(* Use the return-frame window AND shrinking dirty set, not the physical
   memory frame alone. A child may clean extra bytes outside its own cell. *)
Theorem array_iteration_robust_prefix[local]:
  stride = type_memory_size tv /\ EVERY (val_wf tv) xs /\ LENGTH xs = j /\
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory /\ dirty' SUBSET dirty /\
  (!k. k < j ==> !mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory tv (EL k xs) (dst+32+k*stride) mem) ==>
  !k. k < j ==> !mem. mem_agree_outside dirty' t.vs_memory mem ==>
    val_in_memory tv (EL k xs) (dst+32+k*stride) mem
Proof
  strip_tac >> qx_gen_tac `k` >> strip_tac >>
  `val_wf tv (EL k xs)` by metis_tac[EVERY_EL] >>
  `val_footprint tv (EL k xs) <= stride` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> irule calldata_member_robust_window_frame >>
  qexistsl_tac [`dirty`, `s.vs_memory`] >> simp[] >>
  `SUC k * stride <= j * stride` by simp[] >>
  `32+k*stride+val_footprint tv (EL k xs) <= 32+j*stride` by
    (fs[MULT_CLAUSES] >> decide_tac) >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`32+k*stride`, `val_footprint tv (EL k xs)`] mp_tac) >>
  simp[ADD_ASSOC]
QED

Theorem array_iteration_index_edges[local]:
  (0 < count /\ count < dimword (:256) ==>
    w2n (n2w (0:num):bytes32) = 0 /\ SUC 0 <= count) /\
  (j < count /\ count < dimword (:256) /\ j+1 = count ==>
    (n2w j:bytes32)+1w = n2w count /\ SUC j = count) /\
  ~((0:num) < 0) /\
  (!tv dst dirty mem. !k. k < LENGTH ([]:value list) ==>
    !m. mem_agree_outside dirty mem m ==>
      val_in_memory tv (EL k []) (dst+32+k*type_memory_size tv) m)
Proof
  simp[] >> metis_tac[abi_decode_loop_increment_word, ADD1]
QED
