(* Exact nonrecursive bulk decoding: source and resource witnesses coincide. *)
Theory calldataExactBulkJoint
Ancestors
  calldataBulkSourceOutcome calldataBulkUniformPtr calldataFiniteTransport calldataDynOwned
  abiDecoderBulk abiDecoderCoherence abiDecoderReentry abiDecoderContract
  fragGasOriginPtr compileEnv loweringStateRelDefs venomState venomExecSemantics
  vyperCalldata exprLowering valueEncoding words finite_map list arithmetic

Theorem calldata_exact_bulk_joint_limit:
  !ce env sf ety maxn tv ei abi_sz mem_sz
   st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) st = ((),last) /\
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
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==> val_in_memory tv x d mem) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    v.vs_accounts = initial.vs_accounts /\ v.vs_transient = initial.vs_transient /\
    v.vs_logs = initial.vs_logs /\ v.vs_outcomes = initial.vs_outcomes /\
    v.vs_requests = initial.vs_requests /\
    v.vs_pending_deletions = initial.vs_pending_deletions /\
    v.vs_tx_ctx = initial.vs_tx_ctx /\ v.vs_block_ctx = initial.vs_block_ctx /\
    v.vs_fmp = initial.vs_fmp /\ v.vs_gas_readings = initial.vs_gas_readings /\
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
      (initial,G,tn) [] (OK v,H,u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?etv. tv = ArrayTV etv (Dynamic maxn) /\
    abi_decoder_coherent ce env sf ety etv` by
    metis_tac[abi_decoder_coherent_array_iff] >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  `maxn < dimword (:256)` by metis_tac[abi_decoder_bulk_metadata] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (fn th => qpat_assum `type_to_abi_dec_info _ _ _ = _`
      (fn eq => assume_tac (PURE_REWRITE_RULE [eq] th))) >>
  drule_all calldata_bulk_source_outcome >> strip_tac >>
  Cases_on `n <= maxn`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      `lookup_var child initial = SOME (n2w d)` by
        metis_tac[eval_operand_def] >>
      `not_fresh_at st child /\ (!x. src = Var x ==> not_fresh_at st x)` by
        metis_tac[calldata_operand_live_not_fresh] >>
      `abi_decode_load CALLDATALOAD p initial = n2w n` by
        metis_tac[n2w_w2n] >>
      qpat_x_assum `n = _`
        (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM eq])) >>
      `32+n*mem_sz <= type_memory_size (ArrayTV etv (Dynamic maxn)) /\
       n*mem_sz < dimword (:256)` by asm_rewrite_tac[] >>
      drule_all calldata_bulk_decoder_endpoint_ptr_uniform_origin >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      `d + type_memory_size (ArrayTV etv (Dynamic maxn)) <= initial.vs_alloca_next` by
        metis_tac[abiCallerAllocationTheory.abi_caller_allocation_end] >>
      `d+32+n*mem_sz <= initial.vs_alloca_next` by decide_tac >>
      disj2_tac >>
      qexistsl [`t with vs_inst_idx := LENGTH last.cs_current_insts`,
        `v`,`[]`,`H`,`u`] >>
      asm_rewrite_tac[] >>
      FAIL_TAC "accepted package") >>
  FAIL_TAC "rejected count guard"
QED
