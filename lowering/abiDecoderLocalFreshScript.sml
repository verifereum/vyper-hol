(* Select the exact decoder witnesses at their local compiler limit first.
   Ambient freshness is then restored on those same witnesses. *)
Theory abiDecoderLocalFresh
Ancestors
  calldataExactInterfaceProbe abiDecoderCounters emitHelperProps

Theorem abi_decoder_local_fresh:
  (!st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
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
        (initial,G,tn) [] (OK v,H,u))) ==>
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
    fresh_vars_wrt st initial /\ allocas_from lower initial /\
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
      fresh_vars_wrt last v /\ fresh_vars_wrt limit v /\
      ptr_covers H u child v (type_memory_size tv) /\
      (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
        FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
        (initial,G,tn) [] (OK v,H,u))
Proof
  disch_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_var <= last.cs_next_var` by
    (drule abi_decoder_variable_counter >> simp[]) >>
  `fresh_vars_wrt last initial` by
    (irule fresh_vars_wrt_mono >> qexists_tac `st` >> simp[]) >>
  qpat_x_assum `!st last limit. _`
    (qspecl_then [`st`, `last`, `last`]
      (drule_all_then (qspec_then `PG` strip_assume_tac) o
       PURE_REWRITE_RULE [arithmeticTheory.LESS_EQ_REFL]))
  >- (disj1_tac >> conj_tac >- simp[] >>
      qexistsl_tac [`z`, `H`, `u`] >> simp[] >>
      qexists_tac `fuel` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`v`, `x`, `sc`, `H`, `u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule fresh_vars_wrt_mono >> qexists_tac `last` >>
  rewrite_tac [arithmeticTheory.GREATER_EQ] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
