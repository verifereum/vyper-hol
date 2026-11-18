(* Positive induction interfaces for registration on the actual calldata. *)
Theory selectedAcceptedInterfaces
Ancestors
  calldataRegistrationRawAddress abiDecoderCoherence abiDecoderReentry
  abiDecoderFrame fragGasOriginPtr fragGasOriginPtrExec gasPathPtrExec ptrSafeRun
  fragGasPathMem moduleLowering ptrDiscipline bodyPtrDefs compileEnv loweringStateRelDefs
  venomState venomExecSemantics valueEncoding vyperCalldata words finite_map
  pred_set list arithmetic

(* The conclusion refers to the given source value, not a value selected
   after execution. Scratch owners and old-variable frames permit reentry. *)
Definition selected_decoder_accepts_def:
  selected_decoder_accepts ce env sf ty tv <=>
  !st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG x.
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
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x ==>
    ?v sc H u.
      ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
      v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
      val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
      (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==>
        val_in_memory tv x d mem) /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn initial = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
      v.vs_call_ctx = initial.vs_call_ctx /\
      v.vs_data_section = initial.vs_data_section /\ v.vs_code = initial.vs_code /\
      v.vs_accounts = initial.vs_accounts /\ v.vs_transient = initial.vs_transient /\
      v.vs_logs = initial.vs_logs /\ v.vs_outcomes = initial.vs_outcomes /\
      v.vs_requests = initial.vs_requests /\
      v.vs_pending_deletions = initial.vs_pending_deletions /\
      v.vs_tx_ctx = initial.vs_tx_ctx /\ v.vs_block_ctx = initial.vs_block_ctx /\
      v.vs_fmp = initial.vs_fmp /\ v.vs_gas_readings = initial.vs_gas_readings /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\ allocas_from lower v /\
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
End

Definition selected_slot_accepts_def:
  selected_slot_accepts ce env sf ty tv <=>
  !name prim dyn sz di ofs st ce' last loc n limit ctx fn site lo PG s G tn
    delta srcpos x.
    compile_register_positional_args ce [(name,prim,dyn,sz,di)] (4+ofs) st =
      (ce',last) /\
    FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
    n = type_memory_size tv /\ di = type_to_abi_dec_info sf ce ty /\
    abi_decoder_coherent ce env sf ty tv /\ dyn = tv_abi_dynamic tv /\
    (prim ==> ~dyn /\ ?clamp. di = DecPrimWord clamp) /\
    4+ofs < dimword (:256) /\ n < dimword (:256) /\
    delta = w2n (cd_word s.vs_call_ctx.cc_calldata (4+ofs)) /\
    abi_decode_load CALLDATALOAD (n2w (4+ofs) : bytes32) s = n2w delta /\
    srcpos = (if dyn then (4+delta) MOD dimword (:256) else 4+ofs) /\
    4 <= srcpos /\ srcpos = 4 + (if dyn then delta else ofs) /\
    (dyn ==> 4+delta < dimword (:256)) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    unit_alloca_budget ctx < dimword (:256) /\
    fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
    (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit.cs_next_var /\
    fresh_vars_wrt st s /\ fresh_vars_wrt limit s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
    cd_decode F s.vs_call_ctx.cc_calldata tv srcpos = SOME x ==>
    ?t H u q p.
      ce' = ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var q) n)) /\
      lookup_var q t = SOME (n2w p) /\
      FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
      MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
      st.cs_next_id < last.cs_next_id /\ p+n < dimword (:256) /\
      ptr_covers H u q t n /\ value_has_type tv x /\ val_wf tv x /\
      val_footprint tv x <= n /\ val_in_memory tv x p t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv x p mem) /\
      (!old q0 p0 n0 tv0 v0.
        old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
        lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
        val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory tv0 v0 p0 mem) ==>
        old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
        lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
        val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
        (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
          val_in_memory tv0 v0 p0 mem)) /\
      (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
      ((!inst w b k. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) ==> k = w2n w) ==>
       (!inst w b k. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k) ==> k = w2n w)) /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      fresh_vars_wrt last t /\ fresh_vars_wrt limit t /\
      ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
      t.vs_inst_idx = LENGTH last.cs_current_insts /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
      t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
      t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,H,u))
End

(* The caller can keep cd fixed as it advances through the registration fold. *)
Theorem selected_slot_source_input:
  cd = s.vs_call_ctx.cc_calldata /\ dyn = tv_abi_dynamic tv /\
  delta = w2n (cd_word cd (4+ofs)) /\
  srcpos = (if dyn then (4+delta) MOD dimword (:256) else 4+ofs) /\
  4+ofs < dimword (:256) /\
  calldata_decode_args cd (tv::tvs) ofs = SOME (x::xs) ==>
  abi_decode_load CALLDATALOAD (n2w (4+ofs) : bytes32) s = n2w delta /\
  4 <= srcpos /\ srcpos = 4 + (if dyn then delta else ofs) /\
  (dyn ==> 4+delta < dimword (:256)) /\
  w2n (n2w srcpos : bytes32) = srcpos /\
  cd_decode F s.vs_call_ctx.cc_calldata tv srcpos = SOME x /\
  calldata_decode_args cd tvs (ofs + tv_abi_size tv) = SOME xs
Proof
  strip_tac >>
  `srcpos = (if tv_abi_dynamic tv then (4+delta) MOD dimword (:256) else 4+ofs)` by simp[] >>
  drule_all calldata_decode_args_step_exact >>
  disch_then (qspec_then `tvs` strip_assume_tac) >>
  qpat_x_assum `!vals. calldata_decode_args _ _ _ = SOME vals <=> _`
    (qspec_then `x::xs` mp_tac) >>
  asm_rewrite_tac [CONS_11] >> strip_tac >>
  `srcpos < dimword (:256)` by (Cases_on `dyn` >> fs[]) >>
  `w2n (n2w srcpos : bytes32) = srcpos` by simp[] >>
  metis_tac[]
QED

(* Both projections retain the concrete endpoint of the registration path. *)
Theorem selected_zero_path_mem:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u) ==>
  gas_path_mem ctx fn s 0 (OK t)
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule fragGasOriginTheory.gas_origin_path_erase >>
  simp[fragGasModeTheory.gas_marked_path_def]
QED

Theorem selected_zero_path_ptr_pullback:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u) /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> simp[] >>
  strip_tac >> metis_tac[gas_path_ptr_safe_run]
QED
