(* One pass through a nonbulk calldata decoder loop. *)
Theory calldataNoneArrayIteration
Ancestors
  decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr
  abiDecoderLoopRegisters decoderGhostFramePtr allocaFrontierBound
  calldataDynOwned calldataChildFrame calldataFiniteTransport ptrDiscipline
  abiDecodeRanges abiDecoderExecution
  calldataSourceCorrespondence vyperCalldata abiDecoderFrame abiDecoderReentry
  abiDecoderCoherence abiDecoderContract abiDecoderDynamicLoopSetup
  entryDecoderSetupEndpoint entryDecoderStateFrame calldataDynStep decoderArraySetupPtr
  fragGasOriginPtr fragGasOriginPtrLoop fragExec emitHelperProps instIdxIndep venomExecSemantics
  venomState loweringStateRelDefs abiDecoderLoopSetup abiDecoderArraySetupInputs
  words arithmetic finite_map pred_set list

(* Both the header displacement and the scaled element offset are modular. *)
Theorem none_array_member_word[local]:
  (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
    (cd_at F sb 32) (j*tv_abi_size tv)) : bytes32) =
  if tv_abi_dynamic tv then
    n2w (sb+32+w2n (abi_decode_load CALLDATALOAD
      (n2w (sb+32+j*tv_abi_size tv):bytes32) s))
  else n2w (sb+32+j*tv_abi_size tv)
Proof
  Cases_on `tv_abi_dynamic tv` >>
  simp[cd_member_ptr_def, cd_at_def, LET_THM, calldata_decode_load_word,
       w2n_n2w, MOD_PLUS]
QED

(* No fresh allocation or global history is needed: this setup is read-only. *)
Theorem none_array_element_setup[local]:
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
  j < dimword (:256) /\ slot+32 < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ lookup_var root s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  not_fresh_at st q /\ not_fresh_at st root /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn q s 32 /\ ptr_covers G tn root s cap /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  32+j*type_memory_size tv+type_memory_size tv <= cap /\
  d+32+j*type_memory_size tv < dimword (:256) /\
  type_memory_size tv < dimword (:256) /\
  ready.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code st ready fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts
  ==>
  ?t HG u child.
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F sb 32) (j*tv_abi_size tv))) /\
    eval_operand (SND (SND ops)) t =
      SOME (n2w (d+32+j*type_memory_size tv)) /\
    SND (SND ops) = Var child /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    ptr_covers HG u child t (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov HG (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov HG (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit t /\ entry_decoder_obs s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!x. not_fresh_at st x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower explicit ctx.
      allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,HG,u))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w d) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspecl_then [`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK raw` >>
  `LENGTH (emitted_insts st ready) + s.vs_inst_idx =
    LENGTH ready.cs_current_insts` by fs[inst_extends_def] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op raw = eval_operand op s` by
    (rpt strip_tac >> irule entry_element_setup_total_frame >>
     qexistsl_tac [`tv_abi_size tv`, `di`, `Var root`, `Var q`,
                    `type_memory_size tv`, `ops`, `ready`, `src`, `st`] >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  `raw.vs_current_bb = s.vs_current_bb` by
    (drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> simp[]) >>
  `dec_info_needs_offset di = tv_abi_dynamic tv` by
    metis_tac[calldataSourceDecisionsTheory.calldata_coherent_offset] >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH ready.cs_current_insts`, `HG`, `u`, `child`] >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def, none_array_member_word,
     abi_decoder_address_frame_def] >> metis_tac[]
QED

(* The header changes only its four test registers. In particular the source
   address is still a word, not an assumed nonwrapping natural address. *)
Theorem none_array_true_header[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts id (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\ src <> Var iv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME srcaddr /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w cnt /\
  j < cnt /\ cnt < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  fresh_vars_wrt limit s /\
  (!x. MEM x [iv;cv;cmp;done] ==>
    ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
  ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 0 /\
    fresh_vars_wrt limit t /\ entry_decoder_obs s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    mload slot t = n2w j /\ ptr_covers H u q t 32 /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u))
Proof
  strip_tac >>
  `j <= cnt` by decide_tac >>
  drule_all decoder_index_header_ptr_core_uniform_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t = jump_to body_lbl (abi_decode_header_state iv cv cmp done j cnt s)` by fs[] >>
  drule_all decoder_index_header_replay_frame >> strip_tac >>
  drule calldata_header_owned_state >>
  disch_then (qspecl_then [`ARB`,`fn`,`ctx`] strip_assume_tac) >>
  `entry_decoder_obs s t` by simp[abi_decode_header_state_def] >>
  `~t.vs_halted /\ t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 0` by
    simp[abi_decode_header_state_def, jump_to_def, update_var_def] >>
  qexistsl_tac [`t`,`H`,`u`] >> simp[]
QED

Theorem none_array_backedge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ q <> nv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < cnt /\ cnt < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  fresh_vars_wrt limit s /\ nv = STRING #"%" (toString k) /\ k < limit.cs_next_var
  ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    fresh_vars_wrt limit t /\ entry_decoder_obs s t /\
    abi_decode_footprint_frame [(slot,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    mload slot t = n2w (SUC j) /\ ptr_covers H u q t 32 /\
    DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. x <> nv ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u))
Proof
  strip_tac >>
  `DISJOINT {} tn.t_mem` by simp[] >>
  drule_all decoder_index_backedge_ptr_core_uniform_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all decoder_index_backedge_replay_frame >> strip_tac >>
  drule calldata_backedge_owned_state >>
  disch_then (qspecl_then [`ARB`,`fn`,`ctx`] strip_assume_tac) >>
  `entry_decoder_obs s t` by simp[] >>
  `~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  `abi_decode_footprint_frame [(slot,32)] s t` by
    (simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def,
          IgnAsm `t = jump_to _ _`] >> metis_tac[ADD_COMM]) >>
  qexistsl_tac [`t`,`H`,`u`] >> simp[]
QED

Theorem none_array_member_pointer_range[local]:
  w2n (n2w (cd_member_ptr F cd tv (cd_at F sb 32) ofs) : bytes32) =
  cd_member_ptr F cd tv (cd_at F sb 32) ofs
Proof
  Cases_on `tv_abi_dynamic tv` >>
  simp[w2n_n2w, cd_member_ptr_def, cd_at_def, LET_THM]
QED

Theorem none_array_iteration_paths:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) (type_to_abi_dec_info sf ce ty)
    (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_has_code ready last fn /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD
    (Lit 0w) (Lit 0w) (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_inst_ids_distinct fn /\
  (last.cs_current_insts = [] ==> phi_prefix_length back_bb.bb_instructions = 0) /\
  ready.cs_next_var <= last.cs_next_var /\ last.cs_next_var < limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  hdr_bb.bb_instructions =
    abi_decode_header_insts hid (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\ phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  st.cs_current_bb = body_lbl /\ st.cs_current_insts = [] /\
  lookup_block last.cs_current_bb fn.fn_blocks = SOME back_bb /\ FST ops = Var ix /\
  back_bb.bb_instructions = last.cs_current_insts ++
      abi_decode_backedge_insts last.cs_next_id ix nv (Var q) hdr /\
  nv = STRING #"%" (toString last.cs_next_var) /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\
  (!x. MEM x [iv;cv;cmp;done] ==>
    ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var) /\
  q IN protect /\ root IN protect /\ (!x. src = Var x ==> x IN protect) /\
  (!x. x IN protect ==> not_fresh_at st x /\ not_fresh_at ready x /\
      ~MEM x [iv;cv;cmp;done] /\ x <> nv) /\
  abi_decoder_operand_live st.cs_next_var src /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
  lookup_var root s = SOME (n2w d) /\ eval_operand src s = SOME (n2w sb) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w cnt /\
  j < cnt /\ cnt < dimword (:256) /\
  ptr_covers G tn q s 32 /\ ptr_covers G tn root s cap /\
  DISJOINT {x | slot <= x /\ x < slot+32} tn.t_mem /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  32+j*type_memory_size tv+type_memory_size tv <= cap /\
  d+cap < dimword (:256) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  FLOOKUP s.vs_allocas counter_id = SOME (slot,32) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
  counter_id <> oid /\ base_addr <= d /\ d+cap <= base_addr+owner_cap /\
  (counter_id < ready.cs_next_id \/ last.cs_next_id <= counter_id) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  (!id p k. ready.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  (!a A ta child.
    SND (SND ops) = Var child /\
    eval_operand (FST (SND ops)) a = SOME (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F sb 32) (j*tv_abi_size tv))) /\
    lookup_var child a = SOME (n2w (d+32+j*type_memory_size tv)) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (Var child) /\
    ptr_covers A ta child a (type_memory_size tv) /\
    op_taint ta (FST (SND ops)) = {} /\ op_prov A (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit a /\ entry_decoder_obs s a /\
    a.vs_allocas = s.vs_allocas /\ a.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv a /\ alloca_frontier_inv ctx fn site a /\ allocas_from lo a /\
    ~a.vs_halted /\ a.vs_current_bb = ready.cs_current_bb /\
    a.vs_inst_idx = LENGTH ready.cs_current_insts ==>
    (?z Z tz. z.vs_returndata = [] /\
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (a,A,ta) [] (Abort Revert_abort z,Z,tz)) \/
    ?r R tr scratch.
      IS_SOME (cd_decode F a.vs_call_ctx.cc_calldata tv
        (w2n (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
          (cd_at F sb 32) (j*tv_abi_size tv)):bytes32))) /\
      ~r.vs_halted /\ r.vs_current_bb = last.cs_current_bb /\
      r.vs_inst_idx = LENGTH last.cs_current_insts /\
      fresh_vars_wrt limit r /\
      r.vs_call_ctx = a.vs_call_ctx /\ r.vs_data_section = a.vs_data_section /\
      alloca_inv r /\ alloca_frontier_inv ctx fn site r /\ allocas_from lo r /\
      a.vs_alloca_next <= r.vs_alloca_next /\
      (!id p k. FLOOKUP a.vs_allocas id = SOME (p,k) ==> FLOOKUP r.vs_allocas id = SOME (p,k)) /\
      (!id. id < ready.cs_next_id \/ last.cs_next_id <= id ==>
        FLOOKUP r.vs_allocas id = FLOOKUP a.vs_allocas id) /\
      (!id p k. ready.cs_next_id <= id /\ id < last.cs_next_id /\
        FLOOKUP r.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      abi_decode_footprint_frame ((d+32+j*type_memory_size tv,type_memory_size tv)::scratch) a r /\
      (!p k. MEM (p,k) scratch ==> ?id. ready.cs_next_id <= id /\ id < last.cs_next_id /\
        FLOOKUP r.vs_allocas id = SOME (p,k)) /\
      (!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op r = eval_operand op a) /\
      (!x. not_fresh_at ready x ==> FLOOKUP R x = FLOOKUP A x /\
        op_taint tr (Var x) = op_taint ta (Var x)) /\
      tr.t_mem SUBSET ta.t_mem /\ tr.t_stor = ta.t_stor /\ tr.t_trans = ta.t_trans /\ tr.t_imm = ta.t_imm /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (a,A,ta) [] (OK r,R,tr)))
  ==>
  (?z Z tz. z.vs_returndata = [] /\
     !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (Abort Revert_abort z,Z,tz)) \/
  ?t H u scratch.
    IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F sb 32) (j*tv_abi_size tv))) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    fresh_vars_wrt limit t /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    mload slot t = n2w (SUC j) /\ ptr_covers H u q t 32 /\ ptr_covers H u root t cap /\
    DISJOINT {x | slot <= x /\ x < slot+32} u.t_mem /\
    (!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==> FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < ready.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id p k. ready.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    abi_decode_footprint_frame ((d+32+j*type_memory_size tv,type_memory_size tv)::(slot,32)::scratch) s t /\
    (!p k. MEM (p,k) scratch ==> ?id. ready.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!x. x IN protect ==> lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hdr_bb` by simp[] >>
  `!x. src = Var x ==> ~MEM x [iv;cv;cmp;done]` by metis_tac[] >>
  `src <> Var iv` by (strip_tac >> fs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  mp_tac (Q.INST [`bb` |-> `hdr_bb`, `id` |-> `hid`,
                 `srcaddr` |-> `n2w sb`] none_array_true_header) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `t.vs_current_bb = body_lbl` >>
  `!x. x IN protect ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. ~MEM x [iv;cv;cmp;done] ==> lookup_var x t = _ /\ _`
       (qspec_then `x` MATCH_MP_TAC) >>
     qpat_assum `!x. x IN protect ==> not_fresh_at st x /\ _`
       (qspec_then `x` (fn frame =>
         qpat_assum `x IN protect`
           (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o MATCH_MP frame)))) >>
  `t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `entry_decoder_obs s t` mp_tac >> simp[NoAsms, entry_decoder_obs_def]) >>
  `eval_operand src t = SOME (n2w sb) /\ op_taint u src = {} /\ op_prov H src = NONE` by
    (qpat_assum `t.vs_labels = s.vs_labels` mp_tac >>
     qpat_assum `eval_operand src s = _` mp_tac >>
     qpat_assum `op_taint tn src = _` mp_tac >>
     qpat_assum `op_prov G src = _` mp_tac >>
     qpat_assum `!x. src = Var x ==> x IN protect` mp_tac >>
     qpat_assum `!x. x IN protect ==> lookup_var x t = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `src` >>
     simp[eval_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  `ptr_covers H u root t cap` by metis_tac[ptr_covers_frame] >>
  `lookup_var q t = SOME (n2w slot) /\ lookup_var root t = SOME (n2w d) /\
   not_fresh_at st q /\ not_fresh_at st root /\
   (!x. src = Var x ==> not_fresh_at st x)` by
    (qpat_assum `!x. x IN protect ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `!x. x IN protect ==> not_fresh_at st x /\ _` mp_tac >>
     qpat_assum `!x. src = Var x ==> x IN protect` mp_tac >>
     qpat_assum `lookup_var q s = _` mp_tac >>
     qpat_assum `lookup_var root s = _` mp_tac >>
     qpat_assum `q IN protect` mp_tac >> qpat_assum `root IN protect` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `abi_decoder_operand_live st.cs_next_var (Var root)` by simp[calldata_operand_live_not_fresh] >>
  `j < dimword (:256) /\ ready.cs_next_var <= limit.cs_next_var /\
   d+32+j*type_memory_size tv < dimword (:256) /\ type_memory_size tv < dimword (:256)` by decide_tac >>
  `slot+32 <= t.vs_alloca_next /\ t.vs_current_bb = st.cs_current_bb /\
   t.vs_inst_idx = LENGTH st.cs_current_insts /\
   (!a. slot <= a /\ a < slot+32 ==> a NOTIN u.t_mem)` by
    (asm_rewrite_tac[LENGTH] >>
     qpat_assum `DISJOINT _ tn.t_mem` mp_tac >>
     simp[NoAsms, DISJOINT_ALT]) >>
  mp_tac (Q.INST [`s` |-> `t`, `G` |-> `H`, `tn` |-> `u`,
                 `di` |-> `type_to_abi_dec_info sf ce ty`] none_array_element_setup) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `entry_decoder_obs t a` >>
  rename1 `ptr_covers A ta child a (type_memory_size tv)` >>
  `allocas_from lo t /\ allocas_from lo a` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `entry_decoder_obs s a /\ alloca_inv a /\ alloca_frontier_inv ctx fn site a` by
    (conj_tac
     >- (irule entry_decoder_obs_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
     conj_tac
     >- (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `a`] calldata_alloca_inv_fields) >>
         asm_rewrite_tac[]) >>
     mp_tac (Q.INST [`s` |-> `s`, `t` |-> `a`] calldata_alloca_frontier_inv_fields) >>
     asm_rewrite_tac[]) >>
  `lookup_var child a = SOME (n2w (d+32+j*type_memory_size tv)) /\
   abi_decoder_operand_live ready.cs_next_var (Var child)` by
    (qpat_x_assum `eval_operand (SND (SND ops)) a = _` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live ready.cs_next_var (SND (SND ops))` mp_tac >>
     asm_rewrite_tac[eval_operand_def] >> simp[NoAsms]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by simp[] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK a,A,ta)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`H`,`t`,`u`] >> metis_tac[]) >>
  qpat_x_assum `!a A ta child. SND (SND ops) = Var child /\ _ ==> _`
    (qspecl_then [`a`,`A`,`ta`,`child`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> strip_tac
  >- (disj1_tac >> rename1 `z.vs_returndata = []` >>
      qexistsl_tac [`z`,`Z`,`tz`] >> asm_rewrite_tac[] >>
      rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`A`,`a`,`ta`] >> metis_tac[]) >>
  disj2_tac >>
  rename1 `r.vs_call_ctx = a.vs_call_ctx` >>
  rename1 `tr.t_mem SUBSET ta.t_mem` >>
  rename1 `gas_origin_ptr_path _ (a,A,ta) [] (OK r,R,tr)` >>
  (Q.SUBGOAL_THEN `slot+32 <= d+32+j*type_memory_size tv \/
                    d+32+j*type_memory_size tv+type_memory_size tv <= slot` assume_tac
   >- (`oid <> counter_id` by metis_tac[] >>
       qpat_assum `alloca_inv s` mp_tac >>
       pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def,
                        venomMemDefsTheory.allocas_non_overlapping_def] >>
       disch_then (mp_tac o CONJUNCT1) >>
       disch_then (qspecl_then [`oid`,`counter_id`,`base_addr`,`owner_cap`,`slot`,`32`] mp_tac) >>
       asm_rewrite_tac[] >> decide_tac)) >>
  `mload slot a = n2w j` by
    (qpat_assum `mload slot s = _` (fn th =>
       asm_rewrite_tac[mload_def, REWRITE_RULE[mload_def] th])) >>
  `mload slot r = n2w j` by
    (mp_tac (Q.INST [`s` |-> `a`, `t` |-> `r`, `lo` |-> `ready.cs_next_id`,
                    `hi` |-> `last.cs_next_id`, `counter` |-> `slot`,
                    `d` |-> `d+32+j*type_memory_size tv`,
                    `sz` |-> `type_memory_size tv`] calldata_child_preserves_counter) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >> asm_rewrite_tac[]) >>
  `!x. x IN protect ==> lookup_var x r = lookup_var x s /\
      FLOOKUP R x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at st x /\ not_fresh_at ready x` by metis_tac[] >>
     `lookup_var x a = lookup_var x t /\ lookup_var x r = lookup_var x a` by
       metis_tac[calldata_operand_live_not_fresh, eval_operand_def] >>
     metis_tac[]) >>
  `ptr_covers R tr q r 32 /\ lookup_var q r = SOME (n2w slot) /\
   q <> nv /\ ptr_covers R tr root r cap` by
    (qpat_assum `!x. x IN protect ==> lookup_var x r = _ /\ _`
       (fn frame =>
         qpat_assum `q IN protect`
           (strip_assume_tac o MATCH_MP (Q.SPEC `q` frame)) >>
         qpat_assum `root IN protect`
           (strip_assume_tac o MATCH_MP (Q.SPEC `root` frame))) >>
     conj_tac
     >- (mp_tac (Q.INST [`p` |-> `q`, `n` |-> `32`, `H` |-> `R`, `u` |-> `tr`, `t` |-> `r`]
            ptr_covers_frame) >> asm_rewrite_tac[]) >>
     conj_tac >- asm_rewrite_tac[] >>
     conj_tac
     >- (qpat_assum `!x. x IN protect ==> not_fresh_at st x /\ _`
           (qspec_then `q` (fn frame =>
             qpat_assum `q IN protect` (strip_assume_tac o MATCH_MP frame))) >>
         qpat_assum `q <> nv` ACCEPT_TAC) >>
     mp_tac (Q.INST [`p` |-> `root`, `n` |-> `cap`, `H` |-> `R`, `u` |-> `tr`, `t` |-> `r`]
       ptr_covers_frame) >> asm_rewrite_tac[]) >>
  `eval_operand (Var ix) r = SOME (n2w j) /\
   op_taint tr (Var ix) = {} /\ op_prov R (Var ix) = NONE` by
    (`abi_decoder_operand_live ready.cs_next_var (Var ix) /\
       eval_operand (Var ix) a = SOME (n2w j) /\ op_taint ta (Var ix) = {} /\
       op_prov A (Var ix) = NONE` by metis_tac[] >>
     `not_fresh_at ready ix` by asm_rewrite_tac[GSYM calldata_operand_live_not_fresh] >>
     qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> _`
       (qspec_then `Var ix` drule) >> disch_tac >>
     qpat_assum `!x. not_fresh_at ready x ==> FLOOKUP R x = _ /\ _`
       (qspec_then `ix` drule) >> strip_tac >>
     asm_rewrite_tac[] >>
     qpat_assum `op_prov A (Var ix) = NONE` (mp_tac o SRULE[op_prov_def]) >>
     simp[NoAsms, op_prov_def] >> asm_rewrite_tac[]) >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME back_bb /\
   slot+32 <= r.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by simp[] >>
  mp_tac (Q.INST [`s` |-> `r`, `G` |-> `R`, `tn` |-> `tr`, `bb` |-> `back_bb`,
                 `id` |-> `last.cs_next_id`, `prefix` |-> `last.cs_current_insts`,
                 `iv` |-> `ix`, `k` |-> `last.cs_next_var`] none_array_backedge) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `entry_decoder_obs r b` >>
  rename1 `gas_origin_ptr_path _ (r,R,tr) [] (OK b,B,tb)` >>
  `a.vs_call_ctx = s.vs_call_ctx /\ a.vs_data_section = s.vs_data_section` by
    (qpat_assum `entry_decoder_obs s a` mp_tac >> simp[NoAsms, entry_decoder_obs_def]) >>
  `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv
      (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (cd_at F sb 32) (j*tv_abi_size tv)))` by
    (qpat_x_assum `IS_SOME (cd_decode F _ tv _)` mp_tac >>
     asm_rewrite_tac[none_array_member_pointer_range]) >>
  `b.vs_call_ctx = s.vs_call_ctx /\ b.vs_data_section = s.vs_data_section` by
    (qpat_assum `entry_decoder_obs r b` mp_tac >>
     simp[NoAsms, entry_decoder_obs_def] >> asm_rewrite_tac[]) >>
  `alloca_inv b /\ alloca_frontier_inv ctx fn site b` by
    metis_tac[calldata_alloca_inv_fields, calldata_alloca_frontier_inv_fields] >>
  `allocas_from lo b` by
    (qpat_assum `allocas_from lo r` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `s.vs_alloca_next <= b.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
  `!x. x IN protect ==> lookup_var x b = lookup_var x s /\
      FLOOKUP B x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `ptr_covers B tb root b cap` by metis_tac[ptr_covers_frame] >>
  qexistsl_tac [`b`,`B`,`tb`,`scratch`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `!id p k. FLOOKUP a.vs_allocas id = SOME (p,k) ==> _` mp_tac >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (qpat_x_assum `!id. _ ==> FLOOKUP r.vs_allocas id = FLOOKUP a.vs_allocas id` mp_tac >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (qmatch_goalsub_abbrev_tac `abi_decode_footprint_frame ((e,_)::_) s b` >>
      `abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) s r` by
        (qpat_assum `abi_decode_footprint_frame ((e,_)::scratch) a r` mp_tac >>
         pure_rewrite_tac[abi_decode_footprint_frame_def] >> asm_rewrite_tac[]) >>
      irule abi_decode_footprint_frame_trans >> qexists_tac `r` >> conj_tac
      >- (irule abi_decode_footprint_frame_weaken >>
          qexists_tac `(e,type_memory_size tv)::scratch` >> asm_rewrite_tac[] >>
          rpt gen_tac >> disch_tac >> rename1 `MEM (p,n) _` >>
          qexistsl_tac [`p`,`n`] >> simp[NoAsms] >>
          qpat_assum `MEM (p,n) ((e,_)::scratch)` mp_tac >> simp[NoAsms] >> strip_tac >> asm_rewrite_tac[]) >>
      irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
      asm_rewrite_tac[] >> simp[NoAsms] >>
      rpt strip_tac >> qexistsl_tac [`slot`,`32`] >> asm_rewrite_tac[] >> simp[NoAsms]) >>
  conj_tac
  >- (irule SUBSET_TRANS >> qexists_tac `tr.t_mem` >> asm_rewrite_tac[] >>
      qpat_x_assum `tr.t_mem SUBSET ta.t_mem` mp_tac >> asm_rewrite_tac[]) >>
  rpt gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`R`,`r`,`tr`] >> conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`A`,`a`,`ta`] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED
