(* Source-exact transition of an installed nonbulk array loop. *)
Theory selectedAcceptedArrayStep
Ancestors
  selectedAcceptedInterfaces calldataArrayRawCallsite calldataMemberResourceFrame
  decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr robustCopyTransportPtr
  fragGasOriginPtrExec vyperCalldataProps vyperCalldata words arithmetic
  calldataSourceCorrespondence calldataDynStep decoderArraySetupPtr
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderExecution
  entryDecoderSetupEndpoint entryDecoderStateFrame calldataFiniteTransport
  compileEnv venomState venomExecSemantics abiDecoderFrame fragGasOriginPtr
  exprLoweringProps loweringStateRelDefs ptrDiscipline abiDecoderReentry
  codegenRel instIdxIndep emitHelperProps abiEncoder finite_map pred_set list
  bodyPtrDefs venomInst abiDecoderContract

(* The index computation is word arithmetic even when the ABI head wraps. *)
Theorem selected_array_source_word:
  (if tv_abi_dynamic tv then
    n2w (sb + 32 + w2n (abi_decode_load CALLDATALOAD
      (n2w (sb + 32 + ofs) : bytes32) s))
   else n2w (sb + 32 + ofs)) =
  (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
    (cd_at F (w2n (n2w sb:bytes32)) 32) ofs) : bytes32)
Proof
  Cases_on `tv_abi_dynamic tv` >>
  simp[cd_member_ptr_def, cd_at_def, w2n_n2w, MOD_PLUS, calldata_decode_load_word]
QED

Theorem selected_array_source_cons:
  cd_decode_elems F cd tv b i (SUC n) = SOME xs ==>
  ?x rest. xs = x::rest /\
    cd_decode F cd tv (cd_member_ptr F cd tv b (i*tv_abi_size tv)) = SOME x /\
    cd_decode_elems F cd tv b (SUC i) n = SOME rest
Proof
  simp[Once cd_decode_def, AllCaseEqs(), ADD1] >> metis_tac[]
QED

(* The body setup runs at the installed cursor; its source need not be a
   nonwrapping ABI header and the cnter can be a replay allocation. *)
Theorem selected_array_setup[local]:
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  dec_info_needs_offset di = tv_abi_dynamic tv /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ j < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ lookup_var root s = SOME (n2w d) /\
  ptr_covers G tn q s 32 /\ ptr_covers G tn root s span /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  not_fresh_at st q /\ not_fresh_at st root /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  32+j*type_memory_size tv+type_memory_size tv <= span /\
  d+32+j*type_memory_size tv < dimword (:256) /\ type_memory_size tv < dimword (:256) /\
  ready.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code st ready fn /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a H u child.
    ~a.vs_halted /\ a.vs_current_bb = ready.cs_current_bb /\
    a.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) a = SOME (n2w j) /\
    eval_operand (FST (SND ops)) a = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F (w2n (n2w sb:bytes32)) 32) (j*tv_abi_size tv))) /\
    eval_operand (Var child) a = SOME (n2w (d+32+j*type_memory_size tv)) /\
    SND (SND ops) = Var child /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (Var child) /\
    ptr_covers H u child a (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit a /\ entry_decoder_obs s a /\
    a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
    a.vs_alloca_next = s.vs_alloca_next /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op a = eval_operand op s) /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,H,u))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w d) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK raw` >>
  `LENGTH (emitted_insts st ready) + s.vs_inst_idx =
    LENGTH ready.cs_current_insts` by fs[inst_extends_def] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op raw = eval_operand op s` by
    (rpt strip_tac >> drule_all entry_element_setup_total_frame >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH ready.cs_current_insts`, `HG`, `u`, `child`] >>
  pure_once_rewrite_tac [GSYM selected_array_source_word] >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def]
QED

Theorem selected_array_header[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts hid (Var q) src CALLDATALOAD hv cv cmp dn body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;hv;cv;cmp;dn] /\ src <> Var hv /\
  lookup_var q s = SOME (n2w slot) /\ ptr_covers G tn q s 32 /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD (n2w sb:bytes32) s = n2w cnt /\ j < cnt /\
  cnt < dimword (:256) /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\ fresh_vars_wrt limit s /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ?k. x = STRING #"%" (toString k) /\
    k < limit.cs_next_var) ==>
  ?b H u.
    ~b.vs_halted /\ b.vs_current_bb = body_lbl /\ b.vs_inst_idx = 0 /\
    b.vs_memory = s.vs_memory /\ b.vs_allocas = s.vs_allocas /\
    b.vs_alloca_next = s.vs_alloca_next /\ entry_decoder_obs s b /\
    fresh_vars_wrt limit b /\ ptr_covers H u q b 32 /\ mload slot b = n2w j /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\
    (!x. ~MEM x [hv;cv;cmp;dn] ==>
      lookup_var x b = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK b,H,u))
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `lower`, `id` |-> `hid`, `iv` |-> `hv`,
    `done` |-> `dn`, `ncount` |-> `cnt`, `srcaddr` |-> `n2w sb`]
    (SPEC_ALL decoder_index_header_ptr_core_uniform_origin)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`t`, `H`, `u`] >>
  `fresh_vars_wrt limit (abi_decode_header_state hv cv cmp dn j cnt s)` by
    (rewrite_tac[abi_decode_header_state_def, LET_THM] >>
     qpat_x_assum `!x. MEM x [hv;cv;cmp;dn] ==> ?k. _`
       (fn th => map_every (fn v => qspec_then v mp_tac th) [`hv`,`cv`,`cmp`,`dn`]) >>
     simp[] >> rpt strip_tac >> metis_tac[fresh_vars_wrt_update_var]) >>
  `entry_decoder_obs s (abi_decode_header_state hv cv cmp dn j cnt s)` by
    simp[abi_decode_header_state_def] >>
  gvs[] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def, fresh_vars_wrt_def]
QED

(* The address produced by the setup is already reduced in the source
   semantics. Recasting it as a word therefore reads exactly that cell. *)
Theorem selected_array_member_word[local]:
  w2n (n2w (cd_member_ptr F cd tv b ofs) : bytes32) =
  cd_member_ptr F cd tv b ofs
Proof
  simp[cd_member_ptr_def, cd_at_def] >> Cases_on `tv_abi_dynamic tv` >> simp[]
QED

Theorem selected_array_child[local]:
  selected_decoder_accepts ce env sf ty tv /\
  abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf (Var child) (FST (SND ops)) CALLDATALOAD
    (Lit 0w) (Lit 0w) (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_has_code ready last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\ unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand (FST (SND ops)) a = SOME (n2w (cd_member_ptr F cd tv b (j*tv_abi_size tv))) /\
  eval_operand (Var child) a = SOME (n2w e) /\
  abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live ready.cs_next_var (Var child) /\
  alloca_inv a /\ alloca_frontier_inv ctx fn site a /\
  calldata_member_own fn L H a /\ L <= ready.cs_next_id /\ last.cs_next_id <= H /\
  FLOOKUP a.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
  e+type_memory_size tv < dimword (:256) /\
  ptr_covers Ga ta child a (type_memory_size tv) /\
  op_taint ta (FST (SND ops)) = {} /\ op_prov Ga (FST (SND ops)) = NONE /\
  fresh_vars_wrt limit a /\ allocas_from lower a /\
  lower <= a.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~a.vs_halted /\ a.vs_current_bb = ready.cs_current_bb /\
  a.vs_inst_idx = LENGTH ready.cs_current_insts /\
  cd = a.vs_call_ctx.cc_calldata /\
  cd_decode_elems F cd tv b j (SUC n) = SOME xs ==>
  ?x rest v sc Gv tvn.
    xs = x::rest /\ cd_decode_elems F cd tv b (SUC j) n = SOME rest /\
    cd_decode F cd tv (cd_member_ptr F cd tv b (j*tv_abi_size tv)) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    value_has_type tv x /\ val_wf tv x /\
    (!mem. mem_agree_outside tvn.t_mem v.vs_memory mem ==> val_in_memory tv x e mem) /\
    calldata_member_resource_frame ctx fn site limit ready.cs_next_id last.cs_next_id
      ready.cs_next_var e (type_memory_size tv) a v sc /\
    v.vs_code = a.vs_code /\ v.vs_accounts = a.vs_accounts /\
    v.vs_transient = a.vs_transient /\ v.vs_logs = a.vs_logs /\
    v.vs_outcomes = a.vs_outcomes /\ v.vs_requests = a.vs_requests /\
    v.vs_pending_deletions = a.vs_pending_deletions /\
    v.vs_tx_ctx = a.vs_tx_ctx /\ v.vs_block_ctx = a.vs_block_ctx /\
    v.vs_fmp = a.vs_fmp /\ v.vs_gas_readings = a.vs_gas_readings /\
    allocas_from lower v /\
    (!name. not_fresh_at ready name ==> FLOOKUP Gv name = FLOOKUP Ga name /\
      op_taint tvn (Var name) = op_taint ta (Var name)) /\
    tvn.t_mem SUBSET ta.t_mem /\ tvn.t_stor = ta.t_stor /\
    tvn.t_trans = ta.t_trans /\ tvn.t_imm = ta.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (a,Ga,ta) [] (OK v,Gv,tvn))
Proof
  strip_tac >> drule selected_array_source_cons >> strip_tac >>
  `calldata_member_own fn ready.cs_next_id last.cs_next_id a` by
    (irule calldata_member_own_nested >> metis_tac[]) >>
  qpat_x_assum `selected_decoder_accepts _ _ _ _ _`
    (mp_tac o REWRITE_RULE [selected_decoder_accepts_def]) >>
  disch_then (qspecl_then [`ready`,`last`,`limit`,`ctx`,`fn`,`site`,
    `FST (SND ops)`,`child`,`a`,`n2w (cd_member_ptr F cd tv b (j*tv_abi_size tv))`,
    `e`,`oid`,`base_addr`,`cap`,`Ga`,`ta`,`lower`,`PG`,`x`] mp_tac) >>
  (impl_tac >- gvs[GSYM calldata_member_own_def, selected_array_member_word]) >>
  strip_tac >> rename1 `abi_decode_footprint_frame _ a v` >>
  rename1 `gas_origin_ptr_path _ (a,Ga,ta) [] (OK v,Gv,tvn)` >>
  qexistsl_tac [`x`,`rest`,`v`,`sc`,`Gv`,`tvn`] >>
  asm_rewrite_tac[calldata_member_resource_frame_def, calldata_member_own_def,
    calldata_member_wit_def, op_taint_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
