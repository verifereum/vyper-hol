(* Source-exact transition of an installed nonbulk array loop. *)
Theory selectedAcceptedArrayStep
Ancestors
  selectedAcceptedInterfaces calldataArrayRawCallsite calldataMemberResourceFrame
  decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr robustCopyTransportPtr
  sourceArrayHeaderOriginPtr sourceArrayBackedgeOriginPtr
  fragGasOriginPtrExec vyperCalldataProps vyperCalldata words arithmetic
  calldataSourceCorrespondence calldataDynStep decoderArraySetupPtr
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderExecution
  entryDecoderSetupEndpoint entryDecoderStateFrame calldataFiniteTransport
  compileEnv venomState venomExecSemantics abiDecoderFrame fragGasOriginPtr
  exprLoweringProps loweringStateRelDefs ptrDiscipline abiDecoderReentry
  codegenRel instIdxIndep emitHelperProps abiEncoder finite_map pred_set list
  bodyPtrDefs venomInst abiDecoderContract calldataDynOwned valueEncodingProps exprSimProps

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
    (!x. not_fresh_at st x ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,H,u))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w d) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core_exact_frame >>
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
    (!x. ~MEM x [hv;cv;cmp;dn] ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK b,H,u))
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `lower`, `id` |-> `hid`, `iv` |-> `hv`,
    `done` |-> `dn`, `ncount` |-> `cnt`, `srcaddr` |-> `n2w sb`]
    (SPEC_ALL source_array_header_origin_ptr_exact_frame)) >>
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
  compile_abi_decode_to_buf (Var child) (FST (SND (ops:operand # operand # operand))) CALLDATALOAD
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
    (!name. not_fresh_at ready name ==> FLOOKUP tvn.t_var name = FLOOKUP ta.t_var name) /\
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
  rpt strip_tac >>
  qpat_assum `!name. not_fresh_at ready name ==> _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

(* Separate the owned counter write from the child footprint. *)
Theorem selected_array_backedge[local]:
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  v.vs_inst_idx = LENGTH prefix /\ ~v.vs_halted /\ q <> nv /\
  ptr_covers G tn q v 32 /\ lookup_var q v = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= v.vs_alloca_next /\
  eval_operand (Var iv) v = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < cnt /\ cnt < dimword (:256) /\
  allocas_from lower v /\ ~ctx_has_dalloca ctx /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  fresh_vars_wrt limit v /\ nv = STRING #"%" (toString k) /\ k < limit.cs_next_var /\
  alloca_inv v /\ alloca_frontier_inv ctx fn site v /\ calldata_member_own fn L H v /\
  L <= counter_id /\ counter_id < H /\ FLOOKUP v.vs_allocas counter_id = SOME (slot,32) /\
  ~abi_decoder_operand_live live (Var nv) ==>
  ?t Gt tt.
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    entry_decoder_obs v t /\ allocas_from lower t /\
    calldata_member_resource_frame ctx fn site limit L H live d span v t [(slot,32)] /\
    t.vs_allocas = v.vs_allocas /\ t.vs_alloca_next = v.vs_alloca_next /\
    ptr_covers Gt tt q t 32 /\ mload slot t = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot+32} tt.t_mem /\
    tt.t_mem SUBSET tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. x <> nv ==> lookup_var x t = lookup_var x v /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!x. x <> nv ==> FLOOKUP tt.t_var x = FLOOKUP tn.t_var x) /\
    (!a n. a+n <= slot \/ slot+32 <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n v.vs_memory) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (v,G,tn) [] (OK t,Gt,tt))
Proof
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `v`, `lo` |-> `lower`, `P` |-> `{}`, `ncount` |-> `cnt`]
    (SPEC_ALL source_array_backedge_origin_ptr_exact_frame)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `t = jump_to hdr _` >>
  drule_all decoder_index_backedge_replay_frame >> strip_tac >>
  drule calldata_backedge_owned_state >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ entry_decoder_obs v t` by
    (conj_tac >- simp[jump_to_def, mstore_def, update_var_def] >>
     simp[entry_decoder_obs_def, jump_to_def, mstore_def, update_var_def]) >>
  `allocas_from lower t` by
    (rewrite_tac[allocas_from_def] >> asm_rewrite_tac[] >>
     asm_rewrite_tac[GSYM allocas_from_def]) >>
  `calldata_member_own fn L H t` by
    (rewrite_tac[calldata_member_own_def] >> asm_rewrite_tac[] >>
     asm_rewrite_tac[GSYM calldata_member_own_def]) >>
  `calldata_member_wit L H t [(slot,32)]` by
    (simp[calldata_member_wit_def] >> qexists_tac `counter_id` >> simp[]) >>
  `!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op v` by
    (rpt strip_tac >> `op <> Var nv` by (strip_tac >> fs[]) >> simp[]) >>
  `abi_decode_footprint_frame [(d,span);(slot,32)] v t` by
    (rewrite_tac[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     rpt strip_tac >> qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     qpat_x_assum `!d' sz. MEM _ _ ==> _` (qspecl_then [`slot`,`32`] mp_tac) >> simp[]) >>
  `calldata_member_resource_frame ctx fn site limit L H live d span v t [(slot,32)]` by
    (rewrite_tac[calldata_member_resource_frame_def] >>
     asm_rewrite_tac[LESS_EQ_REFL]) >>
  qexistsl_tac [`t`,`H'`,`u`] >>
  simp_tac bool_ss [] >> asm_rewrite_tac[]
  >> (gvs[])
QED

Theorem selected_array_robust_prefix[local]:
  EVERY (val_wf tv) xs /\ LENGTH xs = j /\ stride = type_memory_size tv /\
  mem_bytes_at d (32+j*stride) new = mem_bytes_at d (32+j*stride) old /\
  dirty' SUBSET dirty /\
  (!k. k < j ==> !mem. mem_agree_outside dirty old mem ==>
    val_in_memory tv (EL k xs) (d+32+k*stride) mem) ==>
  !k. k < j ==> !mem. mem_agree_outside dirty' new mem ==>
    val_in_memory tv (EL k xs) (d+32+k*stride) mem
Proof
  strip_tac >> qx_gen_tac `k` >> strip_tac >>
  `val_wf tv (EL k xs)` by metis_tac[EVERY_EL] >>
  `val_footprint tv (EL k xs) <= stride` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> irule calldata_member_robust_window_frame >>
  simp[] >> qexistsl_tac [`new`, `dirty'`, `old`, `dirty`] >> simp[] >>
  `SUC k * stride <= j * stride` by simp[] >>
  `32+k*stride+val_footprint tv (EL k xs) <= 32+j*stride` by
    (qpat_x_assum `SUC k * stride <= j * stride` mp_tac >>
     pure_rewrite_tac [MULT_CLAUSES] >> decide_tac) >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`32+k*stride`, `val_footprint tv (EL k xs)`] mp_tac) >>
  gvs[]
QED

(* Join the header branch to the cursor just before the child decoder. *)
Theorem selected_array_enter_child[local]:
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
  cnt < dimword (:256) /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  lookup_block st.cs_current_bb fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st.cs_current_insts = [] /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\ fresh_vars_wrt limit s /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ?k. x = STRING #"%" (toString k) /\
    k < limit.cs_next_var) /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  dec_info_needs_offset di = tv_abi_dynamic tv /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s span /\
  abi_decoder_operand_live live (Var q) /\ abi_decoder_operand_live live (Var root) /\
  abi_decoder_operand_live live src /\ live <= st.cs_next_var /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ~abi_decoder_operand_live live (Var x)) /\
  32+j*type_memory_size tv+type_memory_size tv <= span /\
  d+32+j*type_memory_size tv < dimword (:256) /\ type_memory_size tv < dimword (:256) /\
  ready.cs_next_var <= limit.cs_next_var /\ fn_has_code st ready fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn L H s ==>
  ?a Ga ta child.
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
    ptr_covers Ga ta child a (type_memory_size tv) /\
    op_taint ta (FST ops) = {} /\ op_prov Ga (FST ops) = NONE /\
    op_taint ta (FST (SND ops)) = {} /\ op_prov Ga (FST (SND ops)) = NONE /\
    entry_decoder_obs s a /\ allocas_from lower a /\
    a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
    a.vs_alloca_next = s.vs_alloca_next /\
    calldata_member_resource_frame ctx fn site limit L H live d span s a [] /\
    (!x. abi_decoder_operand_live live (Var x) ==>
      FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x) /\
      FLOOKUP ta.t_var x = FLOOKUP tn.t_var x) /\
    ta.t_mem = tn.t_mem /\ ta.t_stor = tn.t_stor /\
    ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,Ga,ta))
Proof
  strip_tac >>
  `src <> Var hv` by (strip_tac >> fs[]) >>
  `!x. abi_decoder_operand_live live (Var x) ==> ~MEM x [hv;cv;cmp;dn]` by metis_tac[] >>
  drule_all selected_array_header >> disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `b.vs_current_bb = st.cs_current_bb` >>
  rename1 `ptr_covers Gb tb q b 32` >>
  `!op. abi_decoder_operand_live live op ==>
    eval_operand op b = eval_operand op s /\ op_taint tb op = op_taint tn op /\
    op_prov Gb op = op_prov G op` by
    (`b.vs_labels = s.vs_labels` by
       (qpat_assum `entry_decoder_obs s b` (strip_assume_tac o REWRITE_RULE [entry_decoder_obs_def]) >>
        first_assum ACCEPT_TAC) >>
     Cases >> simp[op_taint_def, op_prov_def, eval_operand_def] >>
     strip_tac >> rename1 `abi_decoder_operand_live live (Var x)` >>
     `~MEM x [hv;cv;cmp;dn]` by metis_tac[] >>
     qpat_assum `!x. ~MEM x _ ==> _` (qspec_then `x` mp_tac) >>
     asm_rewrite_tac[op_taint_def]) >>
  `allocas_from lower b` by
    (rewrite_tac[allocas_from_def] >> asm_rewrite_tac[] >>
     asm_rewrite_tac[GSYM allocas_from_def]) >>
  `lookup_var q b = SOME (n2w slot) /\ lookup_var root b = SOME (n2w d)` by metis_tac[] >>
  `ptr_covers Gb tb root b span` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `!op. abi_decoder_operand_live live op ==> abi_decoder_operand_live st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!x. abi_decoder_operand_live live (Var x) ==> not_fresh_at st x` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand src b = SOME (n2w sb) /\ op_taint tb src = {} /\ op_prov Gb src = NONE /\
   abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var (Var root) /\
   not_fresh_at st q /\ not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    metis_tac[] >>
  `!z. slot <= z /\ z < slot+32 ==> z NOTIN tb.t_mem` by
    (qpat_x_assum `DISJOINT _ _` mp_tac >> simp[DISJOINT_ALT]) >>
  `slot+32 <= b.vs_alloca_next /\ j < dimword (:256) /\
    b.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all selected_array_setup >> disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `a.vs_inst_idx = LENGTH ready.cs_current_insts` >>
  rename1 `ptr_covers Ga ta child a _` >>
  `entry_decoder_obs s a` by metis_tac[entry_decoder_obs_trans] >>
  `a.vs_call_ctx = s.vs_call_ctx /\ a.vs_data_section = s.vs_data_section` by
    (qpat_assum `entry_decoder_obs s a` (strip_assume_tac o REWRITE_RULE [entry_decoder_obs_def]) >>
     asm_rewrite_tac[]) >>
  `b.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `entry_decoder_obs s b` (strip_assume_tac o REWRITE_RULE [entry_decoder_obs_def]) >>
     first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live live op ==> eval_operand op a = eval_operand op s` by
    (rpt strip_tac >> qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `calldata_member_resource_frame ctx fn site limit L H live d span s a []` by
    (irule calldata_member_resource_unchanged >> simp[]) >>
  `allocas_from lower a` by
    (rewrite_tac[allocas_from_def] >> asm_rewrite_tac[] >>
     asm_rewrite_tac[GSYM allocas_from_def]) >>
  qexistsl_tac [`a`,`Ga`,`ta`,`child`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qx_gen_tac `name` >> strip_tac >>
      `not_fresh_at st name /\ ~MEM name [hv;cv;cmp;dn]` by simp[] >>
      asm_simp_tac bool_ss [])
  >> rpt gen_tac >>
  irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL gas_origin_ptr_path_append))) >>
  qexistsl_tac [`Gb`,`b`,`(OK b,Gb,tb)`,`tb`] >> simp[]
QED

(* The backedge may write its counter but not the array allocation. *)
Theorem selected_array_counter_disjoint[local]:
  alloca_inv v /\ counter_id <> oid /\
  FLOOKUP v.vs_allocas counter_id = SOME (slot,32) /\
  FLOOKUP v.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+n <= base_addr+cap ==>
  d+n <= slot \/ slot+32 <= d
Proof
  simp_tac bool_ss [venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def] >> strip_tac >>
  qpat_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`counter_id`,`oid`,`slot`,`32`,`base_addr`,`cap`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> decide_tac
QED

Theorem selected_array_extend_values[local]:
  LENGTH xs = j /\ EVERY (val_wf tv) xs /\ val_wf tv x /\
  stride = type_memory_size tv /\
  mem_bytes_at d (32+j*stride) new = mem_bytes_at d (32+j*stride) old /\
  mem_bytes_at (d+32+j*stride) stride new =
    mem_bytes_at (d+32+j*stride) stride mid /\
  clean SUBSET dirty /\ clean SUBSET middle /\
  (!k. k < j ==> !mem. mem_agree_outside dirty old mem ==>
    val_in_memory tv (EL k xs) (d+32+k*stride) mem) /\
  (!mem. mem_agree_outside middle mid mem ==>
    val_in_memory tv x (d+32+j*stride) mem) ==>
  !k. k < SUC j ==> !mem. mem_agree_outside clean new mem ==>
    val_in_memory tv (EL k (xs ++ [x])) (d+32+k*stride) mem
Proof
  strip_tac >>
  `!k. k < j ==> !mem. mem_agree_outside clean new mem ==>
    val_in_memory tv (EL k xs) (d+32+k*stride) mem` by
    (mp_tac (Q.INST [`dirty'` |-> `clean`] selected_array_robust_prefix) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at (d+32+j*stride) (val_footprint tv x) new =
   mem_bytes_at (d+32+j*stride) (val_footprint tv x) mid` by
    (qpat_assum `mem_bytes_at _ stride new = _` (mp_then Any mp_tac mem_bytes_at_translated_window) >>
     disch_then (qspecl_then [`0`,`val_footprint tv x`] mp_tac) >>
     simp[val_footprint_le]) >>
  qx_gen_tac `k` >> strip_tac >> Cases_on `k < j` >-
    (qpat_assum `!k. k < j ==> !mem. mem_agree_outside clean new mem ==> _`
       (qspec_then `k` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     gvs[EL_APPEND_EQN]) >>
  `k = j` by decide_tac >>
  `!mem. mem_agree_outside clean new mem ==>
    val_in_memory tv x (d+32+j*stride) mem` by
    (metis_tac[calldata_member_robust_window_frame]) >>
  gvs[EL_APPEND_EQN]
QED

(* One installed iteration, from the header to the same header.  The source
   cursor is modular; the destination cursor is contained in its real owner. *)
Theorem selected_array_iteration_with_frame:
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) /\
   d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
   d+32+j*type_memory_size tv < dimword (:256) /\ type_memory_size tv < dimword (:256)` by
    decide_tac >>
  mp_tac (SPEC_ALL selected_array_enter_child) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `a.vs_inst_idx = LENGTH ready.cs_current_insts` >>
  rename1 `ptr_covers Ga ta child a _` >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s a []`
    (strip_assume_tac o MATCH_MP calldata_member_resource_endpoint) >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s a []`
    (strip_assume_tac o MATCH_MP calldata_member_resource_observations) >>
  qpat_assum `!child. SND (SND ops) = Var child ==> _`
    (qspec_then `child` (fn th => qpat_assum `SND (SND ops) = Var child`
       (assume_tac o MP th))) >>
  mp_tac (Q.INST [`cd` |-> `s.vs_call_ctx.cc_calldata`,
      `b` |-> `cd_at F (w2n (n2w sb:bytes32)) 32`,
      `e` |-> `d+32+j*type_memory_size tv`, `xs` |-> `pending`]
    (SPEC_ALL selected_array_child)) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> strip_tac >>
  rename1 `v.vs_inst_idx = LENGTH last.cs_current_insts` >>
  rename1 `gas_origin_ptr_path _ (a,Ga,ta) [] (OK v,Gv,tvn)` >>
  `live <= ready.cs_next_var /\ d <= d+32+j*type_memory_size tv /\
   d+32+j*type_memory_size tv+type_memory_size tv <= d+span` by decide_tac >>
  `calldata_member_resource_frame ctx fn site limit L H live d span s v ([] ++ sc)` by
    (irule calldata_member_resource_extend >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s a []` (irule_at Any) >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ a v sc` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s v _`
    (strip_assume_tac o MATCH_MP calldata_member_resource_endpoint) >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s v _`
    (strip_assume_tac o MATCH_MP calldata_member_resource_observations) >>
  `!name. abi_decoder_operand_live ready.cs_next_var (Var name) ==>
    FLOOKUP Gv name = FLOOKUP Ga name /\
    op_taint tvn (Var name) = op_taint ta (Var name) /\
    FLOOKUP tvn.t_var name = FLOOKUP ta.t_var name` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
     rpt strip_tac >> asm_simp_tac bool_ss []) >>
  `!name. abi_decoder_operand_live live (Var name) ==>
    FLOOKUP Gv name = FLOOKUP G name /\ op_taint tvn (Var name) = op_taint tn (Var name) /\
    FLOOKUP tvn.t_var name = FLOOKUP tn.t_var name` by
    (rpt strip_tac >>
     `abi_decoder_operand_live ready.cs_next_var (Var name)` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `live` >> asm_rewrite_tac[]) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand (Var iv) v = SOME (n2w j) /\ op_taint tvn (Var iv) = {} /\
   op_prov Gv (Var iv) = NONE` by
    (qpat_assum `FST ops = Var iv` (fn th =>
       map_every (fn tm => qpat_assum tm (assume_tac o REWRITE_RULE [th]))
         [`eval_operand (FST ops) a = _`,`op_taint ta (FST ops) = _`,
          `op_prov Ga (FST ops) = _`,`abi_decoder_operand_live ready.cs_next_var (FST ops)`]) >>
     qpat_assum `op_prov Ga (Var iv) = NONE` (assume_tac o SRULE [op_prov_def]) >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ a v sc`
       (strip_assume_tac o MATCH_MP calldata_member_resource_observations) >>
     simp[op_prov_def]) >>
  `lookup_var q v = lookup_var q s` by
    (qpat_assum `!op. abi_decoder_operand_live live op ==> eval_operand op v = _`
       (qspec_then `Var q` mp_tac) >> simp[eval_operand_def]) >>
  `ptr_covers Gv tvn q v 32` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qpat_assum `ptr_covers G tn q s 32` (irule_at Any) >> asm_simp_tac bool_ss []) >>
  `q <> nv /\ slot+32 <= v.vs_alloca_next /\
   FLOOKUP v.vs_allocas counter_id = SOME (slot,32) /\
   FLOOKUP v.vs_allocas oid = SOME (base_addr,cap)` by
    (conj_tac >- (strip_tac >> gvs[]) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `lookup_var q v = SOME (n2w slot)` by asm_rewrite_tac[] >>
  mp_tac (Q.INST [`bb` |-> `back_bb`, `prefix` |-> `last.cs_current_insts`, 
      `id` |-> `bid`, `hdr` |-> `s.vs_current_bb`, `hdr_bb` |-> `bb`,
      `G` |-> `Gv`, `tn` |-> `tvn`] (SPEC_ALL selected_array_backedge)) >>
  (impl_tac >- fs[]) >> strip_tac >>
  rename1 `ptr_covers Gout tt q t 32` >>
  `calldata_member_resource_frame ctx fn site limit L H live d span s t
      (([] ++ sc) ++ [(slot,32)])` by
    (irule calldata_member_resource_extend >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s v _` (irule_at Any) >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ v t _` (irule_at Any) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
     mem_bytes_at d (32+j*type_memory_size tv) s.vs_memory` by
    (qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ a v sc` (fn th =>
       strip_assume_tac (MATCH_MP calldata_member_resource_endpoint th) >>
       strip_assume_tac (MATCH_MP calldata_member_resource_observations th)) >>
     qpat_assum `calldata_member_wit _ _ v sc`
       (assume_tac o REWRITE_RULE [calldata_member_wit_def]) >>
     mp_tac (Q.INST [`dst` |-> `d`, `stride` |-> `type_memory_size tv`,
         `s` |-> `a`, `t` |-> `v`, `lo` |-> `ready.cs_next_id`,
         `hi` |-> `last.cs_next_id`, `scratch` |-> `sc`, `output_id` |-> `oid`]
       (SPEC_ALL calldata_child_preserves_contained_prefix)) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> asm_rewrite_tac[]) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `d+(32+j*type_memory_size tv+type_memory_size tv) <= slot \/ slot+32 <= d` >-
    (irule selected_array_counter_disjoint >>
     qpat_assum `FLOOKUP v.vs_allocas counter_id = _` (irule_at Any) >>
     qpat_assum `FLOOKUP v.vs_allocas oid = _` (irule_at Any) >>
     asm_rewrite_tac[] >> decide_tac)) >>
  `mem_bytes_at d (32+j*type_memory_size tv) t.vs_memory =
     mem_bytes_at d (32+j*type_memory_size tv) s.vs_memory /\
   mem_bytes_at (d+32+j*type_memory_size tv) (type_memory_size tv) t.vs_memory =
     mem_bytes_at (d+32+j*type_memory_size tv) (type_memory_size tv) v.vs_memory` by
    (`d+(32+j*type_memory_size tv) <= slot \/ slot+32 <= d` by decide_tac >>
     `d+32+j*type_memory_size tv+type_memory_size tv <= slot \/
        slot+32 <= d+32+j*type_memory_size tv` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  `tvn.t_mem SUBSET tn.t_mem /\ tt.t_mem SUBSET tn.t_mem` by
    (metis_tac[SUBSET_TRANS]) >>
  `!i. i < SUC j ==> !mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
    val_in_memory tv (EL i (xs ++ [x])) (d+32+i*type_memory_size tv) mem` by
    (mp_tac (Q.INST [`stride` |-> `type_memory_size tv`,
       `old` |-> `s.vs_memory`, `mid` |-> `v.vs_memory`, `new` |-> `t.vs_memory`,
       `dirty` |-> `tn.t_mem`, `middle` |-> `tvn.t_mem`, `clean` |-> `tt.t_mem`]
       (SPEC_ALL selected_array_extend_values)) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC) >>
  `!name. abi_decoder_operand_live live (Var name) ==>
     FLOOKUP Gout name = FLOOKUP G name /\ op_taint tt (Var name) = op_taint tn (Var name) /\
     FLOOKUP tt.t_var name = FLOOKUP tn.t_var name` by
    (qx_gen_tac `name` >> strip_tac >> `name <> nv` by (strip_tac >> gvs[]) >>
     asm_simp_tac bool_ss []) >>
  `!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op s` by
    (qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s t _`
       (strip_assume_tac o MATCH_MP calldata_member_resource_observations) >>
     first_assum ACCEPT_TAC) >>
  `lookup_var q t = lookup_var q s /\ lookup_var root t = lookup_var root s` by
    (qpat_assum `!op. abi_decoder_operand_live live op ==> eval_operand op t = _`
       (fn th => mp_tac (Q.SPEC `Var q` th) >> mp_tac (Q.SPEC `Var root` th)) >>
     simp[eval_operand_def]) >>
  `ptr_covers Gout tt root t span` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qpat_assum `ptr_covers G tn root s span` (irule_at Any) >> asm_simp_tac bool_ss []) >>
  `op_taint tt src = {} /\ op_prov Gout src = NONE` by
    (Cases_on `src` >> fs[op_taint_def,op_prov_def]) >>
  qpat_assum `entry_decoder_obs s a` (strip_assume_tac o REWRITE_RULE [entry_decoder_obs_def]) >>
  qpat_assum `entry_decoder_obs v t` (strip_assume_tac o REWRITE_RULE [entry_decoder_obs_def]) >>
  qexistsl_tac [`x`,`rest`,`t`,`Gout`,`tt`,`([] ++ sc) ++ [(slot,32)]`] >>
  asm_simp_tac bool_ss [LENGTH_APPEND, EVERY_APPEND, LENGTH, listTheory.EVERY_DEF, ADD1, ADD] >>
  rpt gen_tac >>
  irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL gas_origin_ptr_path_append))) >>
  qexistsl_tac [`Gv`,`v`,`(OK v,Gv,tvn)`,`tvn`] >> asm_simp_tac bool_ss [] >>
  irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL gas_origin_ptr_path_append))) >>
  qexistsl_tac [`Ga`,`a`,`(OK a,Ga,ta)`,`ta`] >> asm_simp_tac bool_ss []
QED

Theorem selected_array_iteration:
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
    tt.t_mem SUBSET tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gt,tt))
Proof
  disch_tac >> mp_tac (SPEC_ALL selected_array_iteration_with_frame) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `ptr_covers Gout tt root t span` >>
  qexistsl_tac [`x`,`rest`,`t`,`Gout`,`tt`,`scratch`] >> asm_rewrite_tac[]
QED
