(* One pass through a nonbulk calldata decoder loop. *)
Theory calldataNoneArrayIteration
Ancestors
  calldataArrayRawCallsite decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr
  abiDecoderLoopRegisters decoderGhostFramePtr allocaFrontierBound
  calldataDynOwned calldataChildFrame calldataFiniteTransport ptrDiscipline
  abiDecodeRanges abiDecoderExecution
  calldataSourceCorrespondence vyperCalldata abiDecoderFrame abiDecoderReentry
  abiDecoderCoherence abiDecoderContract abiDecoderDynamicLoopSetup
  entryDecoderSetupEndpoint entryDecoderStateFrame calldataDynStep decoderArraySetupPtr
  fragGasOriginPtr fragExec emitHelperProps instIdxIndep venomExecSemantics
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
      allocas_from lower s /\ ~ctx_has_dalloca ctx ==>
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
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
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
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
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
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
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
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ DISJOINT {} tn.t_mem` by simp[] >>
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
