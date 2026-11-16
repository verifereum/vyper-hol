(* Raw array iteration: finite address setup and conditional child framing. *)
Theory calldataArrayRawCallsite
Ancestors
  calldataDynStep decoderArraySetupPtr calldataSourceCorrespondence
  calldataChildFrame calldataDynOwned entryDecoderSetupEndpoint
  entryDecoderStateFrame entryDecoderHistoryFrame abiDecoderCoherence
  abiDecoderDynamicLoopSetup abiDecoderLoopSetup abiDecoderContract
  abiDecoderReentry abiDecoderArraySetupInputs abiDecoderIndexedAddress
  loweringStateRelDefs compileEnv emitHelper emitHelperProps
  fragGasOriginPtr fragExecPtr ptrDiscipline bodyPtrDefs venomMemDefs
  valueEncodingProps valueEncodingDefs valueEncoding abiDecoderFrame
  venomState venomExecSemantics words arithmetic list finite_map pred_set
  instIdxIndep exprLoweringProps successfulSequenceEndpoint safeSequence fragExecMem rich_list

Theorem calldata_array_raw_child_callsite:
  abi_decoder_coherent ce env sf ty tv /\
  dec_info_needs_offset di = is_abi_dynamic ce.ce_struct_fields ty /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\ j < bound /\
  bound < dimword (:256) /\ slot+32 < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ sb+32 < dimword (:256) /\
  j*tv_abi_size tv < dimword (:256) /\
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
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts
  ==>
  ?raw t HG u child.
    run_inst_seq (emitted_insts st ready) s = OK raw /\
    t = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (sb+32) (j*tv_abi_size tv))) /\
    eval_operand (SND (SND ops)) t =
      SOME (n2w (d+32+j*type_memory_size tv)) /\
    SND (SND ops) = Var child /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    ptr_covers HG u child t (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov HG (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov HG (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit t /\ alloca_inv t /\ alloca_history fn t /\
    inst_extends st ready /\ entry_decoder_obs s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!x. not_fresh_at st x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
    (!D lower explicit ctx' func.
      fn_has_code st ready func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' ==>
      gas_origin_ptr_path (D,lower,explicit,ctx',func,PG) (s,G,tn) [] (OK t,HG,u))
Proof
  strip_tac >>
  `j < dimword (:256)` by decide_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w d) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspecl_then [`ctx`,`PG`,`ARB`] strip_assume_tac) >>
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
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (fs[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `n2w slot`] >>
     goal_assum (drule_at Any) >> simp[w2n_n2w] >> metis_tac[LESS_EQ]) >>
  mp_tac (Q.INST [`P` |-> `\s:venom_state. T`, `t` |-> `raw`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  drule calldata_coherent_dynamic >> strip_tac >>
  `(n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (sb+32) (j*tv_abi_size tv)):bytes32) =
    (if dec_info_needs_offset di then
      n2w (sb+32+w2n (abi_decode_load CALLDATALOAD
        (n2w (sb+32+j*tv_abi_size tv):bytes32) s))
     else n2w (sb+32+j*tv_abi_size tv))` by
    (mp_tac (Q.INST [`bp` |-> `(n2w (sb+32)):bytes32`,
       `ofs` |-> `(n2w (j*tv_abi_size tv)):bytes32`] calldata_member_pointer) >>
     simp[w2n_n2w, word_add_n2w] >> strip_tac >>
     Cases_on `tv_abi_dynamic tv` >> simp[word_add_def, w2n_n2w]) >>
  qexistsl_tac [`HG`, `u`] >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def,
    abi_decoder_address_frame_def, alloca_inv_def] >>
  fs[allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]
QED

Theorem calldata_array_raw_child_return_frame:
  abi_decode_footprint_frame
    ((dst+32+j*stride,stride)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (counter_id < lo \/ hi <= counter_id) /\
  (output_id < lo \/ hi <= output_id) /\ counter_id <> output_id /\
  FLOOKUP s.vs_allocas counter_id = SOME (counter,32) /\
  FLOOKUP s.vs_allocas output_id = SOME (base_addr,cap) /\
  base_addr <= dst /\ dst+32+j*stride+stride <= base_addr+cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  LENGTH xs = j /\ EVERY (val_wf tv) xs /\ stride = type_memory_size tv /\
  (!k. k < j ==> val_in_memory tv (EL k xs)
    (dst+32+k*stride) s.vs_memory)
  ==>
  FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
  mload counter t = mload counter s /\ t.vs_call_ctx = s.vs_call_ctx /\
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory /\
  (!k. k < j ==> val_in_memory tv (EL k xs)
    (dst+32+k*stride) t.vs_memory)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
   FLOOKUP t.vs_allocas output_id = SOME (base_addr,cap)` by metis_tac[] >>
  `counter+32 <= dst+32+j*stride \/
   dst+32+j*stride+stride <= counter` by
    (qpat_x_assum `alloca_inv t` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
     strip_tac >>
     first_x_assum (qspecl_then
       [`counter_id`,`output_id`,`counter`,`32`,`base_addr`,`cap`] mp_tac) >>
     impl_tac >- simp[] >> decide_tac) >>
  `mload counter t = mload counter s` by
    (irule (cj 2 calldata_child_preserves_counter) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `mem_bytes_at dst (32+j*stride) t.vs_memory =
     mem_bytes_at dst (32+j*stride) s.vs_memory` by
    (irule calldata_child_preserves_contained_prefix >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`base_addr`,`cap`,`output_id`] >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >> fs[]) >>
  drule_all calldata_prefix_window_transport >> strip_tac >>
  gvs[abi_decode_footprint_frame_def]
QED
