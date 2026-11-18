(* Countdown from the installed nonbulk-array header, using the source
   equation over the calldata in the current call context. *)
Theory selectedAcceptedArrayLoop
Ancestors
  selectedAcceptedArrayExactStep selectedAcceptedArrayStep
  selectedAcceptedInterfaces sourceArrayHeaderOriginPtr decoderGhostFramePtr
  calldataMemberResourceFrame calldataSourceCorrespondence
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderExecution
  abiDecoderCoherence entryDecoderStateFrame valueEncodingProps emitHelperProps
  representationCleanPtr logStoreDataOriginPtr abiStaticAggregateProps
  compileEnv venomState venomExecSemantics words arithmetic list finite_map pred_set
  ptrDiscipline bodyPtrDefs fragGasOriginPtr vyperCalldata loweringStateRelDefs codegenRel

(* An iteration writes the new element and the private counter, not the
   array's length word. Its clean window stays clean as dirty bytes shrink. *)
Theorem selected_array_count_frame[local]:
  (!mem. mem_agree_outside dirty pre mem ==> mem_word_at d mem = w) /\
  dirty' SUBSET dirty /\
  mem_bytes_at d (32+n) post = mem_bytes_at d (32+n) pre ==>
  !mem. mem_agree_outside dirty' post mem ==> mem_word_at d mem = w
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  `mem_bytes_at d 32 post = mem_bytes_at d 32 pre` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`, `32`] mp_tac) >> simp[]) >>
  `!i. d <= i /\ i < d+32 ==> i NOTIN dirty'` by
    (drule representationCleanPtrTheory.robust_mem_word_at_clean >>
     fs[SUBSET_DEF] >> metis_tac[]) >>
  `mem_bytes_at d 32 post = mem_bytes_at d 32 mem` by
    (irule logStoreDataOriginPtrTheory.mem_agree_outside_window >> qexists_tac `dirty'` >> simp[]) >>
  `mem_word_at d pre = w` by simp[mem_agree_outside_def] >>
  fs[mem_word_at_bytes]
QED

Theorem selected_array_exit_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts hid (Var q) src CALLDATALOAD hv cv cmp dn body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ALL_DISTINCT [q;hv;cv;cmp;dn] /\
  lookup_var q s = SOME (n2w slot) /\ ptr_covers G tn q s 32 /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ mload slot s = n2w cnt /\
  DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD (n2w sb:bytes32) s = n2w cnt /\
  cnt < dimword (:256) /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\ fresh_vars_wrt limit s /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ?k. x = STRING #"%" (toString k) /\
    k < limit.cs_next_var) /\
  abi_decoder_operand_live live (Var root) /\ abi_decoder_operand_live live src /\
  (!x. MEM x [hv;cv;cmp;dn] ==> ~abi_decoder_operand_live live (Var x)) /\
  ptr_covers G tn root s span /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn L H_id s ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    t.vs_memory = s.vs_memory /\ ptr_covers H u root t span /\ allocas_from lower t /\
    calldata_member_resource_frame ctx fn site limit L H_id live d span s t [] /\
    entry_decoder_obs s t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live live (Var x) ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u))
Proof
  strip_tac >>
  `src <> Var hv` by (strip_tac >> fs[]) >>
  mp_tac (Q.INST [`lo` |-> `lower`, `id` |-> `hid`, `iv` |-> `hv`,
    `done` |-> `dn`, `ncount` |-> `cnt`, `j` |-> `cnt`, `srcaddr` |-> `n2w sb`]
    (SPEC_ALL source_array_header_origin_ptr_exact_frame)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t = jump_to exit_lbl (abi_decode_header_state hv cv cmp dn cnt cnt s)` by simp[] >>
  `fresh_vars_wrt limit (abi_decode_header_state hv cv cmp dn cnt cnt s)` by
    (rewrite_tac[abi_decode_header_state_def, LET_THM] >>
     qpat_x_assum `!x. MEM x [hv;cv;cmp;dn] ==> ?k. _`
       (fn th => map_every (fn v => qspec_then v mp_tac th) [`hv`,`cv`,`cmp`,`dn`]) >>
     simp[] >> rpt strip_tac >> metis_tac[fresh_vars_wrt_update_var]) >>
  `entry_decoder_obs s t` by simp[jump_to_def, abi_decode_header_state_def] >>
  `t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
   fresh_vars_wrt limit t /\ allocas_from lower t /\
   ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0` by
    (fs[jump_to_def, abi_decode_header_state_def, update_var_def,
        fresh_vars_wrt_def, allocas_from_def] >> metis_tac[]) >>
  `!x. abi_decoder_operand_live live (Var x) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint u (Var x) = op_taint tn (Var x) /\
    FLOOKUP u.t_var x = FLOOKUP tn.t_var x` by
    (rpt strip_tac >> metis_tac[]) >>
  `ptr_covers H u root t span` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `!op. abi_decoder_operand_live live op ==> eval_operand op t = eval_operand op s` by
    (Cases >> simp[eval_operand_def, jump_to_def, abi_decode_header_state_def, update_var_def]
     >> metis_tac[]) >>
  `calldata_member_resource_frame ctx fn site limit L H_id live d span s t []` by
    (irule calldata_member_resource_unchanged >>
     fs[entry_decoder_obs_def]) >>
  qexistsl_tac [`t`,`H`,`u`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem selected_array_header_to_exit:
  !remaining s G tn j xs pending.
  selected_decoder_accepts ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  s.vs_current_bb = hdr /\ lookup_block hdr fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts hid (Var q) src CALLDATALOAD hv cv cmp dn
      st.cs_current_bb exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ALL_DISTINCT [q;hv;cv;cmp;dn] /\
  lookup_var q s = SOME (n2w slot) /\ ptr_covers G tn q s 32 /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  abi_decode_load CALLDATALOAD (n2w sb:bytes32) s = n2w cnt /\
  j + remaining = cnt /\ cnt < dimword (:256) /\ allocas_from lower s /\
  lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
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
  32+cnt*type_memory_size tv <= span /\ d+span < dimword (:256) /\
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
    abi_decode_backedge_insts bid iv nv (Var q) hdr /\
  nv = STRING #"%" (toString k) /\ k < limit.cs_next_var /\
  ~abi_decoder_operand_live live (Var nv) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn L H_id s /\
  L <= ready.cs_next_id /\ ready.cs_next_id <= last.cs_next_id /\ last.cs_next_id <= H_id /\
  L <= counter_id /\ counter_id < H_id /\ counter_id <> oid /\
  FLOOKUP s.vs_allocas counter_id = SOME (slot,32) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+span <= base_addr+cap /\
  LENGTH xs = j /\ EVERY (val_wf tv) xs /\ EVERY (value_has_type tv) xs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> mem_word_at d mem = n2w cnt) /\
  (!i. i < j ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem) /\
  cd_decode_elems F s.vs_call_ctx.cc_calldata tv (cd_at F (w2n (n2w sb:bytes32)) 32)
    j remaining = SOME pending ==>
  ?t H u sc.
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    LENGTH (xs ++ pending) = cnt /\
    EVERY (val_wf tv) (xs ++ pending) /\ EVERY (value_has_type tv) (xs ++ pending) /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> mem_word_at d mem = n2w cnt) /\
    (!i. i < cnt ==> !mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv (EL i (xs ++ pending)) (d+32+i*type_memory_size tv) mem) /\
    ptr_covers H u root t span /\ allocas_from lower t /\
    calldata_member_resource_frame ctx fn site limit L H_id live d span s t sc /\
    t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live live (Var x) ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u))
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `j = cnt` by decide_tac >>
      `pending = []` by fs[Once cd_decode_def] >>
      mp_tac (Q.INST [`body_lbl` |-> `st.cs_current_bb`]
        (SPEC_ALL selected_array_exit_edge)) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `entry_decoder_obs s t` (strip_assume_tac o REWRITE_RULE[entry_decoder_obs_def]) >>
      qexistsl_tac [`t`,`H`,`u`,`[]`] >> gnvs[AC ADD_ASSOC ADD_COMM]) >>
  pop_assum (mk_asm "ih") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `j + SUC remaining = cnt` >>
  `j < cnt /\ SUC j + remaining = cnt` by decide_tac >>
  `32+j*type_memory_size tv+type_memory_size tv <= span` by
    (`SUC j * type_memory_size tv <= cnt * type_memory_size tv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `SUC j * _ <= cnt * _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  mp_tac (Q.INST [`H` |-> `H_id`, `n` |-> `remaining`]
    (SPEC_ALL selected_array_iteration_exact)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `ptr_covers Gmid tt root t span` >>
  drule_then strip_assume_tac calldata_member_resource_endpoint >>
  drule_then strip_assume_tac calldata_member_resource_observations >>
  `slot+32 <= t.vs_alloca_next /\ lower <= t.vs_alloca_next` by decide_tac >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) t = n2w cnt` by
    fs[calldata_decode_load_word] >>
  `!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==> mem_word_at d mem = n2w cnt` by
    (rpt strip_tac >> irule selected_array_count_frame >>
     qexistsl_tac [`tn.t_mem`,`tt.t_mem`,`j*type_memory_size tv`,`t.vs_memory`,`s.vs_memory`] >> simp[]) >>
  asm_x "ih" (qspecl_then [`t`,`Gmid`,`tt`,`SUC j`,`xs ++ [x]`,`rest`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gout`
    (qx_choose_then `u` (qx_choose_then `sc` strip_assume_tac)))) >>
  `calldata_member_resource_frame ctx fn site limit L H_id live d span s out (scratch ++ sc)` by
    (irule calldata_member_resource_extend >>
     qexistsl_tac [`H_id`,`L`,`live`,`d`,`span`,`t`] >> simp[] >> decide_tac) >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK out,Gout,u)` by
    (rpt gen_tac >>
     qpat_x_assum `!D explicit. gas_origin_ptr_path _ (_,_,_) [] (OK t,Gmid,tt)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append o Q.SPECL [`D`,`explicit`]) >>
     disch_then (qspecl_then [`t`,`Gmid`,`tt`,`[]`,`OK out`,`Gout`,`u`] mp_tac) >> simp[]) >>
  `u.t_mem SUBSET tn.t_mem` by
    (irule SUBSET_TRANS >> qexists_tac `tt.t_mem` >> asm_rewrite_tac[]) >>
  `!name. abi_decoder_operand_live live (Var name) ==>
    FLOOKUP Gout name = FLOOKUP G name /\ FLOOKUP u.t_var name = FLOOKUP tn.t_var name` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x. _ ==> FLOOKUP Gout x = _ /\ _` (qspec_then `name` mp_tac) >>
     qpat_assum `!x. _ ==> FLOOKUP Gmid x = _ /\ _` (qspec_then `name` mp_tac) >>
     qpat_assum `!x. _ ==> FLOOKUP tt.t_var x = _` (qspec_then `name` mp_tac) >>
     simp[]) >>
  qexistsl_tac [`out`,`Gout`,`u`,`scratch ++ sc`] >>
  `xs ++ pending = (xs ++ [x]) ++ rest` by simp[GSYM APPEND_ASSOC] >>
  qpat_assum `xs ++ pending = _` SUBST1_TAC >>
  asm_rewrite_tac[]
QED
