(* Conservative vocabulary for the jointly witnessed nonbulk array loop. *)
Theory entryDecoderJointLoop
Ancestors
  entryDecoderLoopStep entryDecoderRelationIteration
  entryDecoderEndpointValidation entryDecoderStateFrame words abiDecoderFrame
  calldataDynStep abiDecoderReentry abiDecoderReentryAddress abiDecoderLoopSetup
  entryDecoderSetupEndpoint entryDecoderHistoryFrame successfulSequenceEndpoint
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderContract
  fragExecMem instIdxIndep abiEncoder emitHelper exprLoweringProps
  list rich_list arithmetic venomInst venomMemDefs decoderPrefixEdges
  abiDecoderValidArrayEntry abiDecoderLoopRegisters calldataDynOwned
  abiDecoderExecution venomExecSemantics calldataEmptyArrayChild
  calldataValidOwnedStep abiDecoderTypedContract abiDecoderCoherence

Definition EntryLoopOwn_def:
  EntryLoopOwn fn lo hi s <=>
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
End

Definition EntryLoopSafe_def:
  EntryLoopSafe ctx fn s t <=>
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
End

Definition EntryLoopPull_def:
  EntryLoopPull ctx fn s t <=>
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
End

Definition EntrySetupFrame_def:
  EntrySetupFrame next u entry <=>
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u)
End

Definition EntryChildResources_def:
  EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new <=>
    ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
    child.vs_inst_idx = LENGTH st1.cs_current_insts /\
    val_wf tv (EL j vs) /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
    fresh_vars_wrt limit_st child /\
    child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
    alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
    EntryLoopOwn fn ready.cs_next_id st1.cs_next_id child /\
    entry.vs_alloca_next <= child.vs_alloca_next /\
    (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
      FLOOKUP child.vs_allocas id = SOME (q,k)) /\
    (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
      FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
    (!op. abi_decoder_operand_live ready.cs_next_var op ==>
      eval_operand op child = eval_operand op entry) /\
    abi_decode_footprint_frame
      ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
    (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP child.vs_allocas id = SOME (q,k))
End

Definition EntryLoopHeader_def:
  EntryLoopHeader ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j s scratch <=>
    ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
    j <= LENGTH vs /\ LENGTH vs <= maxn /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
    abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
    mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
    s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
    FLOOKUP s.vs_allocas iid = SOME (p,32) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    EntryLoopOwn fn st.cs_next_id end_st.cs_next_id s /\
    initial.vs_alloca_next <= s.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP s.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op s = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
    MEM (p,32) scratch /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit_st s /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
End

Definition EntryLoopInv_def:
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j s scratch <=>
    EntryLoopHeader ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j s scratch /\
    (!k. k < j ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) s.vs_memory)
End

Theorem entry_setup_frame_refl:
  EntrySetupFrame next s s
Proof
  simp[EntrySetupFrame_def]
QED

Theorem entry_setup_frame_trans:
  EntrySetupFrame next s t /\ EntrySetupFrame next t u ==> EntrySetupFrame next s u
Proof
  simp[EntrySetupFrame_def] >> metis_tac[]
QED

Theorem entry_joint_loop_safe_refl:
  EntryLoopSafe ctx fn s s
Proof
  simp[EntryLoopSafe_def] >> metis_tac[]
QED

Theorem entry_joint_loop_pull_refl:
  EntryLoopPull ctx fn s s
Proof
  simp[EntryLoopPull_def]
QED

Definition EntryLoopConfig_def:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
      hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
      p d iid oid base_addr cap <=>
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
    st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= st1.cs_next_id /\
    st1.cs_next_id <= end_st.cs_next_id /\
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions :=
        abi_decode_header_insts hid ip src CALLDATALOAD
          (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
          (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
          body_lbl exit_lbl|> /\
    lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions :=
        st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
          (STRING #"%" (toString nvar)) ip hdr|> /\
    FST ops = Var biv /\ abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
      (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
    vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
    ((!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) \/
     (type_to_abi_dec_info sf ce ty = DecComplex T [] /\ ready = st1 /\
      EVERY (value_has_type tv) vs)) /\
    EVERY (val_wf tv) vs /\ LENGTH vs < dimword (:256) /\
    p < dimword (:256) /\
    d+(32+maxn*type_memory_size tv) < dimword (:256) /\
    (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
    (iid < ready.cs_next_id \/ st1.cs_next_id <= iid) /\
    (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
    base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
    abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
    abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
    next+4 <= limit_st.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var /\
    nvar < limit_st.cs_next_var /\
    (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
      op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
    (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op)
End

Theorem entry_joint_loop_safe_trans:
  EntryLoopSafe ctx fn s t /\ EntryLoopSafe ctx fn t u ==> EntryLoopSafe ctx fn s u
Proof
  simp[EntryLoopSafe_def] >> metis_tac[]
QED

Theorem entry_joint_loop_pull_trans:
  EntryLoopPull ctx fn s t /\ EntryLoopPull ctx fn t u ==> EntryLoopPull ctx fn s u
Proof
  simp[EntryLoopPull_def]
QED

(* Application boundary: all resources and observations refer to the supplied
   child and its explicit backedge, never to independently chosen endpoints. *)
Theorem entry_joint_fixed_successor:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ EntrySetupFrame next u entry /\
  EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
  v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child)) /\
  EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
  EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
  EntryLoopSafe ctx fn child v /\ EntryLoopPull ctx fn child v /\
  entry_decoder_obs initial u /\ entry_decoder_obs u entry /\
  entry_decoder_obs entry child /\ alloca_history fn child /\
  bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts id iv (STRING #"%" (toString nvar)) ip hdr /\
  eval_operand (Var iv) child = SOME (n2w j) /\
  eval_operand ip child = SOME (n2w p) /\ ip <> Var (STRING #"%" (toString nvar)) ==>
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial
    (SUC j) v (old++new) /\
  EntryLoopSafe ctx fn u v /\ EntryLoopPull ctx fn u v /\
  entry_decoder_obs initial v /\ entry_decoder_obs u v /\ alloca_history fn v
Proof
  pure_rewrite_tac[EntryLoopConfig_def, EntryLoopInv_def,
    EntrySetupFrame_def, EntryChildResources_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac entry_owned_fixed_successor_frame >>
  map_every (fn th =>
    CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
    BETA_TAC >> pure_rewrite_tac[GSYM th])
    [EntryLoopOwn_def, EntryLoopSafe_def, EntryLoopPull_def, EntryLoopHeader_def] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] entry_backedge_endpoint_frame) >>
  simp[Once w2n_n2w] >> strip_tac >>
  rpt conj_tac >> asm_rewrite_tac[] >>
  metis_tac[entry_decoder_obs_trans]
QED

Theorem entry_joint_identity_child:
  ~entry.vs_halted /\ entry.vs_current_bb = st1.cs_current_bb /\
  entry.vs_inst_idx = LENGTH st1.cs_current_insts /\
  val_wf tv (EL j vs) /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) entry.vs_memory /\
  fresh_vars_wrt limit_st entry /\ alloca_inv entry /\
  alloca_frontier_inv ctx fn site entry ==>
  EntryChildResources ctx fn site st1 st1 limit_st tv vs d j entry entry [] /\
  EntryLoopSafe ctx fn entry entry /\ EntryLoopPull ctx fn entry entry /\
  entry_decoder_obs entry entry
Proof
  simp[EntryChildResources_def, EntryLoopOwn_def,
    abi_decode_footprint_frame_refl, entry_joint_loop_safe_refl,
    entry_joint_loop_pull_refl] >>
  rpt strip_tac >> fs[]
QED

Theorem entry_joint_child_control:
  EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new ==>
  ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
  child.vs_inst_idx = LENGTH st1.cs_current_insts /\
  alloca_inv child /\ alloca_frontier_inv ctx fn site child
Proof
  simp[EntryChildResources_def]
QED

Theorem entry_joint_loop_control:
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j s scratch ==>
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  j <= LENGTH vs /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s
Proof
  simp[EntryLoopInv_def, EntryLoopHeader_def]
QED


(* The exceptional zero-static child uses this actual setup endpoint and
   then the identity child; no ordinary array-entry certificate is needed. *)
Theorem entry_joint_empty_setup_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecComplex T []) abi_sz mem_sz st = (ops,ready) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    EntrySetupFrame st.cs_next_var s t /\ fresh_vars_wrt limit_st t /\
    inst_extends st ready /\ entry_decoder_obs s t /\ alloca_history fn t /\
    EntryLoopSafe ctx fn s t /\ EntryLoopPull ctx fn s t
Proof
  strip_tac >> drule_all entry_element_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  fs[EntrySetupFrame_def, EntryLoopSafe_def, EntryLoopPull_def,
     abi_decoder_address_frame_def]
QED

Theorem entry_joint_empty_setup:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] ==>
  ?entry. ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    EntrySetupFrame next u entry /\ fresh_vars_wrt limit_st entry /\
    eval_operand (FST ops) entry = SOME (n2w j) /\
    EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
    entry_decoder_obs u entry /\ alloca_history fn entry
Proof
  pure_rewrite_tac[EntryLoopConfig_def, EntryLoopInv_def, EntryLoopHeader_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p+32 <= u.vs_alloca_next` by
    (qhdtm_assum `alloca_inv` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas iid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  qpat_assum `lookup_block hdr _ = _` mp_tac >>
  qpat_assum `u.vs_current_bb = hdr` (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >> drule_all calldata_valid_header_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all entry_header_body_transfer_frame >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand src head = SOME (n2w sb) /\
   eval_operand dst head = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  `alloca_inv head` by metis_tac[cj 1 calldata_alloca_invariants_fields] >>
  `head.vs_current_bb = st0.cs_current_bb /\
   head.vs_inst_idx = LENGTH st0.cs_current_insts /\
   mload (w2n (n2w p:bytes32)) head = n2w j /\
   w2n (n2w p:bytes32)+32 <= head.vs_alloca_next` by
    (qpat_x_assum `head = _` kall_tac >> simp[]) >>
  qpat_x_assum `type_to_abi_dec_info sf ce ty = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all entry_joint_empty_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `t.vs_current_bb = ready.cs_current_bb` >>
  qexists_tac `t` >> suspend "compose"
QED
Resume entry_joint_empty_setup[compose]:
  `EntrySetupFrame next u head` by simp[EntrySetupFrame_def] >>
  `EntrySetupFrame next head t` by
    (qpat_assum `EntrySetupFrame st0.cs_next_var head t` mp_tac >>
     qpat_assum `next <= st0.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EntrySetupFrame_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `EntryLoopSafe ctx fn u head /\ EntryLoopPull ctx fn u head` by
    asm_rewrite_tac[EntryLoopSafe_def, EntryLoopPull_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[entry_setup_frame_trans]
  >- metis_tac[entry_joint_loop_safe_trans]
  >- metis_tac[entry_joint_loop_pull_trans]
  >> metis_tac[entry_decoder_obs_trans]
QED
Finalise entry_joint_empty_setup

(* Execute the backedge of the child already selected by the caller. *)
Theorem entry_joint_backedge_transfer:
  lookup_block child.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  child.vs_inst_idx = LENGTH prefix /\ ~child.vs_halted /\
  eval_operand (Var iv) child = SOME (n2w j) /\
  eval_operand ip child = SOME (n2w p) /\ ip <> Var nv /\
  j < n /\ n < dimword (:256) /\ p < dimword (:256) /\
  p+32 <= child.vs_alloca_next /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  v = jump_to hdr (mstore p (n2w (SUC j)) (update_var nv (n2w (SUC j)) child)) ==>
  EntryLoopSafe ctx fn child v /\ EntryLoopPull ctx fn child v
Proof
  strip_tac >>
  `v = jump_to hdr (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
    (update_var nv (n2w (SUC j)) child)) /\
   w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` by simp[] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] calldata_backedge_safe_transfer) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var iv) child = _`)) >>
  disch_then (drule_at (Pat `eval_operand ip child = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = _`)) >>
  disch_then (qspecl_then [`v`, `n`, `ctx`] mp_tac) >>
  asm_rewrite_tac[] >> disch_tac >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] calldata_backedge_all_fuel_pullback) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var iv) child = _`)) >>
  disch_then (drule_at (Pat `eval_operand ip child = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = _`)) >>
  disch_then (qspecl_then [`v`, `n`, `ctx`] mp_tac) >>
  asm_rewrite_tac[] >> disch_tac >>
  asm_rewrite_tac[EntryLoopSafe_def, EntryLoopPull_def] >>
  qpat_x_assum `!fuel. (!fuel. _) ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Theorem entry_joint_setup_resources:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ EntrySetupFrame next u entry ==>
  alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
  EntryLoopOwn fn ready.cs_next_id st1.cs_next_id entry /\
  FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d+32+j*type_memory_size tv /\
  d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
  d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256)
Proof
  pure_rewrite_tac[EntryLoopConfig_def, EntryLoopInv_def, EntryLoopHeader_def,
    EntrySetupFrame_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `j+1 <= maxn` by decide_tac >>
  `j*type_memory_size tv+type_memory_size tv <= maxn*type_memory_size tv` by
    (`(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  conj_tac >- metis_tac[cj 1 calldata_alloca_invariants_fields] >>
  conj_tac >- metis_tac[cj 2 calldata_alloca_invariants_fields] >>
  conj_tac >-
    (qpat_assum `EntryLoopOwn _ _ _ _` mp_tac >>
     qpat_assum `st.cs_next_id <= ready.cs_next_id` mp_tac >>
     qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_assum `entry.vs_allocas = u.vs_allocas` mp_tac >>
     qpat_assum `entry.vs_alloca_next = u.vs_alloca_next` mp_tac >>
     rpt (pop_assum kall_tac) >>
     ntac 5 strip_tac >>
     pure_rewrite_tac[EntryLoopOwn_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `EntryLoopOwn _ _ _ _` mp_tac >>
     pure_rewrite_tac[EntryLoopOwn_def] >> strip_tac >>
     qpat_assum `entry.vs_allocas = _` (fn th =>
       rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     pure_asm_rewrite_tac[] >> first_x_assum irule >>
     pure_asm_rewrite_tac[] >> decide_tac) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem entry_joint_valid_setup:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  ?head entry.
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    EntrySetupFrame next u entry /\
    fresh_vars_wrt limit_st entry /\ eval_operand (FST ops) entry = SOME (n2w j) /\
    EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
    entry_decoder_obs u entry /\ alloca_history fn entry
Proof
  pure_rewrite_tac[EntryLoopConfig_def, EntryLoopInv_def, EntryLoopHeader_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p+32 <= u.vs_alloca_next` by
    (qhdtm_assum `alloca_inv` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas iid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  qpat_assum `lookup_block hdr _ = _` mp_tac >>
  qpat_assum `u.vs_current_bb = hdr` (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >>
  drule_all entry_valid_header_child_frame >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt limit_st entry /\ eval_operand (FST ops) entry = SOME (n2w j)` by
    (qhdtm_assum `abi_decoder_valid_array_entry` mp_tac >>
     simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM] >>
     strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`head`, `entry`] >>
  asm_rewrite_tac[EntrySetupFrame_def, EntryLoopSafe_def, EntryLoopPull_def]
QED

Theorem entry_joint_ordinary_child:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  (!head entry.
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    EntryLoopOwn fn ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) /\
    alloca_history fn entry ==>
    ?child new. EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
      EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
      entry_decoder_obs entry child /\ alloca_history fn child) ==>
  ?entry child new.
    EntrySetupFrame next u entry /\ eval_operand (FST ops) entry = SOME (n2w j) /\
    EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
    EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
    EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
    entry_decoder_obs u entry /\ entry_decoder_obs entry child /\ alloca_history fn child
Proof
  strip_tac >> drule_all entry_joint_valid_setup >> strip_tac >>
  drule_all entry_joint_setup_resources >> strip_tac >>
  qpat_x_assum `!head entry. _` drule_all >> strip_tac >>
  qexistsl_tac [`entry`, `child`, `new`] >> asm_rewrite_tac[]
QED

Theorem entry_joint_empty_child:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  ~(!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  ?entry child new.
    EntrySetupFrame next u entry /\ eval_operand (FST ops) entry = SOME (n2w j) /\
    EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
    EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
    EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
    entry_decoder_obs u entry /\ entry_decoder_obs entry child /\ alloca_history fn child
Proof
  strip_tac >>
  `type_to_abi_dec_info sf ce ty = DecComplex T [] /\ ready = st1 /\
   EVERY (value_has_type tv) vs /\ abi_decoder_coherent ce env sf ty tv` by
    (qhdtm_assum `EntryLoopConfig` mp_tac >>
     qpat_assum `~(!elem. _)` mp_tac >> rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [EntryLoopConfig_def] >> rpt strip_tac >>
     fs[abi_decoder_coherent_array_iff]) >>
  `value_has_type tv (EL j vs)` by fs[EVERY_EL] >>
  drule_all calldata_empty_dynamic_child_value >> strip_tac >>
  drule_all entry_joint_empty_setup >> strip_tac >>
  drule_all entry_joint_setup_resources >> strip_tac >>
  `entry.vs_current_bb = st1.cs_current_bb /\
   entry.vs_inst_idx = LENGTH st1.cs_current_insts /\
   val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) entry.vs_memory` by
    asm_rewrite_tac[] >>
  drule_all entry_joint_identity_child >> strip_tac >>
  qexistsl_tac [`entry`, `entry`, `[]`] >> asm_rewrite_tac[]
QED

Theorem entry_joint_chosen_successor:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ EntrySetupFrame next u entry /\
  eval_operand (FST ops) entry = SOME (n2w j) /\
  EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
  EntryLoopSafe ctx fn u entry /\ EntryLoopPull ctx fn u entry /\
  EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
  entry_decoder_obs initial u /\ entry_decoder_obs u entry /\
  entry_decoder_obs entry child /\ alloca_history fn child ==>
  ?v. EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial
      (SUC j) v (old++new) /\
    EntryLoopSafe ctx fn u v /\ EntryLoopPull ctx fn u v /\
    entry_decoder_obs initial v /\ entry_decoder_obs u v /\ alloca_history fn v
Proof
  strip_tac >>
  `~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
   child.vs_inst_idx = LENGTH st1.cs_current_insts /\
   eval_operand (Var biv) child = SOME (n2w j) /\
   eval_operand ip child = SOME (n2w p) /\
   ip <> Var (STRING #"%" (toString nvar)) /\ p+32 <= child.vs_alloca_next` by
    suspend "operands" >>
  qabbrev_tac `bb = <|bb_label := st1.cs_current_bb; bb_instructions :=
    st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
      (STRING #"%" (toString nvar)) ip hdr|>` >>
  qabbrev_tac `v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child))` >>
  `EntryLoopSafe ctx fn child v /\ EntryLoopPull ctx fn child v` by suspend "edge" >>
  `bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts st1.cs_next_id biv (STRING #"%" (toString nvar)) ip hdr` by
    simp[Abbr `bb`] >>
  `v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child))` by
    simp[Abbr `v`] >>
  drule_all entry_joint_fixed_successor >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[]
QED
Resume entry_joint_chosen_successor[operands]:
  `FST ops = Var biv /\ abi_decoder_operand_live ready.cs_next_var (FST ops) /\
   abi_decoder_operand_live next ip /\
   (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
   ip <> Var (STRING #"%" (toString nvar))` by
    (qhdtm_assum `EntryLoopConfig` mp_tac >> rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [EntryLoopConfig_def] >> rpt strip_tac >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `alloca_inv u /\ FLOOKUP u.vs_allocas iid = SOME (p,32) /\
   eval_operand ip u = SOME (n2w p)` by
    (qhdtm_assum `EntryLoopInv` mp_tac >> rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [EntryLoopInv_def, EntryLoopHeader_def] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `p+32 <= u.vs_alloca_next` by
    (qhdtm_assum `alloca_inv` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas iid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  qhdtm_x_assum `EntryLoopConfig` kall_tac >>
  qhdtm_x_assum `EntryLoopInv` kall_tac >>
  qhdtm_x_assum `alloca_inv` kall_tac >>
  qhdtm_x_assum `EntrySetupFrame` mp_tac >>
  qhdtm_x_assum `EntryChildResources` mp_tac >>
  pure_rewrite_tac[EntrySetupFrame_def, EntryChildResources_def] >>
  ntac 2 (disch_then (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand ip child = SOME (n2w p)` by metis_tac[] >>
  `eval_operand (Var biv) child = SOME (n2w j)` by metis_tac[] >>
  asm_rewrite_tac[] >> decide_tac
QED
Resume entry_joint_chosen_successor[edge]:
  `p < dimword (:256) /\ LENGTH vs < dimword (:256) /\
   lookup_block child.vs_current_bb fn.fn_blocks = SOME bb /\
   ?hbb. lookup_block hdr fn.fn_blocks = SOME hbb /\
     phi_prefix_length hbb.bb_instructions = 0` by
    (qhdtm_assum `EntryLoopConfig` mp_tac >>
     qpat_assum `child.vs_current_bb = _` mp_tac >>
     qpat_assum `Abbrev (bb = _)` mp_tac >> rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [EntryLoopConfig_def, markerTheory.Abbrev_def] >>
     ntac 2 strip_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_rewrite_tac[] >>
     simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  `bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts st1.cs_next_id biv (STRING #"%" (toString nvar)) ip hdr` by
    simp[Abbr `bb`] >>
  `v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child))` by
    simp[Abbr `v`] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] entry_joint_backedge_transfer) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var biv) child = _`)) >>
  disch_then (drule_at (Pat `eval_operand ip child = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = _`)) >>
  disch_then (qspecl_then [`v`, `LENGTH (vs:value list)`, `ctx`] mp_tac) >>
  asm_rewrite_tac[]
QED
Finalise entry_joint_chosen_successor

(* The ordinary recursive producer is called only in the nonempty branch;
   the exceptional zero-static branch constructs its identity child. *)
Theorem entry_joint_header_successor:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j u old /\
  j < LENGTH vs /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  entry_decoder_obs initial u /\
  (!head entry.
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    EntryLoopOwn fn ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) /\
    alloca_history fn entry ==>
    ?child new. EntryChildResources ctx fn site ready st1 limit_st tv vs d j entry child new /\
      EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
      entry_decoder_obs entry child /\ alloca_history fn child) ==>
  ?v new. EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial
      (SUC j) v (old++new) /\
    EntryLoopSafe ctx fn u v /\ EntryLoopPull ctx fn u v /\
    entry_decoder_obs initial v /\ entry_decoder_obs u v /\ alloca_history fn v
Proof
  strip_tac >>
  Cases_on `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem`
  >- (drule_all entry_joint_ordinary_child >> strip_tac >>
      drule_all entry_joint_chosen_successor >> strip_tac >>
      qexistsl_tac [`v`, `new`] >> asm_rewrite_tac[]) >>
  drule_all entry_joint_empty_child >> strip_tac >>
  drule_all entry_joint_chosen_successor >> strip_tac >>
  qexistsl_tac [`v`, `new`] >> asm_rewrite_tac[]
QED

(* Finite closure hides scratch existentially; a successor must still supply
   all resources and observations jointly before this boundary can be used. *)
Theorem entry_joint_loop_finite:
  let H = EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial
  in
  j <= LENGTH vs /\ H j s old /\ entry_decoder_obs initial s /\ alloca_history fn s /\
  (!k u scratch. k < LENGTH vs /\ H k u scratch /\
    entry_decoder_obs initial u /\ alloca_history fn u ==>
    ?v new. H (SUC k) v (scratch++new) /\
      EntryLoopSafe ctx fn u v /\ EntryLoopPull ctx fn u v /\
      entry_decoder_obs u v /\ alloca_history fn v) ==>
  ?t scratch. H (LENGTH vs) t scratch /\
    EntryLoopSafe ctx fn s t /\ EntryLoopPull ctx fn s t /\
    entry_decoder_obs s t /\ alloca_history fn t
Proof
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >> strip_tac >>
  qabbrev_tac `Inv = \k u. (?scratch. H k u scratch) /\
    entry_decoder_obs initial u /\ alloca_history fn u` >>
  mp_tac (Q.INST [`Inv` |-> `Inv`, `n` |-> `LENGTH (vs:value list)`]
    (SPEC_ALL entry_safe_pull_frame_iteration)) >>
  map_every (fn th =>
    CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
    BETA_TAC >> pure_rewrite_tac[GSYM th]) [EntryLoopSafe_def, EntryLoopPull_def] >>
  CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >> BETA_TAC >>
  (impl_tac >-
    (conj_tac >- asm_rewrite_tac[] >>
     conj_tac >- (simp[Abbr `Inv`] >> metis_tac[]) >>
     simp[Abbr `Inv`] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     goal_assum (drule_at Any) >>
     metis_tac[entry_decoder_obs_trans])) >>
  simp[Abbr `Inv`] >> metis_tac[]
QED

Theorem entry_joint_loop_from_header:
  EntryLoopConfig fn st st0 ready st1 end_st limit_st ce env sf ty tv vs maxn
    hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs
    p d iid oid base_addr cap /\
  EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
    src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial j s old /\
  j <= LENGTH vs /\ alloca_history fn s /\ fn_inst_ids_distinct fn /\
  entry_decoder_obs initial s /\
  (!k head entry.
    k < LENGTH vs /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs k ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    EntryLoopOwn fn ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+k*type_memory_size tv /\
    d+32+k*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+k*type_memory_size tv+type_memory_size tv < dimword (:256) /\
    alloca_history fn entry ==>
    ?child new. EntryChildResources ctx fn site ready st1 limit_st tv vs d k entry child new /\
      EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
      entry_decoder_obs entry child /\ alloca_history fn child) ==>
  ?t scratch. EntryLoopInv ctx fn site st end_st limit_st ce ty tv vs maxn hdr
      src srcword dst ip d p iid oid base_addr cap sb bs b reserve_cap initial
      (LENGTH vs) t scratch /\
    EntryLoopSafe ctx fn s t /\ EntryLoopPull ctx fn s t /\
    entry_decoder_obs s t /\ alloca_history fn t
Proof
  strip_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] entry_joint_loop_finite) >>
  reverse conj_tac
  >- (asm_rewrite_tac[] >> qexistsl_tac [`j`, `old`] >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k head entry. _` (qspec_then `k` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_tac >>
  drule_all entry_joint_header_successor >>
  strip_tac >> qexistsl_tac [`v`, `new`] >> asm_rewrite_tac[]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry joint loop inherited admission"
    end) [entry_setup_frame_refl, entry_setup_frame_trans,
          entry_joint_loop_safe_refl, entry_joint_loop_pull_refl,
          entry_joint_loop_safe_trans, entry_joint_loop_pull_trans,
          entry_joint_fixed_successor, entry_joint_identity_child,
          entry_joint_child_control, entry_joint_loop_control,
          entry_joint_empty_setup_endpoint, entry_joint_loop_finite,
          entry_joint_backedge_transfer, entry_joint_setup_resources,
          entry_joint_valid_setup, entry_joint_ordinary_child,
          entry_joint_chosen_successor, entry_joint_empty_setup,
          entry_joint_empty_child, entry_joint_header_successor,
          entry_joint_loop_from_header];
