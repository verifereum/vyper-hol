(* Conservative vocabulary for the jointly witnessed nonbulk array loop. *)
Theory entryDecoderJointLoop
Ancestors
  entryDecoderLoopStep entryDecoderRelationIteration
  entryDecoderEndpointValidation entryDecoderStateFrame words abiDecoderFrame
  calldataDynStep abiDecoderReentry abiDecoderReentryAddress abiDecoderLoopSetup
  entryDecoderSetupEndpoint entryDecoderHistoryFrame successfulSequenceEndpoint
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderContract
  fragExecMem instIdxIndep abiEncoder emitHelper exprLoweringProps
  list rich_list arithmetic venomInst

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
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
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
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
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
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
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
          entry_joint_empty_setup_endpoint, entry_joint_loop_finite];
