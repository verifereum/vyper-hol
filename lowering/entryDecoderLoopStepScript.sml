(* Resource projection and frames on one chosen nonbulk successor. *)
Theory entryDecoderLoopStep
Ancestors
  calldataStaticChildSetup abiDecoderValidArrayEntry calldataDynStep
  entryDecoderHistoryFrame successfulSequenceEndpoint
  abiDecoderTypedContract instIdxIndep calldataValidOwnedStep calldataDynOwned
  abiDecoderLoopRegisters abiDecoderArrayBackedge decoderPrefixEdges
  calldataSafeIteration
  calldataOwnedSuccessorEndpoint entryDecoderEndpointValidation
  entryDecoderRelationIteration entryDecoderSetupEndpoint
  calldataOwnedLoopClosure entryDecoderStateFrame abiDecoderExecution
  abiDecoderContract abiDecoderDynamicLoopSetup abiDecoderLoopSetup
  abiDecoderReentry abiDecoderReentryAddress abiDecoderArraySetupInputs
  compileEnv exprLoweringProps allocaHistory fragExecMem
  words list rich_list arithmetic finite_map venomState venomExecSemantics venomInstProofs1
  abiDecoderDynamic abiDecoderIndexedAddress abiEncoder emitHelper venomInst
  pred_set

Theorem entry_owned_fixed_successor_frame:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s);
      H = \j s scratch.
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
        Own st.cs_next_id end_st.cs_next_id s /\
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
  in
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) u.vs_memory) /\
  st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= st1.cs_next_id /\
  st1.cs_next_id <= end_st.cs_next_id /\
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  p < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (iid < ready.cs_next_id \/ st1.cs_next_id <= iid) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  nvar < limit_st.cs_next_var /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
  entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
  entry.vs_alloca_next = u.vs_alloca_next /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
  ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
  child.vs_inst_idx = LENGTH st1.cs_current_insts /\
  val_wf tv (EL j vs) /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
  fresh_vars_wrt limit_st child /\
  child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
  alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
  Own ready.cs_next_id st1.cs_next_id child /\
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
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child)) /\
  Safe u entry /\ Pull u entry /\ Safe entry child /\ Pull entry child /\
  Safe child v /\ Pull child v /\
  entry_decoder_obs initial u /\ entry_decoder_obs u entry /\
  entry_decoder_obs entry child /\ alloca_history fn child /\
  bb.bb_instructions = st1.cs_current_insts ++
    abi_decode_backedge_insts id iv (STRING #"%" (toString nvar)) ip hdr /\
  eval_operand (Var iv) child = SOME (n2w j) /\
  eval_operand ip child = SOME (n2w p) /\ ip <> Var (STRING #"%" (toString nvar)) ==>
  H (SUC j) v (old++new) /\
  (!k. k < SUC j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v /\ Pull u v /\
  entry_decoder_obs initial v /\ alloca_history fn v
Proof
  map_every (fn q => qmatch_goalsub_abbrev_tac q >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Own`, `LET _ Safe`, `LET _ Pull`, `LET _ H`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac calldata_owned_fixed_successor_endpoint >>
  map_every (fn q => qpat_assum q (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
    CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)))
    [`Abbrev (Own = _)`, `Abbrev (Safe = _)`, `Abbrev (Pull = _)`, `Abbrev (H = _)`] >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] entry_backedge_endpoint_frame) >>
  simp[Once w2n_n2w] >> strip_tac >>
  rpt conj_tac >> asm_rewrite_tac[] >>
  metis_tac[entry_decoder_obs_trans]
QED

Theorem entry_array_setup_chosen_valid[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  run_inst_seq (emitted_insts st ready) initial = OK prepared ==>
  abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
    (Lit 0w) sb d b cap st.cs_next_var limit_st initial prepared /\ inst_extends st ready
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (drule_all abi_decoder_valid_array_setup_sequence >>
      strip_tac >> gvs[]) >>
  drule_all calldata_static_valid_array_setup_sequence >> strip_tac >> gvs[]
QED

Theorem entry_source_valid_element_setup_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st.cs_next_var limit_st s t /\
    abi_decoder_address_frame st.cs_next_var s t /\ fresh_vars_wrt limit_st t /\
    inst_extends st ready /\ entry_decoder_obs s t /\ alloca_history fn t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d)` by
    fs[abi_decoder_ranges_def] >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  drule_all entry_array_setup_chosen_valid >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> drule_all entry_element_setup_total_frame >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ _) _` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `p`] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`P` |-> `\s:venom_state. T`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qexists_tac `t with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  fs[abi_decoder_address_frame_def, eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem entry_header_body_transfer_frame:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < n /\ n < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w n /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  abi_decoder_operand_live next src /\ alloca_history fn u /\
  head = jump_to body_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j n u) ==>
  entry_decoder_obs u head /\ alloca_history fn head /\
  ((!fuel. mem_safe_run fuel ctx fn head) ==> !fuel. mem_safe_run fuel ctx fn u)
Proof
  strip_tac >>
  `src <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `STRING #"%" (toString next) <> STRING #"%" (toString (next+1))` by simp[] >>
  `j <= n /\ mload (w2n (n2w p:bytes32)) u = n2w j /\
   w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] calldata_header_all_fuel_pullback) >>
  disch_then (drule_at (Pat `eval_operand ip u = _`)) >>
  disch_then (drule_at (Pat `eval_operand src u = _`)) >>
  asm_rewrite_tac[] >> strip_tac >>
  conj_tac
  >- (qpat_assum `head = _` (fn th => pure_rewrite_tac[th]) >>
      simp[entry_decoder_obs_def, abi_decode_header_state_def, jump_to_def,
           update_var_def]) >>
  conj_tac
  >- (qpat_assum `head = _` (fn th => pure_rewrite_tac[th]) >>
      irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `u` >>
      simp[abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  first_x_assum (qspecl_then [`head`, `body_bb`, `n`, `j`] mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem entry_valid_header_child_frame:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  alloca_inv u /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  ready.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn u)) /\
    ((!fuel. mem_safe_run fuel ctx fn entry) ==> !fuel. mem_safe_run fuel ctx fn u) /\
    entry_decoder_obs u entry /\ alloca_history fn entry
Proof
  strip_tac >> drule_all calldata_valid_header_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all entry_header_body_transfer_frame >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `alloca_inv head` by
    metis_tac[cj 1 calldata_alloca_invariants_fields] >>
  `head.vs_current_bb = st0.cs_current_bb /\
   head.vs_inst_idx = LENGTH st0.cs_current_insts /\
   mload (w2n (n2w p:bytes32)) head = n2w j /\
   w2n (n2w p:bytes32)+32 <= head.vs_alloca_next` by
    (qpat_x_assum `head = _` kall_tac >> simp[]) >>
  drule_all entry_source_valid_element_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `entry.vs_current_bb = ready.cs_current_bb` >>
  `entry_decoder_obs u entry` by metis_tac[entry_decoder_obs_trans] >>
  qexistsl_tac [`head`, `entry`] >> asm_rewrite_tac[] >>
  conj_tac >- fs[abi_decoder_address_frame_def] >>
  conj_tac >- fs[abi_decoder_address_frame_def] >>
  conj_tac >- fs[abi_decoder_address_frame_def] >>
  conj_tac >- fs[abi_decoder_address_frame_def] >>
  conj_tac >- fs[abi_decoder_address_frame_def] >>
  conj_tac >-
    (qpat_x_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> _` mp_tac >>
     qpat_x_assum `!op. abi_decoder_operand_live next op ==> _` mp_tac >>
     qpat_x_assum `next <= st0.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  conj_tac >- metis_tac[calldata_safe_transfer_trans] >> metis_tac[]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry loop successor inherited admission"
    end) [entry_owned_fixed_successor_frame, entry_array_setup_chosen_valid,
          entry_source_valid_element_setup_endpoint,
          entry_element_setup_total_frame, entry_header_body_transfer_frame,
          entry_valid_header_child_frame];
