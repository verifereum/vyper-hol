(* Successful source-valued Bytes/String children in dynamic array loops. *)
Theory calldataValidOwnedBytesArray
Ancestors
  calldataValidOwnedBytes calldataValidOwnedArray abiDecoderValidArrayEntry
  abiDecoderCoherence abiDecoderContract compileEnv words list finite_map

Theorem calldata_valid_bytes_array_child[local]:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
  in
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),st1) /\ fn_has_code ready st1 fn /\
  st1.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_valid_array_entry ce env sf ty tv bs vs k ready ops CALLDATALOAD
    (Lit 0w) sb d b cap next limit_st head entry /\
  ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
  entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
  alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
  Own ready.cs_next_id st1.cs_next_id entry /\
  FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ st1.cs_next_id <= oid) /\
  base_addr <= d+32+k*type_memory_size tv /\
  d+32+k*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
  d+32+k*type_memory_size tv+type_memory_size tv < dimword (:256) ==>
  ?child new.
    ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
    child.vs_inst_idx = LENGTH st1.cs_current_insts /\
    val_wf tv (EL k vs) /\
    val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) child.vs_memory /\
    fresh_vars_wrt limit_st child /\
    child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
    alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
    Own ready.cs_next_id st1.cs_next_id child /\
    entry.vs_alloca_next <= child.vs_alloca_next /\
    (!id q len. FLOOKUP entry.vs_allocas id = SOME (q,len) ==>
      FLOOKUP child.vs_allocas id = SOME (q,len)) /\
    (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
      FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
    (!op. abi_decoder_operand_live ready.cs_next_var op ==>
      eval_operand op child = eval_operand op entry) /\
    abi_decode_footprint_frame
      ((d+32+k*type_memory_size tv,type_memory_size tv)::new) entry child /\
    (!q len. MEM (q,len) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP child.vs_allocas id = SOME (q,len)) /\ Safe entry child
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
      SIMP_RULE (srw_ss()) [abi_decoder_valid_array_entry_def, LET_THM]) >>
  qpat_assum `type_memory_bytes ce ty = _`
    (fn th => qpat_x_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    calldata_valid_bytes_owned_success)) >> strip_tac >>
  qexistsl_tac [`child`, `[]`] >> BETA_TAC >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_assum `child.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `child.vs_alloca_next = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [])]
QED

Theorem calldata_valid_bytes_array_owned_success:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      H = \j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
        mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
        s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
        FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (p,32) /\
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
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ LENGTH vs < dimword (:256) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  Own st.cs_next_id end_st.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  fresh_vars_wrt limit_st initial /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),prefix_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st prefix_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
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
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  EVERY (val_wf tv) vs /\ p < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (header_st.cs_next_id < ready.cs_next_id \/ st1.cs_next_id <= header_st.cs_next_id) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var /\
  nvar < limit_st.cs_next_var /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),st1) /\ fn_has_code ready st1 fn /\
  st1.cs_next_var <= limit_st.cs_next_var /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?v scratch out. H (LENGTH vs) v scratch /\
    (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\
    out = jump_to exit_lbl (abi_decode_header_state
      (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
      (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
      (LENGTH vs) (LENGTH vs) v) /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d out.vs_memory /\
    out.vs_memory = v.vs_memory /\ out.vs_call_ctx = v.vs_call_ctx /\
    out.vs_data_section = v.vs_data_section /\ out.vs_allocas = v.vs_allocas /\
    out.vs_alloca_next = v.vs_alloca_next /\
    (alloca_inv out <=> alloca_inv v) /\
    (alloca_frontier_inv ctx fn site out <=> alloca_frontier_inv ctx fn site v) /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op out = eval_operand op v) /\
    Safe initial out
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp_tac (srw_ss()) [abi_decoder_coherent_array_iff] >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  mp_tac (SPEC_ALL calldata_valid_owned_array_success) >>
  simp_tac (pure_ss ++ boolSimps.LET_ss) [] >>
  map_every (fn pat => qpat_assum pat
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >> BETA_TAC)
    [`Abbrev (Own = _)`, `Abbrev (Safe = _)`, `Abbrev (H = _)`] >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      (Q.SUBGOAL_THEN `oid < ready.cs_next_id \/ st1.cs_next_id <= oid` assume_tac
       >- decide_tac) >>
      qpat_x_assum `Own ready.cs_next_id st1.cs_next_id entry` mp_tac >>
      simp_tac pure_ss [Abbr `Own`] >> BETA_TAC >> strip_tac >>
      drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
        calldata_valid_bytes_array_child)) >>
      simp_tac pure_ss [Abbr `Safe`] >> BETA_TAC >>
      disch_then ACCEPT_TAC) >>
  simp[]
QED
