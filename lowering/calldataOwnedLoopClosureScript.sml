(* Same-endpoint terminal and finite-loop composition for owned calldata arrays. *)
Theory calldataOwnedLoopClosure
Ancestors
  calldataOwnedSuccessorEndpoint decoderPrefixEdges calldataSafeIteration
  calldataDynOwned abiDecoderLoopRegisters abiDecoderDynamic abiDecoderContract
  abiEncoder abiDecoderExecution abiDecoderArrayBackedge abiDecoderFrame
  exprLoweringProps allocaFrontierBound venomMemDefs calldataValidInitHeader
  venomState venomExecSemantics words list arithmetic

Theorem calldata_owned_terminal_endpoint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  abi_decoder_operand_live next src /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcword /\
  mload (w2n p) s = n2w (LENGTH vs) /\
  abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
  LENGTH vs < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  LENGTH vs <= maxn /\ EVERY (val_wf tv) vs /\
  mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
  (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) s.vs_memory) /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t.
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (alloca_inv t <=> alloca_inv s) /\
    (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  `src <> Var (STRING #"%" (toString next))` by
    (drule abi_decoder_live_excludes_output >> simp[]) >>
  `STRING #"%" (toString (next:num)) <> STRING #"%" (toString (next+1))` by simp[] >>
  qabbrev_tac `t = jump_to exit_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) (LENGTH vs) (LENGTH vs) s)` >>
  `t = jump_to exit_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) (LENGTH vs) (LENGTH vs) s)` by simp[Abbr `t`] >>
  `(!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s` by
    (ho_match_mp_tac (GEN_ALL calldata_header_all_fuel_pullback) >>
     goal_assum (drule_at (Pos hd)) >>
     qexistsl_tac [`srcword`,`p`,`exit_bb`,`LENGTH vs`,`LENGTH vs`] >>
     simp_tac bool_ss [LESS_EQ_REFL, prim_recTheory.LESS_REFL] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  drule_all calldata_terminal_header_array >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`LENGTH vs`,`LENGTH vs`] strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0` by
    simp[Abbr `t`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  `fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`, abi_decoder_fresh_jump] >> first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s` by
    (simp_tac bool_ss [Abbr `t`, abi_decoder_operand_jump] >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The loop invariant is allowed to retain its scratch list existentially.
   Both continuation relations travel along the same chosen finite path. *)
Theorem owned_loop_finite[local]:
  !bound i Inv Q Rel s.
    (!a b c. Rel a b /\ Rel b c ==> Rel a c) /\
    i <= bound /\ Inv i s /\
    (!j u. Inv j u /\ j < bound ==> ?v. Inv (SUC j) v /\ Rel u v) /\
    (!u. Inv bound u ==> ?v. Q v /\ Rel u v) ==>
    ?t. Q t /\ Rel s t
Proof
  completeInduct_on `bound-i` >> rpt strip_tac >>
  Cases_on `i = bound` >- metis_tac[] >>
  `i < bound` by decide_tac >>
  `?v. Inv (SUC i) v /\ Rel s v` by metis_tac[] >>
  rename1 `Inv (SUC i) next` >>
  `?t. Q t /\ Rel next t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `bound-SUC i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`bound`,`SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `Inv` >> simp[]) >>
  metis_tac[]
QED

Theorem owned_loop_safe_pull_finite[local]:
  let Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s)
  in
  i <= bound /\ Inv i s /\
  (!j u. Inv j u /\ j < bound ==> ?v. Inv (SUC j) v /\ Safe u v /\ Pull u v) /\
  (!u. Inv bound u ==> ?v. Q v /\ Safe u v /\ Pull u v) ==>
  ?t. Q t /\ Safe s t /\ Pull s t
Proof
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >> strip_tac >>
  irule (BETA_RULE (Q.INST [`Rel` |-> `\a b. Safe a b /\ Pull a b`]
    (SPEC_ALL owned_loop_finite))) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (qpat_x_assum `!j u. _` kall_tac >>
          qpat_x_assum `!u. _` kall_tac >>
          gvs[Abbr `Safe`] >> metis_tac[]) >>
      gvs[Abbr `Pull`]) >>
  qexistsl_tac [`Inv`,`bound`,`i`] >> asm_rewrite_tac[]
QED

(* Finite header-to-header closure uses the actual compiled child and backedge,
   not a supplied execution step.  Initialization and the terminal edge are
   deliberately separate phases of the array producer. *)
Theorem calldata_owned_loop_from_header:
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
        abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
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
  EVERY (val_wf tv) vs /\ LENGTH vs < dimword (:256) /\ p < dimword (:256) /\
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
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  (!j u head entry.
    j < LENGTH vs /\
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    Own ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) ==>
    ?child new.
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
        FLOOKUP child.vs_allocas id = SOME (q,k)) /\ Safe entry child /\ Pull entry child) /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\ Safe u t /\ Pull u t
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v scratch. H (LENGTH vs) v scratch /\
    (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v /\ Pull u v` by
    suspend "iterate" >>
  suspend "terminal"
QED

Resume calldata_owned_loop_from_header[iterate]:
  `!a s scratch.
    H a s scratch /\
    (!k. k < a ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) s.vs_memory) /\ a < LENGTH vs ==>
    ?v new. H (SUC a) v (scratch++new) /\
      (!k. k < SUC a ==> val_in_memory tv (EL k vs)
        (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe s v /\ Pull s v` by
    (rpt gen_tac >> strip_tac >> suspend "successor") >>
  suspend "finite"
QED

Resume calldata_owned_loop_from_header[successor]:
  `p+32 <= s.vs_alloca_next` by
    (qpat_assum `H a s scratch` mp_tac >>
     simp_tac bool_ss [Abbr `H`] >> strip_tac >>
     qhdtm_x_assum `alloca_inv` mp_tac >>
     qpat_x_assum `FLOOKUP s.vs_allocas iid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`j` |-> `a`, `u` |-> `s`, `old` |-> `scratch`]
    (SPEC_ALL calldata_owned_header_successor_endpoint)) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (Own = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  qpat_assum `Abbrev (Safe = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  qpat_assum `Abbrev (Pull = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  qpat_assum `Abbrev (H = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  impl_tac >- suspend "premises" >>
  disch_then ACCEPT_TAC
QED

Resume calldata_owned_loop_from_header[premises]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `!j u head entry. _`
        (qspecl_then [`a`,`s`] mp_tac) >>
      qpat_assum `a < LENGTH vs` (fn th => simp_tac bool_ss [th])) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume calldata_owned_loop_from_header[finite]:
  qabbrev_tac `Inv = \i s. ?scratch. H i s scratch /\
    (!k. k < i ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) s.vs_memory)` >>
  `?v. Inv (LENGTH vs) v /\ Safe u v /\ Pull u v` suffices_by
    (simp_tac bool_ss [Abbr `Inv`] >> metis_tac[]) >>
  mp_tac (Q.INST [`i` |-> `j`, `bound` |-> `LENGTH (vs:value list)`, 
    `Q` |-> `Inv (LENGTH (vs:value list))`, `s` |-> `u`]
    (SPEC_ALL owned_loop_safe_pull_finite)) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (Safe = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  qpat_assum `Abbrev (Pull = _)` (fn th => pure_rewrite_tac
    [GSYM (BETA_RULE (SIMP_RULE pure_ss [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  impl_tac >- suspend "finite_inputs" >> disch_then ACCEPT_TAC
QED

Resume calldata_owned_loop_from_header[finite_inputs]:
  conj_tac
  >- (qpat_assum `H j u old` mp_tac >>
      simp_tac bool_ss [Abbr `H`] >> strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp_tac bool_ss [Abbr `Inv`] >> qexists_tac `old` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- suspend "finite_step" >>
  gen_tac >> disch_tac >> qexists_tac `u'` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac bool_ss [Abbr `Safe`, Abbr `Pull`] >>
  rpt strip_tac >> qexists_tac `fuel` >> simp_tac bool_ss []
QED

Resume calldata_owned_loop_from_header[finite_step]:
  simp_tac bool_ss [Abbr `Inv`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a s scratch. _` drule >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `v` >>
  conj_tac
  >- (qexists_tac `scratch++new` >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume calldata_owned_loop_from_header[terminal]:
  qpat_assum `H (LENGTH vs) v scratch` mp_tac >>
  simp_tac bool_ss [Abbr `H`] >> strip_tac >>
  `p+32 <= v.vs_alloca_next` by
    (qhdtm_assum `alloca_inv` mp_tac >>
     qpat_assum `FLOOKUP v.vs_allocas iid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `w2n (n2w p : bytes32) = p` by simp[] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|>` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `v`, `pw` |-> `(n2w p : bytes32)`]
    (Q.INST [`p` |-> `pw`] (SPEC_ALL calldata_owned_terminal_endpoint))) >>
  impl_tac >- suspend "terminal_inputs" >>
  strip_tac >> suspend "terminal_resources"
QED

Resume calldata_owned_loop_from_header[terminal_inputs]:
  qpat_assum `w2n (n2w p : bytes32) = p` (fn th => pure_rewrite_tac [th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume calldata_owned_loop_from_header[terminal_resources]:
  `Own st.cs_next_id end_st.cs_next_id t` by
    (qpat_assum `Own st.cs_next_id end_st.cs_next_id v` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th => pure_rewrite_tac
       [SIMP_RULE pure_ss [markerTheory.Abbrev_def] th]) >> BETA_TAC >>
     qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `t.vs_alloca_next = v.vs_alloca_next` (fn th => pure_rewrite_tac [th]) >>
     simp_tac bool_ss []) >>
  `Safe u t /\ Pull u t` by suspend "terminal_transfers" >>
  qexistsl_tac [`t`,`scratch`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "terminal_fields"
QED

Resume calldata_owned_loop_from_header[terminal_transfers]:
  conj_tac
  >- (qpat_x_assum `Safe u v` mp_tac >>
      simp_tac bool_ss [Abbr `Safe`] >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn t = r /\ _ ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qpat_x_assum `Pull u v` mp_tac >>
  simp_tac bool_ss [Abbr `Pull`] >>
  qpat_x_assum `(!fuel. mem_safe_run fuel ctx fn t) ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Resume calldata_owned_loop_from_header[terminal_fields]:
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
    [`t.vs_call_ctx = v.vs_call_ctx`, `t.vs_data_section = v.vs_data_section`,
     `t.vs_allocas = v.vs_allocas`, `t.vs_alloca_next = v.vs_alloca_next`,
     `alloca_inv t <=> alloca_inv v`,
     `alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site v`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "terminal_live" >>
  conj_tac
  >- (qpat_assum `abi_decode_footprint_frame _ initial v` mp_tac >>
      simp_tac bool_ss [abi_decode_footprint_frame_def] >>
      map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
        [`t.vs_memory = v.vs_memory`, `t.vs_call_ctx = v.vs_call_ctx`,
         `t.vs_data_section = v.vs_data_section`] >>
      simp_tac bool_ss []) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume calldata_owned_loop_from_header[terminal_live]:
  rpt strip_tac >>
  `abi_decoder_operand_live next op` by
    (qpat_x_assum `!op. op = src \/ _ ==> _` (qspec_then `op` mp_tac) >>
     qpat_assum `abi_decoder_operand_live st.cs_next_var op` mp_tac >>
     rpt (pop_assum kall_tac) >> simp_tac bool_ss []) >>
  qpat_x_assum `!op. abi_decoder_operand_live next op ==> eval_operand op t = _` drule >>
  qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` drule >>
  rpt (pop_assum kall_tac) >> simp_tac bool_ss []
QED

Finalise calldata_owned_loop_from_header

(* Initializer boundary audit: calldata_valid_init_header's H, instantiated
   from polymorphic vs to value list, is alpha-equivalent after LET/beta
   normalization to this H with iid = header_st.cs_next_id. At j=0 the
   additional decoded-prefix premise is vacuous. Actual compiler ID/variable
   bounds, liveness, block lookups and recursive-child specialization remain
   obligations of the coherent decoder consumer, not of this branch rule. *)
