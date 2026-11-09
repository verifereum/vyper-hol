(* Source-indexed successful iteration of the owned calldata array loop. *)
Theory calldataValidOwnedLoop
Ancestors
  calldataValidOwnedStep calldataDynOwned calldataSafeIteration
  abiDecoderValidArrayEntry venomMemDefs

Theorem calldata_valid_owned_header_iterate:
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
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
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
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
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
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  (!k h scratch. k < LENGTH vs /\ H k h scratch ==>
    !head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) k (LENGTH vs) h) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs k ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    Own ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
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
        FLOOKUP child.vs_allocas id = SOME (q,len)) /\ Safe entry child) /\
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  ?v scratch. H (LENGTH vs) v scratch /\
    (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v /\
    (!next_bb t. lookup_block exit_lbl fn.fn_blocks = SOME next_bb /\
      phi_prefix_length next_bb.bb_instructions = 0 /\
      t = jump_to exit_lbl (abi_decode_header_state
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        (LENGTH vs) (LENGTH vs) v) ==>
      val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
      t.vs_memory = v.vs_memory /\ t.vs_call_ctx = v.vs_call_ctx /\
      t.vs_data_section = v.vs_data_section /\ t.vs_allocas = v.vs_allocas /\
      t.vs_alloca_next = v.vs_alloca_next /\
      (alloca_inv t <=> alloca_inv v) /\
      (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site v) /\
      (!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op v) /\
      Safe u t)
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k h scratch. k < LENGTH vs /\ H k h scratch /\
    (!i. i < k ==> val_in_memory tv (EL i vs)
      (d+32+i*type_memory_size tv) h.vs_memory) ==>
    ?v new. H (SUC k) v (scratch++new) /\
      (!i. i < SUC k ==> val_in_memory tv (EL i vs)
        (d+32+i*type_memory_size tv) v.vs_memory) /\ Safe h v` by
    suspend "step" >>
  `?v scratch. H (LENGTH vs) v scratch /\
    (!k. k < LENGTH vs ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v` by
    suspend "iterate" >>
  qexistsl_tac [`v`, `scratch`] >> asm_rewrite_tac[] >>
  suspend "terminal"
QED
Resume calldata_valid_owned_header_iterate[step]:
  rpt gen_tac >> strip_tac >>
  `p+32 <= h.vs_alloca_next` by
    (qpat_assum `H k h scratch` mp_tac >>
     simp_tac pure_ss [Abbr `H`] >> BETA_TAC >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     qpat_x_assum `alloca_inv h` mp_tac >>
     simp[alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`j` |-> `k`, `u` |-> `h`, `old` |-> `scratch`]
    (SPEC_ALL calldata_valid_owned_header_step)) >>
  simp_tac (pure_ss ++ boolSimps.LET_ss) [] >>
  map_every (fn pat => qpat_assum pat
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >> BETA_TAC)
    [`Abbrev (Own = _)`, `Abbrev (Safe = _)`, `Abbrev (H = _)`] >>
  (impl_tac >- (asm_rewrite_tac[] >>
    qpat_x_assum `!k h scratch. _`
      (qspecl_then [`k`, `h`, `scratch`] mp_tac) >> simp[])) >>
  simp_tac bool_ss []
QED
Resume calldata_valid_owned_header_iterate[iterate]:
  `j <= LENGTH vs` by
    (qpat_assum `H j u old` mp_tac >>
     simp_tac pure_ss [Abbr `H`] >> BETA_TAC >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> asm_rewrite_tac[]) >>
  `!s. Safe s s` by (simp[Abbr `Safe`] >> metis_tac[]) >>
  `!s t v. Safe s t /\ Safe t v ==> Safe s v` by
    (simp_tac (pure_ss ++ boolSimps.LET_ss) [Abbr `Safe`] >>
     BETA_TAC >> rpt gen_tac >> MATCH_ACCEPT_TAC calldata_safe_transfer_trans) >>
  qpat_assum `!k h scratch. k < _ /\ H k h scratch /\ _ ==> _` mp_tac >>
  qpat_assum `!s. Safe s s` mp_tac >>
  qpat_assum `!s t v. Safe s t /\ Safe t v ==> _` mp_tac >>
  qpat_assum `H j u old` mp_tac >>
  qpat_assum `!k. k < j ==> _` mp_tac >>
  qpat_assum `j <= LENGTH vs` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `H j u old` mp_tac >>
  qpat_x_assum `!k. k < j ==> _` mp_tac >>
  qpat_x_assum `j <= LENGTH vs` mp_tac >>
  qid_spec_tac `old` >> qid_spec_tac `u` >>
  completeInduct_on `LENGTH vs-j` >> rpt strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (gvs[] >> qexistsl_tac [`u`, `old`] >> asm_rewrite_tac[]) >>
  `j < LENGTH vs` by decide_tac >>
  qpat_assum `!k h scratch. k < LENGTH vs /\ H k h scratch /\ _ ==> _`
    (qspecl_then [`j`, `u`, `old`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `Safe u next_state` >>
  qpat_x_assum `!m. m < _ ==> !vs j. _` (qspec_then `LENGTH vs-SUC j` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`vs`, `SUC j`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`next_state`, `old++new`] mp_tac) >>
  (impl_tac >- (qx_gen_tac `i` >> disch_tac >>
    `d + (i * type_memory_size tv + 32) = d+32+i*type_memory_size tv`
      by decide_tac >>
    asm_rewrite_tac[] >>
    qpat_x_assum `!i. i < SUC j ==> _` (qspec_then `i` mp_tac) >>
    asm_rewrite_tac[])) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choose_then `endpoint` (qx_choose_then `scratch` strip_assume_tac)) >>
  qexistsl_tac [`endpoint`, `scratch`] >> asm_rewrite_tac[] >>
  first_x_assum irule >> qexists_tac `next_state` >> asm_rewrite_tac[]
QED
Resume calldata_valid_owned_header_iterate[terminal]:
  qpat_x_assum `!k h scratch. k < _ /\ H k h scratch ==> _` kall_tac >>
  qpat_x_assum `!k h scratch. k < _ /\ H k h scratch /\ _ ==> _` kall_tac >>
  qpat_x_assum `H j u old` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `H (LENGTH vs) v scratch` mp_tac >>
  simp_tac pure_ss [Abbr `H`] >> BETA_TAC >> strip_tac >>
  `p+32 <= v.vs_alloca_next` by
    (qpat_assum `alloca_inv v` mp_tac >>
     qpat_assum `FLOOKUP v.vs_allocas iid = SOME (p,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `src <> Var (STRING #"%" (toString next))` by
    (irule calldata_live_excludes_generated >> qexists_tac `next` >>
     asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `STRING #"%" (toString next) <> STRING #"%" (toString (next+1))` by
    simp[] >>
  `mload (w2n (n2w p:bytes32)) v = n2w (LENGTH vs)` by simp[] >>
  `w2n (n2w p:bytes32)+32 <= v.vs_alloca_next` by simp[] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions := abi_decode_header_insts hid ip src
      CALLDATALOAD (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) body_lbl exit_lbl|>` by simp[] >>
  `!op. abi_decoder_operand_live next op ==>
    op <> Var (STRING #"%" (toString next)) /\
    op <> Var (STRING #"%" (toString (next+1))) /\
    op <> Var (STRING #"%" (toString (next+2))) /\
    op <> Var (STRING #"%" (toString (next+3)))` by suspend "excludes" >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`n` |-> `LENGTH vs`] (SPEC_ALL calldata_terminal_header_array))) >>
  disch_then (qspecl_then [`site`, `ctx`] (mk_asm "terminal")) >>
  qpat_assum `t = jump_to _ _` (fn th =>
    asm_x "terminal" (mp_tac o ONCE_REWRITE_RULE [GSYM th])) >>
  qpat_assum `Safe u v` mp_tac >>
  qpat_assum `Abbrev (Safe = _)` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live next op ==> _ /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 3 disch_tac >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> first_x_assum drule >> simp[]) >>
  suspend "transfer"
QED
Resume calldata_valid_owned_header_iterate[excludes]:
  qx_gen_tac `op` >> disch_tac >>
  qpat_assum `abi_decoder_operand_live next op` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> disch_tac >> rpt conj_tac >>
  irule calldata_live_excludes_generated >> qexists_tac `next` >>
  asm_rewrite_tac[] >> decide_tac
QED
Resume calldata_valid_owned_header_iterate[transfer]:
  `Safe v t` by
    (qpat_x_assum `!fuel. _` mp_tac >>
     simp_tac bool_ss [Abbr `Safe`]) >>
  qpat_assum `Safe u v` mp_tac >> qpat_assum `Safe v t` mp_tac >>
  simp_tac pure_ss [Abbr `Safe`] >> BETA_TAC >>
  POP_ASSUM_LIST (K all_tac) >> ntac 2 disch_tac >>
  metis_tac[calldata_safe_transfer_trans]
QED
Finalise calldata_valid_owned_header_iterate
Finalise calldata_valid_owned_header_iterate
