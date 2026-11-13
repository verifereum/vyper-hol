Theory calldataExactDyn
Ancestors
  calldataExactDynInit calldataExactDynStep calldataExactDynIteration calldataExactDynInitAdapter
  calldataAggregateTyped abiDecoderCoherence calldataSourceCorrespondence vyperCalldata vyperCalldataProps
  abiDecoderArrayLoopInit abiEncoder abiDecoderContract fragExecMem
  arithmetic list words finite_map venomExecSemantics venomState compileEnv
  venomMemDefs abiDecoderExecution emitHelper valueEncodingDefs valueEncodingProps valueEncoding vyperValue vyperTyping vyperAST

Theorem calldata_exact_nonbulk_array_owned_run:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  di = type_to_abi_dec_info sf ce ty /\
  abi_sz = abi_embedded_static_size ce.ce_struct_fields ty /\
  abi_sz = tv_abi_size tv /\ dec_info_needs_offset di = tv_abi_dynamic tv /\
  (tv_abi_dynamic tv \/ tv_needs_clamp tv) /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (Lit 0w) di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),end_st) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\ fn_has_code st1 end_st fn /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\ lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  alloca_inv initial /\ ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (cd_decode F u.vs_call_ctx.cc_calldata tv (w2n w) = NONE /\
     ?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
    ?v x scratch. cd_decode F u.vs_call_ctx.cc_calldata tv (w2n w) = SOME x /\
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==> ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata (ArrayTV tv (Dynamic maxn)) (w2n srcword) = NONE /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\ mem_safe_run fuel ctx fn initial) \/
  ?t x scratch.
    cd_decode F initial.vs_call_ctx.cc_calldata (ArrayTV tv (Dynamic maxn)) (w2n srcword) = SOME x /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    value_has_type (ArrayTV tv (Dynamic maxn)) x /\ val_wf (ArrayTV tv (Dynamic maxn)) x /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) x d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size (ArrayTV tv (Dynamic maxn)))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size (ArrayTV tv (Dynamic maxn)) = 32+maxn*type_memory_size tv` by
    (POP_ASSUM_LIST (K all_tac) >> rewrite_tac[type_memory_size_def]) >>
  qpat_assum `type_memory_size (ArrayTV _ _) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> pure_rewrite_tac[th]) >>
  `maxn < dimword (:256)` by suspend "bound" >>
  `header_st.cs_next_id < end_st.cs_next_id` by decide_tac >>
  `32 <= 32+maxn*type_memory_size tv` by decide_tac >>
  drule_all calldata_exact_owned_header_initial >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- suspend "count_rejected" >>
  suspend "iterate"
QED
Resume calldata_exact_nonbulk_array_owned_run[bound]:
  drule abi_decoder_coherent_header >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `evaluate_type env (ArrayT ty (Dynamic maxn)) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_type_def, AllCaseEqs(), type_slot_size_def, bound_length_def] >>
  rpt strip_tac >>
  `maxn <= maxn * type_slot_size tv` by
    (Cases_on `type_slot_size tv` >> fs[MULT_CLAUSES]) >>
  decide_tac
QED
Resume calldata_exact_nonbulk_array_owned_run[count_rejected]:
  disj1_tac >> conj_tac
  >- (qpat_assum `maxn < w2n _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[Once cd_decode_def, calldata_decode_load_word]) >>
  qexistsl [`fuel`,`z`] >> asm_rewrite_tac[]
QED
Resume calldata_exact_nonbulk_array_owned_run[iterate]:
  rename1 `mload p start = 0w` >>
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_x_assum `Abbrev (Own = _)`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
      pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))] >> assume_tac th) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_x_assum `Abbrev (Rel = _)`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
      pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))] >> assume_tac th) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qabbrev_tac `n = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `cd = initial.vs_call_ctx.cc_calldata` >>
  qabbrev_tac `srcbase = cd_at F (w2n srcword) 32` >>
  qabbrev_tac `H = \i s.
    ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ i <= n /\ n <= maxn /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    eval_operand ip s = SOME (n2w p) /\ mload p s = n2w i /\
    mem_word_at d s.vs_memory = n2w n /\
    s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
    FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    Own st.cs_next_id end_st.cs_next_id s /\ initial.vs_alloca_next <= s.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP s.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op s = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
      !q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP s.vs_allocas id = SOME (q,k)` >>
  qabbrev_tac `Q = \xs t.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\ initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
      !q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k)` >>
  `H 0 start` by suspend "initial_invariant" >>
  `(!u. Rel u u) /\ (!u v w. Rel u v /\ Rel v w ==> Rel u w) /\
    (!u v. Rel u v /\ X v ==> X u)` by suspend "transfer_laws" >>
  `!i u. i < n /\ H i u ==>
    (cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = NONE /\ X u) \/
    ?v x. cd_decode F cd tv (cd_member_ptr F cd tv srcbase (i*tv_abi_size tv)) = SOME x /\
      H (SUC i) v /\ value_has_type tv x /\ val_wf tv x /\
      val_in_memory tv x (d+32+i*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+i*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+i*type_memory_size tv) u.vs_memory /\ Rel u v`
    by suspend "step" >>
  `!u xs. H n u /\ LENGTH xs = n /\ cd_decode_elems F cd tv srcbase 0 n = SOME xs /\
    EVERY (value_has_type tv) xs /\ EVERY (val_wf tv) xs /\
    (!k. k < n ==> val_in_memory tv (EL k xs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    ?t. Q xs t /\ Rel u t` by suspend "terminal" >>
  drule_all calldata_exact_owned_iteration >>
  suspend "finish"
QED
Resume calldata_exact_nonbulk_array_owned_run[initial_invariant]:
  simp_tac bool_ss [Abbr `H`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `n`] >>
  ntac 11 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists `scratch` >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED
Resume calldata_exact_nonbulk_array_owned_run[transfer_laws]:
  qpat_assum `Abbrev (Rel = _)` mp_tac >>
  qpat_assum `Abbrev (X = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [markerTheory.Abbrev_def] >>
  disch_then SUBST1_TAC >> disch_then SUBST1_TAC >>
  simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> qexists `fuel` >> asm_rewrite_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!fuel. (!err. run_from fuel ctx fn w <> Error err) ==> _` (qspec_then `fuel` mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `!fuel. _` (qspec_then `fuel'` mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      qexists `fuel''` >> metis_tac[]) >>
  rpt strip_tac >> qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> metis_tac[]
QED
Resume calldata_exact_nonbulk_array_owned_run[step]:
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [Abbr `X`] >>
  irule (BETA_RULE (Q.INST [`D` |-> `\j. cd_decode F cd tv
    (cd_member_ptr F cd tv srcbase (j*tv_abi_size tv))`]
    calldata_exact_owned_header_step)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp_tac bool_ss [Abbr `Rel`] >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`
    (fn th => irule_at Any th) >>
  qpat_assum `lookup_block hdr _ = _`
    (fn th => irule_at (Pat `lookup_block _ _ = SOME
      <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`) th) >>
  qpat_assum `lookup_block st1.cs_current_bb _ = _` (fn th => irule_at Any th) >>
  qpat_assum `Abbrev (H = _)`
    (fn th => irule_at Any (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
  qexists_tac `body_bb` >>
  `p < dimword (:256)` by
    (qpat_assum `Own _ _ start` mp_tac >>
     qpat_assum `FLOOKUP start.vs_allocas header_st.cs_next_id = _` mp_tac >>
     simp_tac bool_ss [Abbr `Own`] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`header_st.cs_next_id`,`p`,`32`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  `n < dimword (:256)` by simp[Abbr `n`] >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [GSYM markerTheory.Abbrev_def] >>
  conj_tac >- suspend "callback" >>
  conj_tac >- simp[Abbr `n`] >>
  conj_tac >- simp_tac bool_ss [Abbr `Own`] >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def]
QED
Resume calldata_exact_nonbulk_array_owned_run[callback]:
  qx_gen_tac `a` >> strip_tac >>
  `w2n (if tv_abi_dynamic tv then n2w (w2n srcword + 32) +
      abi_decode_load CALLDATALOAD (n2w (w2n srcword + 32 + i * tv_abi_size tv) : bytes32) initial
      else n2w (w2n srcword + 32 + i * tv_abi_size tv) : bytes32) =
    cd_member_ptr F cd tv srcbase (i * tv_abi_size tv)` by
    (simp[cd_member_ptr_def, cd_at_def, Abbr `srcbase`, Abbr `cd`,
       calldata_decode_load_word, word_add_n2w, ADD_MOD, MOD_MOD, w2n_n2w] >>
     Cases_on `tv_abi_dynamic tv` >>
     simp[calldata_decode_load_word, word_add_def, w2n_n2w, ADD_MOD, MOD_MOD]) >>
  qmatch_asmsub_abbrev_tac `eval_operand (FST (SND ops)) a = SOME cw` >>
  qpat_x_assum `!u w e. ~u.vs_halted /\ _ ==> _`
    (qspecl_then [`a`,`cw`,`d+32+i*type_memory_size tv`] mp_tac) >>
  impl_tac >- simp[Abbr `Own`] >>
  simp_tac bool_ss [Abbr `cd`, Abbr `Rel`, Abbr `Own`] >>
  asm_rewrite_tac[]
QED
Resume calldata_exact_nonbulk_array_owned_run[terminal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `H n u` mp_tac >> simp_tac bool_ss [Abbr `H`] >> strip_tac >>
  `p < dimword (:256)` by
    (qpat_assum `Own _ _ u` mp_tac >>
     simp_tac bool_ss [Abbr `Own`] >> strip_tac >>
     first_x_assum (qspecl_then [`header_st.cs_next_id`,`p`,`32`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  `n < dimword (:256)` by simp[Abbr `n`] >>
  `abi_decode_load CALLDATALOAD srcword u = n2w n` by
    simp[calldata_decode_load_word, Abbr `n`, calldata_decode_load_word] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone` by
    (gen_tac >> strip_tac >> simp[]) >>
  qpat_assum `Own _ _ u` mp_tac >> simp_tac bool_ss [Abbr `Own`] >> strip_tac >>
  drule calldata_exact_owned_header_exit >>
  disch_then (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
  disch_then (drule_at (Pat `LENGTH _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block exit_lbl _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ u`)) >>
  disch_then (drule_at (Pat `eval_operand ip u = _`)) >>
  disch_then (drule_at (Pat `EVERY (val_wf _) _`)) >>
  disch_then (drule_at (Pat `end_st.cs_current_bb = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP u.vs_allocas _ = SOME (p,32)`)) >>
  disch_then (drule_at (Pat `eval_operand src u = _`)) >>
  disch_then (qspecl_then [`srcword`,`maxn`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists `t` >>
  simp_tac bool_ss [Abbr `Q`, Abbr `Rel`] >>
  reverse conj_tac
  >- (qpat_assum `!fuel r. run_from fuel ctx fn t = r /\ _ ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss []) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `EVERY (value_has_type tv) xs` mp_tac >>
    qpat_assum `LENGTH xs = n` mp_tac >> qpat_assum `n <= maxn` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[value_has_type_def, all_have_type_EVERY]) >>
  ntac 11 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists `scratch'` >> conj_tac >> first_assum ACCEPT_TAC
QED
Resume calldata_exact_nonbulk_array_owned_run[finish]:
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- (disj1_tac >> conj_tac
      >- (qpat_assum `cd_decode_elems _ _ _ _ _ _ = NONE` mp_tac >>
          qpat_assum `n <= maxn` mp_tac >>
          qpat_assum `tv_abi_dynamic tv \/ tv_needs_clamp tv` mp_tac >>
          qpat_assum `Abbrev (n = _)` mp_tac >>
          qpat_assum `Abbrev (cd = _)` mp_tac >>
          qpat_assum `Abbrev (srcbase = _)` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[markerTheory.Abbrev_def, calldata_decode_load_word] >>
          rpt strip_tac >> gvs[Once cd_decode_def]) >>
      `X initial` by (qpat_assum `!u v. Rel u v /\ X v ==> X u` drule_all >> simp[]) >>
      qpat_assum `X initial` mp_tac >> simp_tac bool_ss [Abbr `X`]) >>
  `Rel initial t` by
    (qpat_assum `!u v w. Rel u v /\ Rel v w ==> Rel u w` drule_all >> simp[]) >>
  qpat_x_assum `Q xs t` mp_tac >> simp_tac bool_ss [Abbr `Q`] >> strip_tac >>
  disj2_tac >> qexistsl [`t`,`ArrayV (DynArrayV xs)`,`scratch'`] >>
  conj_tac
  >- (qpat_assum `cd_decode_elems _ _ _ _ _ _ = SOME xs` mp_tac >>
      qpat_assum `n <= maxn` mp_tac >>
      qpat_assum `tv_abi_dynamic tv \/ tv_needs_clamp tv` mp_tac >>
      qpat_assum `Abbrev (n = _)` mp_tac >>
      qpat_assum `Abbrev (cd = _)` mp_tac >>
      qpat_assum `Abbrev (srcbase = _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[markerTheory.Abbrev_def, calldata_decode_load_word] >>
      rpt strip_tac >> gvs[Once cd_decode_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise calldata_exact_nonbulk_array_owned_run
