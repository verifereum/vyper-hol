(* The setup allocation starts at the successful length-guard cursor. *)
Theory bodyAbiDecodeLinkedSetupAllocationMods
Ancestors
  bodyPtrBytestringBuiltinsBuffer[qualified] bodyFullAllocGeneric
  bodyPtrIfExpAllocSource bodyPtrIfExpAllocSeparation bodyPtrIfExpAllocKept
  bodyFullHashKeccakFixed stateRelProj allocaHistory allocaBudgetProps
  bufferAllocationExecution loweringHalt exprLoweringProps exprSimOperands
  fragGasOriginPtr fragGasSeq fragGasPath fragExec fragExecPtr
  bodyFullAbiEncodeOriginFloor decoderGhostFramePtr
  abiDecodePtrMemberFrame abiDecoderReentry exprSimPtrLiteralBuffer
  bodyPtrDefs ptrDiscipline loweringStateRelDefs compileEnv
  venomInst venomState venomExecSemantics blockPrefixEquiv ghostPcTransportPtr
  finite_map pred_set list words arithmetic

Theorem decode_output_alloc_fetch[local]:
  compile_alloc_buffer n st = (buf,ready) /\ buf.buf_operand = Var out /\
  fn_has_code st ready obs /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME
      (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out])
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `out = STRING #"%" (toString st.cs_next_var)` by metis_tac[operand_11] >>
  qexists_tac `bb` >> simp[NoAsms, SimpLHS] >>
  qpat_assum `!i. i < _ ==> get_instruction _ _ = _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [])) >> simp[]
QED

Theorem decode_output_alloc_observe[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path ctx obs s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_edge ctx obs s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SRULE [instruction_accessors, is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ALLOCA [Lit (n2w n)] [out]`] tuple_straight_line_edge)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`,`id`,`n`,`out`] >> simp[]) >>
  drule gas_path_edge_normal >> strip_tac >>
  metis_tac[gas_path_rules, ADD_CLAUSES]
QED

Theorem decode_output_alloc_operand_age[local]:
  abi_decoder_operand_live st.cs_next_var op ==>
  !p. op = Var p ==> not_fresh_at st p
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def]
QED

Theorem abi_decode_linked_setup_allocation_mods:
  compile_alloc_buffer outsz header_st = (buf,ready) /\
  fn_has_code header_st ready fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce header_st /\ outsz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = header_st.cs_current_bb /\
  s.vs_inst_idx = LENGTH header_st.cs_current_insts /\
  alloca_history fn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (?H. V H) /\ (!H. V H ==> stmt_state_rel H ctx fn ce cx es s) /\
  abi_decoder_operand_live header_st.cs_next_var len /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  abi_decoder_operand_live header_st.cs_next_var (Var input) /\
  abi_decode_ptr_window G tn s input w (LENGTH bs) /\
  w2n w + LENGTH bs <= s.vs_alloca_next /\
  mem_bytes_at (w2n w) (LENGTH bs) s.vs_memory = bs /\
  ((FLOOKUP s.vs_allocas header_st.cs_next_id = NONE /\ dst = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (dst,outsz)) ==>
  ?t Gs ts output.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gs,ts)) /\
    (!obs. fn_has_code header_st ready obs ==> gas_path ctx obs s 0 (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\ alloca_history fn t /\
    allocas_from lo t /\ lo <= dst /\ s.vs_alloca_next <= t.vs_alloca_next /\
    buf.buf_operand = Var output /\ lookup_var output t = SOME (n2w dst) /\
    ptr_covers Gs ts output t outsz /\ op_taint ts (Var output) = {} /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (dst,outsz) /\
    FLOOKUP Gs output = SOME (dst,outsz) /\ dst + outsz < dimword (:256) /\
    (?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
         i.inst_outputs = [output] /\ i.inst_id = header_st.cs_next_id) /\
    header_st.cs_next_id < ready.cs_next_id /\
    ~not_fresh_at header_st output /\ not_fresh_at ready output /\
    not_local_ptr ce es.scopes output /\
    (!name b n. local_region ce es.scopes t name b n ==> regions_disjoint dst outsz b n) /\
    abi_decoder_operand_live ready.cs_next_var (Var output) /\
    abi_decoder_operand_live ready.cs_next_var (Var input) /\
    abi_decoder_operand_live ready.cs_next_var len /\
    abi_decode_ptr_window Gs ts t input w (LENGTH bs) /\ op_taint ts (Var input) = {} /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    op_prov Gs len = NONE /\ op_taint ts len = {} /\
    mem_bytes_at (w2n w) (LENGTH bs) t.vs_memory = bs /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es t) /\
    t.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!name b n. local_region ce es.scopes t name b n <=> local_region ce es.scopes s name b n) /\
    (!x. not_fresh_at header_st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gs x = FLOOKUP G x /\ op_taint ts (Var x) = op_taint tn (Var x)) /\
    ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\ ts.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next ==> (i IN ts.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
  `stmt_state_rel h ctx fn ce cx es s` by
    (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all bodyPtrBytestringBuiltinsBufferTheory.compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `ARB`]
    (qx_choosel_then [`out`,`raw`,`Gs`,`ts`] strip_assume_tac)) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es raw` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s` (drule_then assume_tac) >>
     drule_all compile_alloc_buffer_raw_resources >> simp[]) >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all decode_output_alloc_fetch >> strip_tac >>
  qabbrev_tac `t = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  `~t.vs_halted` by simp[Abbr `t`] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gs,ts)` by
    (gen_tac >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gs,ts)` by
       (qpat_assum `Gs = _` SUBST1_TAC >> qpat_assum `ts = _` SUBST1_TAC >>
        simp[NoAsms, Abbr `t`] >> irule ifexp_alloca_origin_ptr_edge >>
        `out = STRING #"%" (toString header_st.cs_next_var)` by metis_tac[operand_11] >>
        rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
        qexists_tac `bb` >> simp[]) >>
     pop_assum mp_tac >> qpat_assum `~t.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  qexistsl_tac [`t`,`Gs`,`ts`,`out`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "observe" >>
  suspend "resources"
QED

Resume abi_decode_linked_setup_allocation_mods[observe]:
  qx_gen_tac `obs` >> strip_tac >>
  qpat_x_assum `fn_has_code header_st ready fn` kall_tac >>
  drule_all decode_output_alloc_fetch >> strip_tac >>
  simp[NoAsms, Abbr `t`] >> irule decode_output_alloc_observe >>
  `out = STRING #"%" (toString header_st.cs_next_var)` by metis_tac[operand_11] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bb'`,`header_st.cs_next_id`,`outsz`,`out`] >> simp[]
QED

Resume abi_decode_linked_setup_allocation_mods[resources]:
  `buffer_allocation_base s header_st.cs_next_id = dst` by
    (qpat_assum `(_ = NONE /\ dst = _) \/ _` strip_assume_tac >>
     simp[buffer_allocation_base_def]) >>
  drule_all ifexp_alloca_step_site >> strip_tac >>
  `a = dst` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `a = dst` SUBST_ALL_TAC >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
     drule_all abi_encode_origin_path_allocas_from >> simp[]) >>
  `lo <= dst` by
    (qpat_x_assum `allocas_from lo t` mp_tac >> simp[allocas_from_def, Abbr `t`] >>
     disch_then (qspec_then `header_st.cs_next_id` mp_tac) >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (`(mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out]).inst_opcode = ALLOCA` by
       simp[mk_inst_def] >>
     drule_all step_inst_base_alloca_effect >>
     simp[NoAsms, Abbr `t`, LET_THM] >> IF_CASES_TAC >> simp[]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `out = STRING #"%" (toString header_st.cs_next_var)` by metis_tac[operand_11] >>
  `alloca_history fn t` by
    (qpat_assum `out = _` SUBST_ALL_TAC >>
     drule_all alloca_history_base_step >> simp[mk_inst_def, is_terminator_def, Abbr `t`]) >>
  `~not_fresh_at header_st out /\ not_fresh_at ready out` by simp[] >>
  `not_local_ptr ce es.scopes out` by metis_tac[fresh_not_local_ptr] >>
  `t.vs_inst_idx = LENGTH ready.cs_current_insts /\ t.vs_current_bb = ready.cs_current_bb` by
    (drule compile_alloc_buffer_insts >> simp[Abbr `t`, ADD1]) >>
  `?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
       i.inst_outputs = [out] /\ i.inst_id = header_st.cs_next_id` by
    (qexists_tac `mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out]` >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[mk_inst_def]) >>
  `FLOOKUP Gs out = SOME (dst,outsz)` by
    (drule step_prov_alloca >> disch_then (qspecl_then [`PG`,`G`,`Lit (n2w outsz)`,`out`] mp_tac) >>
     simp[FLOOKUP_UPDATE]) >>
  `!x. not_fresh_at header_st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gs x = FLOOKUP G x /\ op_taint ts (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `x <> out` by metis_tac[] >>
     conj_tac >- simp[Abbr `t`, lookup_var_set_inst_idx] >>
     qpat_assum `Gs = _` SUBST1_TAC >> qpat_assum `ts = _` SUBST1_TAC >>
     `x NOTIN set (mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out]).inst_outputs` by
       (simp[NoAsms, instruction_accessors] >> first_assum ACCEPT_TAC) >>
     conj_tac
     >- (irule step_prov_other_output >> first_assum ACCEPT_TAC) >>
     irule step_taint_other_output >> first_assum ACCEPT_TAC) >>
  `ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\ ts.t_imm = tn.t_imm` by
    (qpat_assum `ts = _` SUBST1_TAC >> irule step_taint_nonmemory_frame >> simp[mk_inst_def]) >>
  `!i. i < s.vs_alloca_next ==> (i IN ts.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >> qpat_assum `ts = _` SUBST1_TAC >>
     irule alloca_step_taint_below_frontier >> simp[]) >>
  `not_fresh_at header_st input` by
    (drule decode_output_alloc_operand_age >> simp[]) >>
  `abi_decode_ptr_window Gs ts t input w (LENGTH bs)` by
    (qpat_assum `!x. not_fresh_at header_st x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
     qx_gen_tac `j` >> strip_tac >> `j < s.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. i < s.vs_alloca_next ==> _` (drule_then ACCEPT_TAC)) >>
  `(!p. len = Var p ==> p <> out)` by
    (qpat_assum `abi_decoder_operand_live header_st.cs_next_var len`
       (mp_then Any mp_tac decode_output_alloc_operand_age) >> metis_tac[]) >>
  `eval_operand len t = eval_operand len s /\ op_prov Gs len = op_prov G len /\
    op_taint ts len = op_taint tn len` by
    (simp[NoAsms, Abbr `t`, eval_operand_inst_idx] >>
     conj_tac >-
       (irule allocationPtrTheory.alloca_step_operand_preserved >>
        qexistsl_tac [`header_st.cs_next_id`,`outsz`,`out`] >>
        metis_tac[]) >>
     qpat_assum `Gs = _` SUBST1_TAC >> qpat_assum `ts = _` SUBST1_TAC >>
     conj_tac >- (irule alloca_step_operand_prov >> first_assum ACCEPT_TAC) >>
     irule alloca_step_operand_taint >> first_assum ACCEPT_TAC) >>
  `!name b n. local_region ce es.scopes t name b n <=> local_region ce es.scopes s name b n` by
    (irule literal_ptr_local_region_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `op_taint ts (Var out) = {} /\ op_taint ts (Var input) = {}` by
    (qpat_assum `ptr_covers Gs ts out t outsz` mp_tac >>
     qpat_assum `abi_decode_ptr_window Gs ts t input w _` mp_tac >>
     simp[NoAsms, abi_decode_ptr_window_def, ptr_covers_def] >> metis_tac[]) >>
  `header_st.cs_next_var <= ready.cs_next_var` by simp[] >>
  `abi_decoder_operand_live ready.cs_next_var len /\
   abi_decoder_operand_live ready.cs_next_var (Var input)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_decoder_operand_live ready.cs_next_var (Var out)` by
    (qpat_assum `not_fresh_at ready out` mp_tac >>
     simp[NoAsms, abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!name b n. local_region ce es.scopes t name b n ==> regions_disjoint dst outsz b n` by
    (qpat_assum `!name b n. local_region ce es.scopes raw name b n ==> _` mp_tac >>
     simp[NoAsms, Abbr `t`, local_region_def, lookup_var_set_inst_idx]) >>
  map_every (fn p => qpat_x_assum p kall_tac) [`Gs = _`, `ts = _`, `out = _`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
  simp[Abbr `t`, lookup_var_set_inst_idx, stmt_state_rel_inst_idx] >>
  qexists_tac `i` >> simp[]
QED
Finalise abi_decode_linked_setup_allocation_mods
