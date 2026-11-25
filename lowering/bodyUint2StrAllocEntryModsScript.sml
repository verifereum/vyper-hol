(* Allocate the Uint2Str buffer on the same run as the linked child landing. *)
Theory bodyUint2StrAllocEntryMods
Ancestors
  bodyMethodIdScratchFrameMods bodyFullAllocaFresh abiValidAllocatedArrayInit
  exprSimUint2Str stateRelProj abiBuiltinAllocation emitHelperProps
  exprLowering exprLoweringProps freshWrites ptrDiscipline bodyPtrDefs venomState venomInst
  finite_map words list compileEnv context loweringPosts loweringStateRelDefs
  vyperAST vyperValue fragGasOriginPtrLoop
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem uint2str_alloc_entry_mods:
  lower_value compile_expr ce ty e sa = (op,sm) /\
  N = type_memory_bytes ce (BaseT (StringT n)) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str op n N sm) = (vv,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sm /\
  (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  eval_operand op s = SOME (n2w X) /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  N+n < dimword(:256) /\ 32 <= N /\
  LENGTH (num_to_dec_string X) <= n /\ X < dimword(:256) /\
  valid_horizon cx st0 H0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx fn ce cx mid s /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s) /\
  alloca_history fn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?ba a p b ready Gr tr inst.
    compile_alloc_buffer (N+n) sm = (ba,a) /\ ba.buf_operand = Var p /\
    compile_uint2str op n N sm = (Var (u2s_var a 2),sb) /\
    u2s_layout a op (Var p) n sb /\ fn_has_code sm a fn /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK ready,Gr,tr)) /\
    valid_horizon cx st0 H0 mid.storage_trace /\
    not_fresh_at a p /\ local_ptrs_reserved ce a /\
    (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at a x) /\
    (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at a x) /\
    fn_inst_ids_distinct fn /\
    inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w (N+n))] [p] /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr ce mid.scopes p /\ n + 32 <= N+n /\
    LENGTH (num_to_dec_string X) <= n /\ X < dimword(:256) /\
    b+(N+n) < dimword(:256) /\ lo <= b /\
    eval_operand op ready = SOME (n2w X) /\ op_prov Gr op = NONE /\ op_taint tr op = {} /\
    (!k. op <> Var (u2s_var a k)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      u2s_safe H ctx fn ce cx mid a (Var p) b (N+n) inst ready ready /\
      ghost_inv_at (DF H) 0 d ce cx mid Gr tr ready) /\
    ghost_kept_at lo ce mid a Gr tr ready Gr tr /\
    FLOOKUP Gr p = SOME (b,N+n) /\ lookup_var p ready = SOME (n2w b) /\
    op_taint tr (Var p) = {} /\ ~ready.vs_halted /\
    ready.vs_current_bb = a.cs_current_bb /\
    ready.vs_inst_idx = LENGTH a.cs_current_insts /\
    lookup_block ready.vs_current_bb fn.fn_blocks =
      SOME <|bb_label := a.cs_current_bb;
             bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|> /\
    lookup_block (u2s_label a 0) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
    lookup_block (u2s_label a 1) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
    lookup_block (u2s_label a 2) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
    lookup_block (u2s_label a 3) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
    lookup_block (u2s_label a 4) fn.fn_blocks =
      SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
    alloca_history fn ready /\ allocas_from lo ready /\
    s.vs_alloca_next <= ready.vs_alloca_next /\ b+(N+n) <= ready.vs_alloca_next /\
    FLOOKUP ready.vs_allocas inst.inst_id = SOME (b,N+n) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
               FLOOKUP ready.vs_allocas aid = SOME row) /\
    (!aid off len. FLOOKUP ready.vs_allocas aid = SOME (off,len) ==>
      FLOOKUP s.vs_allocas aid = SOME (off,len) \/ s.vs_alloca_next <= off) /\
    (!x. not_fresh_at sm x ==> lookup_var x ready = lookup_var x s /\
         FLOOKUP Gr x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)) /\
    ready with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                 vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    ready.vs_memory = s.vs_memory /\
    tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
    (!i. i IN tr.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+(N+n))) /\
    (!i. i < lo /\ i IN tr.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `N = _` kall_tac >>
  Cases_on `compile_uint2str op n N sm` >>
  fs[as_ptr_val_def] >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  drule_then (qx_choose_then `ba` (qx_choose_then `a` strip_assume_tac))
    compile_uint2str_layout >>
  drule_all_then strip_assume_tac u2s_alloc_layout_code >>
  `stmt_state_rel H0 ctx fn ce cx mid s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all (Q.INST [`sa` |-> `sm`, `es` |-> `mid`]
    (INST_TYPE [``:'b`` |-> ``:256``] (SPEC_ALL alloc_buffer_origin_ptr_path_with_raw_endpoint))) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `p` (qx_choose_then `w` (qx_choose_then `ready`
      (qx_choose_then `Gr` (qx_choose_then `tr` (qx_choose_then `raw` strip_assume_tac))))))) >>
  `!aid off len. FLOOKUP ready.vs_allocas aid = SOME (off,len) ==>
      FLOOKUP s.vs_allocas aid = SOME (off,len) \/ s.vs_alloca_next <= off` by
    (qpat_assum `ready = _` SUBST1_TAC >> simp[] >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC abi_valid_allocated_buffer_origin) >>
  qpat_x_assum `ready = _` kall_tac >>
  qpat_x_assum `Gr = _` kall_tac >>
  qpat_x_assum `tr = _` kall_tac >>
  drule_then strip_assume_tac abi_builtin_alloc_buffer_shape >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  `p = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `sm.cs_next_var <= a.cs_next_var` by simp[] >>
  `local_ptrs_reserved ce a` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sm x ==> not_fresh_at a x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `not_local_ptr ce mid.scopes p` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `!k. op <> Var (u2s_var a k)` by
    (rpt strip_tac >>
     `not_fresh_at sm (u2s_var a k)` by (qpat_assum `!x. op = Var x ==> _` irule >> simp[]) >>
     `not_fresh_at a (u2s_var a k)` by (qpat_assum `!x. not_fresh_at sm x ==> _` irule >> simp[]) >>
     drule u2s_var_fresh >> disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `~ready.vs_halted /\ ready.vs_memory = s.vs_memory /\ ready.vs_labels = s.vs_labels` by
    (qpat_assum `ready with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo ready` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  `op_taint tr (Var p) = {}` by fs[ptr_covers_def] >>
  `eval_operand op ready = SOME (n2w X) /\ op_prov Gr op = NONE /\ op_taint tr op = {}` by
    (Cases_on `op` >> fs[eval_operand_def, op_prov_def, op_taint_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` drule >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    u2s_safe H ctx fn ce cx mid a (Var p) (w2n w) (N+n)
      (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (N+n))] [p]) ready ready /\
    ghost_inv_at (DF H) 0 d ce cx mid Gr tr ready` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
     conj_tac
     >- (irule u2s_safe_initial >> simp[mk_inst_def, eval_operand_def] >>
         rpt strip_tac >>
         qpat_assum `!name b len. local_region _ _ ready _ _ _ ==> _` drule >>
         simp[regions_disjoint_def]) >>
     drule method_id_ghost_at_zero >> strip_tac >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     irule alloc_buffer_ghost_inv_at_locals >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl_tac [`G`, `w2n w+(N+n)`, `fn`, `s`, `sm`, `tn`] >>
     simp[allocas_from_def]) >>
  `!i. i < lo /\ i IN tr.t_mem ==> i IN tn.t_mem` by
    (simp[] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`ba`,`a`,`p`,`w2n w`,`ready`,`Gr`,`tr`] >>
  fs[mk_inst_def, ghost_kept_at_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> u2s_safe H _ _ _ _ _ _ _ _ _ _ ready ready /\ _`
        drule >> strip_tac >> gvs[]) >>
  reverse (rpt conj_tac)
  >- (qpat_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!bb. MEM bb (u2s_blocks _ _ _ _) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[u2s_blocks_def] >> strip_tac >>
  rpt conj_tac >> qmatch_goalsub_abbrev_tac `SOME blk` >>
  first_x_assum (qspec_then `blk` mp_tac) >> simp[Abbr `blk`]
QED
