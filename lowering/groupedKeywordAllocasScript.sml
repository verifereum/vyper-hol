(* The keyword pointers allocated before a group's selector checks. *)
Theory groupedKeywordAllocas
Ancestors
  moduleLowering context bodyFullAllocaFresh bodyFullHashKeccakFixed
  bodyPtrMakeArrayAllocBuffer exprLoweringProps exprSimHash loweringHalt
  fragExec fragGasOriginPtr fragGasOriginPtrLoop fragGasSeqPtr ptrDiscipline bodyPtrDefs
  abiBuiltinAllocation bufferAllocationExecution exprPtrUnwrapAllocation
  emitHelperProps emitHelper sourceValueFrames venomExecSemantics
  stmtFragPtr loweringStateRelDefs compileEnv venomState venomInst finite_map list pair words arithmetic

Theorem compile_create_kwarg_allocas_mono:
  !specs ce sa. ci_mono sa (SND (compile_create_kwarg_allocas ce specs sa))
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, ci_mono_comp_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_create_kwarg_allocas_def] >>
  irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
  gen_tac >> irule ci_mono_bind >> simp[ci_mono_comp_return]
QED

Theorem compile_create_kwarg_allocas_origin:
  !specs ce sa sb kwvars s G tn.
    compile_create_kwarg_allocas ce specs sa = (kwvars,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    EVERY (\(_,ty,_). type_memory_bytes ce ty < dimword (:256)) specs /\
    stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
      ctx func ce cx es s /\ alloca_history func s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t G' tn'.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx func PG G' tn' t) ==>
        !fuel. ptr_safe_run D lo fuel ctx func PG G tn s) /\
      fresh_vars_wrt sb t /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
      (!H' : (bool # bytes32 # type_value) list # num list.
        stmt_state_rel H' ctx func ce cx es s ==>
        stmt_state_rel H' ctx func ce cx es t) /\
      alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p)) /\
      (!name op ty e. MEM (name,op,ty,e) kwvars ==>
        ?p w i. op = Var p /\ not_fresh_at sb p /\ lookup_var p t = SOME w /\
          FLOOKUP G' p = SOME (w2n w,type_memory_bytes ce ty) /\
          op_taint tn' op = {} /\ MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
          i.inst_outputs = [p] /\
          FLOOKUP t.vs_allocas i.inst_id = SOME (w2n w,type_memory_bytes ce ty))
Proof
  Induct >- (simp[compile_create_kwarg_allocas_def, comp_return_def] >>
    rpt strip_tac >> qexistsl [`s`,`G`,`tn`] >>
    simp[gas_origin_ptr_path_rules, venom_state_component_equality]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) sa` >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce h1) sa = (buf,mid)` >>
  Cases_on `compile_create_kwarg_allocas ce specs mid` >>
  rename1 `compile_create_kwarg_allocas ce specs mid = (rest,end)` >>
  strip_tac >> gvs[] >>
  `ci_mono sa mid /\ ci_mono mid end` by
    metis_tac[ci_mono_compile_alloc_buffer, compile_create_kwarg_allocas_mono, SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid end func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var p` >>
  rename1 `lookup_var p a = SOME w` >>
  rename1 `ptr_covers A u p a _` >>
  rename1 `a = raw with vs_inst_idx := _` >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `nb = type_memory_bytes ce h1` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [p]` >>
  `emitted_insts sa mid = [ins]` by gvs[Abbr `ins`] >>
  `step_inst_base ins s = OK raw` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `raw.vs_requests = s.vs_requests` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
          vs_alloca_next := _; vs_inst_idx := _|> = s` (mp_tac o AP_TERM ``venom_state_vs_requests``) >>
     simp[]) >>
  `fresh_vars_wrt mid a` by
    (`raw = update_var p (n2w (buffer_allocation_base s sa.cs_next_id))
        (buffer_allocation_fields s sa.cs_next_id nb)` by
       (drule_all unwrap_alloc_generated_step >> strip_tac >> gvs[Abbr `ins`]) >>
     simp[] >> irule fresh_vars_wrt_advance >>
     qexistsl_tac [`sa.cs_next_var`,`sa`] >>
     fs[fresh_vars_wrt_def]) >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx func PG A u a) ==>
       !fuel. ptr_safe_run D lo fuel ctx func PG G tn s` by
    (`mid.cs_current_bb = sa.cs_current_bb /\
         mid.cs_current_insts = sa.cs_current_insts ++ [ins]` by
        (conj_tac
         >- (qpat_assum `same_blocks sa mid`
               (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [same_blocks_def])) >>
         qpat_assum `emitted_insts sa mid = [ins]` (fn code =>
           qpat_assum `mid.cs_current_insts = _`
             (ACCEPT_TAC o PURE_REWRITE_RULE [code]))) >>
     `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         bb.bb_instructions = sa.cs_current_insts ++ ins::rest` by
       (qpat_assum `fn_has_code sa mid func`
          (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
        asm_simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC, APPEND] >>
        strip_tac >> qexistsl_tac [`bb`,`l`] >> simp[]) >>
     rpt strip_tac >>
     `ptr_inst_ok D lo 0 ctx func G tn ins s` by
       (simp_tac bool_ss [Abbr `ins`] >> irule unwrap_alloc_ptr_check >>
        conj_tac
        >- (qexists_tac `raw` >> conj_tac
            >- first_assum ACCEPT_TAC >>
            first_assum ACCEPT_TAC) >>
        simp[]) >>
     mp_tac (Q.INST [`D` |-> `D`, `lo` |-> `lo`, `PG` |-> `PG`]
       (Q.SPECL [`[ins]`,`s`,`raw`,`G`,`tn`,`A`,`u`,`ctx`,`func`,`bb`,`fuel`]
          run_inst_seq_ptr_continuation)) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- asm_simp_tac bool_ss [rich_listTheory.DROP_LENGTH_APPEND,
           rich_listTheory.IS_PREFIX] >>
         conj_tac >- simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
         conj_tac
         >- (simp_tac bool_ss [inst_seq_ptr_def] >>
             asm_simp_tac (srw_ss()) [Excl "step_inst_base_def"]) >>
         conj_tac >- simp[run_inst_seq_def] >>
         qpat_assum `!fuel. ptr_safe_run D lo fuel ctx func PG A u a`
           (qspec_then `fuel` mp_tac) >>
         qpat_assum `a = raw with vs_inst_idx := _` (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `mid.cs_current_insts = _ ++ [ins]` (fn th => PURE_REWRITE_TAC [th]) >>
         asm_rewrite_tac [LENGTH, LENGTH_APPEND]) >>
     disch_then ACCEPT_TAC) >>
  `~a.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `a with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (fn th => PURE_ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  `local_ptrs_reserved ce mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def]) >>
  qpat_assum `!ce sa sb kwvars s G tn. _` (qspecl_then [`ce`,`mid`,`end`,`rest`,`a`,`A`,`u`] mp_tac) >>
  impl_tac >- (`lo <= a.vs_alloca_next` by decide_tac >>
    simp[] >>
    qpat_assum `!H'. stmt_state_rel H' ctx func ce cx es s ==>
      stmt_state_rel H' ctx func ce cx es a` (qspec_then `H` mp_tac) >>
    simp[]) >>
  disch_then (qx_choosel_then [`t`,`B`,`v`] strip_assume_tac) >>
  qexistsl [`t`,`B`,`v`] >> simp[] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  conj_tac >-
    (qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts`
       (fn th => PURE_REWRITE_TAC [SYM th]) >>
     qpat_assum `_ = a` mp_tac >> qpat_assum `_ = s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venom_state_component_equality] >>
     rpt strip_tac >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at mid p'` by
      (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >> fs[]) >>
  rpt strip_tac
  >- (gvs[] >>
      qexists_tac `ins` >>
      `MEM ins (fn_insts func)` by
        (irule hash_emitted_inst_mem >> qexistsl_tac [`sa`,`mid`] >> simp[]) >>
      qunabbrev_tac `ins` >>
      gvs[ci_mono_def, ptr_covers_def, mk_inst_def] >>
      metis_tac[not_fresh_at_mono]) >>
  qpat_assum `!name op ty e. MEM (name,op,ty,e) rest ==> _` drule >> simp[]
QED
