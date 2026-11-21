(* The keyword pointers allocated before a group's selector checks. *)
Theory groupedKeywordAllocas
Ancestors
  moduleLowering context bodyFullAllocaFresh bodyFullHashKeccakFixed
  bodyPtrMakeArrayAllocBuffer exprLoweringProps exprSimHash loweringHalt
  fragExec fragGasOriginPtr fragGasOriginPtrLoop ptrDiscipline bodyPtrDefs
  stmtFragPtr loweringStateRelDefs compileEnv venomState venomInst finite_map list pair words

Theorem compile_create_kwarg_allocas_mono:
  !specs ce sa. ci_mono sa (SND (compile_create_kwarg_allocas ce specs sa))
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def, ci_mono_refl] >>
  PairCases_on `h` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) sa` >>
  Cases_on `compile_create_kwarg_allocas ce specs r` >> gvs[] >>
  irule ci_mono_trans >> qexists_tac `r` >>
  conj_tac >- metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  first_x_assum (qspecl_then [`ce`,`r`] mp_tac) >> simp[]
QED

Theorem compile_create_kwarg_allocas_origin:
  !specs ce sa sb kwvars s G tn.
    compile_create_kwarg_allocas ce specs sa = (kwvars,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    EVERY (\(_,ty,_). type_memory_bytes ce ty < dimword (:256)) specs /\
    stmt_state_rel H ctx func ce cx es s /\ alloca_history func s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t G' tn'.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
      (!H'. stmt_state_rel H' ctx func ce cx es s ==>
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
    rpt strip_tac >> qexistsl [`s`,`G`,`tn`] >> simp[gas_origin_ptr_path_rules]) >>
  PairCases_on `h` >> rpt gen_tac >>
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
  drule_all alloc_buffer_origin_ptr_path_exact >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var p` >>
  rename1 `lookup_var p a = SOME w` >>
  rename1 `ptr_covers A u p a _` >>
  `~a.vs_halted` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s`
      (fn th => PURE_ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  `local_ptrs_reserved ce mid` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  qpat_assum `!ce sa sb kwvars s G tn. _` (qspecl_then [`ce`,`mid`,`end`,`rest`,`a`,`A`,`u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  disch_then (qx_choosel_then [`t`,`B`,`v`] strip_assume_tac) >>
  qexistsl [`t`,`B`,`v`] >> simp[] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  conj_tac >-
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = a` (SUBST1_TAC o SYM) >>
     simp[venom_state_component_equality] >>
     qpat_assum `a with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[LESS_EQ_TRANS] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  rpt strip_tac >> gvs[] >>
  qexistsl [`p`,`w`,`mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce h1))] [p]`] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce h1))] [p]) (fn_insts func)` by
    (drule alloc_buffer_emitted >> strip_tac >> gvs[] >>
     irule hash_emitted_inst_mem >> metis_tac[MEM]) >>
  gvs[ci_mono_def, ptr_covers_def, mk_inst_def] >>
  metis_tac[not_fresh_at_mono]
QED
