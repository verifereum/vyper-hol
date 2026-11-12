Theory appendDynamicHeaderStorePtr
Ancestors appendDynamicMemoryStepPtr typedCopyPtr exprSimPtrTopLevelImmutableCopy abiDecodeStaticProps
  valueEncodingProps bodyPtrDefs loweringStateRelDefs
  ptrDiscipline venomInst venomState venomExecSemantics compileEnv
  context emitHelper codegenRel contextCodegenRel finite_map words

Theorem emit_dynamic_header_store_core:
  !G cx ctx PG R sa sb dst value tn s a w.
    emit_void MSTORE [Var dst; value] sa = ((),sb) /\
    ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    ?tnf sf.
      (sf.vs_inst_idx = SUC s.vs_inst_idx /\
       step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s =
         OK (sf with vs_inst_idx := s.vs_inst_idx) /\
       step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
         (sf with vs_inst_idx := s.vs_inst_idx) = G /\
       step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
         (sf with vs_inst_idx := s.vs_inst_idx) tn = tnf /\
       (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
         ptr_inst_ok D 0 fuel ctx fn G tn
           (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s) /\
       (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_inst_idx := s.vs_inst_idx|>) = s) /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = G /\ t = tnf /\ v = sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        mem_word_at (w2n a) m = w) /\
      (!i. i < w2n a \/ w2n a+32 <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
      sf.vs_transient = s.vs_transient /\
      (!p. lookup_var p sf = lookup_var p s /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst;value] []] /\
   cs_extends sa sb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
        comp_return_def, cs_extends_def] >>
  qabbrev_tac `tnf = tn with t_mem :=
    tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` >>
  qexistsl_tac [`tnf`, `mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (drule_all dynamic_mstore_clean_step_ptr >>
     disch_then (qspecl_then [`PG`, `sa.cs_next_id`] strip_assume_tac) >>
     gvs[Abbr `tnf`, mstore_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (irule mstore_frag_ptr >> simp[] >>
     drule_all dynamic_mstore_clean_step_ptr >>
     disch_then (qspecl_then [`PG`, `sa.cs_next_id`] strip_assume_tac) >>
     gvs[Abbr `tnf`] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `mem_bytes_at (w2n a) 32 (mstore (w2n a) w s).vs_memory =
       mem_bytes_at (w2n a) 32 m` by
       (irule mem_bytes_at_bytewise >>
        gvs[mem_agree_outside_def, Abbr `tnf`] >> metis_tac[]) >>
     metis_tac[mstore_mem_word_at_same, valueEncodingDefsTheory.mem_word_at_def, valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `(mstore (w2n a) w s).vs_call_ctx = s.vs_call_ctx /\
   (mstore (w2n a) w s).vs_accounts = s.vs_accounts /\
   (mstore (w2n a) w s).vs_transient = s.vs_transient /\
   (!p. lookup_var p (mstore (w2n a) w s) = lookup_var p s)` by
    simp[mstore_def, lookup_var_def] >>
  simp[Abbr `tnf`, op_taint_def] >>
  rpt strip_tac >> simp[abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside] >>
  simp[lookup_var_def, mstore_def]
QED

Theorem emit_dynamic_header_store_ptr:
  !G cx ctx PG R sa sb dst value tn s a w.
    emit_void MSTORE [Var dst; value] sa = ((),sb) /\
    ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    ?tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = G /\ t = tnf /\ v = sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        mem_word_at (w2n a) m = w) /\
      (!i. i < w2n a \/ w2n a+32 <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
      sf.vs_transient = s.vs_transient /\
      (!p. lookup_var p sf = lookup_var p s /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >> drule_all emit_dynamic_header_store_core >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`tnf`, `sf`] >> simp[] >> metis_tac[]
QED
