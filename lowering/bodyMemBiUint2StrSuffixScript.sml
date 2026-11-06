(* Allocation followed by the same-run uint2str memory path. *)
Theory bodyMemBiUint2StrSuffix
Ancestors
  bodyMemBiUint2StrLoop bodyMemAggregateAlloc exprSimUint2Str bodyMemBopRestWordPath
  exprSimAlloc exprSimHash loweringPosts compileEnv fragGasPathMem fragGasMode finite_map
  venomInst venomState venomExecSemantics arithmetic

Theorem u2s_alloc_mem_ready:
  compile_alloc_buffer sz sa = (ba,a) /\ fn_has_code sa a fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx fn cenv cx es s /\ alloca_history fn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ sz < dimword (:256) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\
  wb_frame cenv es sp spre s /\ local_ptrs_reserved cenv sp /\
  sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id ==>
  ?b t inst. gas_path_mem ctx fn s 0 (OK t) /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    u2s_safe ctx fn cenv cx es a ba.buf_operand b sz inst t t /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_id < a.cs_next_id /\
    eval_operand op t = SOME (n2w X) /\ local_ptrs_reserved cenv a /\
    (?p. ba.buf_operand = Var p /\ not_fresh_at a p) /\
    b+sz < dimword (:256) /\ t.vs_current_bb = a.cs_current_bb /\
    t.vs_inst_idx = LENGTH a.cs_current_insts /\ ~t.vs_halted /\
    wb_frame cenv es sp spre t /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b) /\
    (!aid off len. aid < sp.cs_next_id /\
       FLOOKUP spre.vs_allocas aid = SOME (off,len) ==>
       off+len <= b \/ b+sz <= off)
Proof
  strip_tac >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `u2s_safe ctx fn cenv cx es a ba.buf_operand b sz ai t t` by
    (irule u2s_safe_initial >>
     gvs[Abbr `ai`, mk_inst_def, eval_operand_def, regions_disjoint_def] >>
     metis_tac[ADD_COMM]) >>
  `eval_operand op t = SOME (n2w X)` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `wb_frame cenv es sp spre t` by
    (irule wb_frame_allocating_tail >>
     simp[] >> qexistsl_tac [`s`, `es.scopes`, `sa`] >> simp[]) >>
  `!aid off len. aid < sp.cs_next_id /\
     FLOOKUP spre.vs_allocas aid = SOME (off,len) ==>
     off+len <= b \/ b+sz <= off` by
    (fs[wb_frame_def] >> rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     `aid < sa.cs_next_id` by decide_tac >>
     qpat_assum `!aid p n. _ ==> regions_disjoint b sz p n` drule_all >>
     simp[regions_disjoint_def, ADD_COMM]) >>
  qexistsl_tac [`b`, `t`, `ai`] >>
  gvs[Abbr `ai`, mk_inst_def, gas_marked_path_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!name p n. _ ==> regions_disjoint b sz p n` drule >>
    simp[regions_disjoint_def, ADD_COMM]) >> first_assum ACCEPT_TAC
QED

Theorem u2s_allocated_mem_exit:
  compile_alloc_buffer (sz+n) sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx fn cenv cx es s /\ alloca_history fn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ sz+n < dimword (:256) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\ X < dimword (:256) /\
  78 <= n /\ 32 <= sz /\
  wb_frame cenv es sp spre s /\ local_ptrs_reserved cenv sp /\
  sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id ==>
  ?b ready inst t. gas_path_mem ctx fn s 0 (OK t) /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    u2s_safe ctx fn cenv cx es a ba.buf_operand b (sz+n) inst ready t /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory ty (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    b+n-LENGTH (num_to_dec_string X)+sz <= t.vs_alloca_next /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    wb_frame cenv es sp spre t /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_id < a.cs_next_id /\
    b+sz+n < dimword (:256)
Proof
  strip_tac >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  drule_all u2s_alloc_mem_ready >> strip_tac >>
  rename1 `gas_path_mem ctx fn s 0 (OK ready)` >>
  `alloca_inv ready` by
    (irule rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  `eval_operand ba.buf_operand ready = SOME (n2w b)` by fs[u2s_safe_def] >>
  `lookup_block ready.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>` by simp[] >>
  mp_tac (Q.INST [`s` |-> `ready`, `s0` |-> `ready`, `buf` |-> `ba.buf_operand`,
    `pre` |-> `a.cs_current_insts`,
    `bb` |-> `<|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>`]
      u2s_setup_mem_exit) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_var <= a.cs_next_var` by
    (mp_tac (Q.SPECL [`sz+n`, `sa`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `wb_frame cenv es sp spre t` by
    (irule u2s_frame_wb_tail >>
     simp[] >> qexistsl_tac [`a`, `b`, `ready`, `sz+n`] >>
     fs[u2s_safe_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`b`, `ready`, `inst`, `t`] >> gvs[] >>
  drule_all gas_path_mem_then >> simp[]
QED
