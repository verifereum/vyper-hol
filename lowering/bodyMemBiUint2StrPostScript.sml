(* Numeric uint2str postconditions on the counted memory execution. *)
Theory bodyMemBiUint2StrPost
Ancestors
  bodyMemBiUint2StrSuffix exprWordOperand exprSimWordArgs tupleMemoryFrame
  exprSimHypsDefs exprSimMemDefs loweringPosts exprSimUint2Str exprSimHash
  exprLoweringProps exprSimSource exprSafeOperand vyperTyping vyperTypeSystem vyperArith arithmetic context compileEnv valueEncoding loweringSlice vyperValue vyperAST

Theorem u2s_alloc_mem_ready_mem[local]:
  compile_alloc_buffer sz sa = (ba,a) /\ fn_has_code sa a fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx fn cenv cx es s /\ alloca_history fn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ sz < dimword (:256) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\
  wb_frame cenv es es sp spre s /\ local_ptrs_reserved cenv sp /\
  sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id ==>
  ?b t inst. gas_path_mem ctx fn s 0 (OK t) /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    u2s_safe H ctx fn cenv cx es a ba.buf_operand b sz inst t t /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_id < a.cs_next_id /\
    eval_operand op t = SOME (n2w X) /\ local_ptrs_reserved cenv a /\
    (?p. ba.buf_operand = Var p /\ not_fresh_at a p) /\
    b+sz < dimword (:256) /\ t.vs_current_bb = a.cs_current_bb /\
    t.vs_inst_idx = LENGTH a.cs_current_insts /\ ~t.vs_halted /\
    wb_frame cenv es es sp spre t /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       b+sz <= lb \/ lb+lsz <= b) /\
    (!aid off len. aid < sp.cs_next_id /\
       FLOOKUP spre.vs_allocas aid = SOME (off,len) ==>
       off+len <= b \/ b+sz <= off) /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  drule_all bodyMemAggregateAllocTheory.aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `u2s_safe H ctx fn cenv cx es a ba.buf_operand b sz ai t t` by
    (irule u2s_safe_initial >>
     gvs[Abbr `ai`, venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[ADD_COMM]) >>
  `eval_operand op t = SOME (n2w X)` by
    (Cases_on `op` >> gvs[venomStateTheory.eval_operand_def]) >>
  `wb_frame cenv es es sp spre t` by
    (irule wb_frame_allocating_tail >>
     simp[] >> qexistsl_tac [`s`, `es.scopes`, `sa`] >> simp[]) >>
  `!aid off len. aid < sp.cs_next_id /\
     FLOOKUP spre.vs_allocas aid = SOME (off,len) ==>
     off+len <= b \/ b+sz <= off` by
    (fs[wb_frame_def] >> rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     `aid < sa.cs_next_id` by decide_tac >>
     qpat_assum `!aid p n. _ ==> regions_disjoint b sz p n` drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, ADD_COMM]) >>
  qexistsl_tac [`b`, `t`, `ai`] >>
  gvs[Abbr `ai`, venomInstTheory.mk_inst_def, fragGasModeTheory.gas_marked_path_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!name p n. _ ==> regions_disjoint b sz p n` drule >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def, ADD_COMM]) >> first_assum ACCEPT_TAC
QED

Theorem u2s_allocated_mem_exit_mem[local]:
  compile_alloc_buffer (sz+n) sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx fn cenv cx es s /\ alloca_history fn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ sz+n < dimword (:256) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\ X < dimword (:256) /\
  78 <= n /\ 32 <= sz /\
  wb_frame cenv es es sp spre s /\ local_ptrs_reserved cenv sp /\
  sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id ==>
  ?b ready inst t. gas_path_mem ctx fn s 0 (OK t) /\
    alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    u2s_safe H ctx fn cenv cx es a ba.buf_operand b (sz+n) inst ready t /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory ty (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    b+n-LENGTH (num_to_dec_string X)+sz <= t.vs_alloca_next /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    wb_frame cenv es es sp spre t /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_id < a.cs_next_id /\
    b+sz+n < dimword (:256) /\
    ready.vs_memory = s.vs_memory /\ wb_frame cenv es es sp spre ready /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    (!name lb lsz. local_region cenv es.scopes ready name lb lsz ==>
       b+(sz+n) <= lb \/ lb+lsz <= b)
Proof
  strip_tac >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  drule_all u2s_alloc_mem_ready_mem >> strip_tac >>
  rename1 `gas_path_mem ctx fn s 0 (OK ready)` >>
  `alloca_inv ready` by
    (irule bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  `eval_operand ba.buf_operand ready = SOME (n2w b)` by fs[u2s_safe_def] >>
  `lookup_block ready.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>` by simp[] >>
  mp_tac (Q.INST [`s` |-> `ready`, `s0` |-> `ready`, `buf` |-> `ba.buf_operand`,
    `pre` |-> `a.cs_current_insts`,
    `bb` |-> `<|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>`]
      bodyMemBiUint2StrLoopTheory.u2s_setup_mem_exit) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_var <= a.cs_next_var` by
    (mp_tac (Q.SPECL [`sz+n`, `sa`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `wb_frame cenv es es sp spre t` by
    (irule u2s_frame_wb_tail >>
     simp[] >> qexistsl_tac [`a`, `b`, `ready`, `sz+n`] >>
     fs[u2s_safe_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`b`, `ready`, `inst`, `t`] >> gvs[] >>
  drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem uint2str_numeric_mem_path:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  compile_uint2str x n sz sm = (out,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel H ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_post H ctx func cenv cx e es sa sm s0 es' (IntV (&X)) x s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz+n < dimword (:256) /\
  alloca_history func s ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    vv_post H ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      es sa sb s0 es' (Value (StringV (num_to_dec_string X)))
      (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ?p. eval_operand out t = SOME (n2w p) /\ p < dimword (:256) /\
      p+sz <= t.vs_alloca_next
Proof
  strip_tac >> drule_all compile_uint2str_layout >> strip_tac >>
  `storage_well_formed_on cx es' (FST H)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all expr_post_frame >> strip_tac >>
  drule_all expr_post_state >> strip_tac >>
  `wb_frame cenv es' es' sm s s` by simp[wb_frame_refl] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `well_formed_type env.type_defs (expr_type e)` by
    (irule well_typed_expr_type_well_formed >>
     metis_tac[expr_body_pre_var_types_well_formed, expr_body_pre_def]) >>
  `eval_operand x s = SOME (n2w X)` by
    (drule expr_post_word_operand >>
     gvs[well_formed_type_def, is_word_type_def, word_value_def,
        val_to_w256_def, evaluate_type_def, integer_wordTheory.i2w_def]) >>
  `32 <= sz` by decide_tac >>
  drule_all (SRULE [] (Q.INST
    [`sa` |-> `sm`, `sp` |-> `sm`, `spre` |-> `s`] u2s_allocated_mem_exit_mem)) >>
  disch_then (qspec_then `BaseTV (StringT n)` mp_tac) >>
  strip_tac >>
  `wb_frame cenv es es' sa s0 t` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`es'`, `sm`, `s`] >> simp[]) >>
  mp_tac (Q.INST [`X` |-> `X`, `n` |-> `n`] uint2str_result_memory_bounds) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH (num_to_dec_string X) <= n` by
    (mp_tac (Q.INST [`x` |-> `X`] uint256_decimal_length) >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  `b <= b+n-LENGTH (num_to_dec_string X) /\
   b+n-LENGTH (num_to_dec_string X) < dimword (:256)` by decide_tac >>
  `sb.cs_current_bb = u2s_label a 5 /\ sb.cs_current_insts = [] /\
   sb.cs_next_id = a.cs_next_id+30` by fs[u2s_layout_def, u2s_end_def] >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 t` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 s` by metis_tac[expr_post_pure_frame] >>
     `pure_frame cenv func es' sm s t` by
       (mp_tac (Q.INST [`fn` |-> `func`, `es` |-> `es'`, `sa` |-> `sm`,
          `buf` |-> `ba.buf_operand`, `sz` |-> `sz+n`, `s0` |-> `ready`,
          `out` |-> `t`] u2s_safe_pure_tail) >>
        impl_tac >- (fs[] >> rpt strip_tac >> res_tac >> decide_tac) >> simp[]) >>
     `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b` by
       (qpat_assum `wb_frame cenv es' es' sm s t`
          (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
        first_assum ACCEPT_TAC) >>
     `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
            lookup_var x s = SOME w` by
       (qpat_assum `wb_frame cenv es es' sa s0 s`
          (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
        first_assum ACCEPT_TAC) >>
     match_mp_tac exprSimPropsTheory.pure_frame_trans >>
     qexistsl_tac [`es'`, `sm`, `s`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac >-
    (qexists_tac `b+n-LENGTH (num_to_dec_string X)` >> simp[]) >>
  irule (SRULE [expr_type_def] (Q.INST
    [`e` |-> `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`]
    vv_post_allocated_memory_intro)) >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def, mk_ptr_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (fs[u2s_safe_def] >> NO_TAC) >>
  qexistsl_tac [`inst.inst_id`, `b`, `sz+n`] >>
  fs[u2s_safe_def, type_slot_size_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `0 < n` by decide_tac >> drule word_size_le >> decide_tac
QED

Theorem uint2str_vv_capacity:
  vv_post H ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
    es sa sb s0 es' tv (LocatedValue (BaseT (StringT n)) p) t /\
  eval_operand p.ptr_operand t = SOME (n2w addr) /\ addr < dimword (:256) /\
  n < dimword (:256) /\
  addr + type_memory_bytes cenv (BaseT (StringT n)) <= t.vs_alloca_next ==>
  vv_store_bound cx (BaseT (StringT n)) (BaseT (StringT n)) es' tv
    (LocatedValue (BaseT (StringT n)) p) t
Proof
  strip_tac >>
  drule vv_store_bound_capacity >> simp[expr_type_def] >> disch_then irule >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[type_memory_size_def] >>
  fs[type_memory_bytes_def, vfmConstantsTheory.word_size_def, type_slot_size_def] >>
  Cases_on `n = 0` >- simp[wordsTheory.dimword_def] >>
  mp_tac (Q.INST [`n` |-> `n`] word_size_le) >>
  fs[vfmConstantsTheory.word_size_def] >> decide_tac
QED
