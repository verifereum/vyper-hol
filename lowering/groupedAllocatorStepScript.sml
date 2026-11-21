(* A dispatcher allocation before any source arguments have been bound. *)
Theory groupedAllocatorStep
Ancestors
  entryPtrSeamRegister decoderOriginAllocationFrame selectedAcceptedFold
  groupedKeywordAllocas moduleLowering loweringShapeDefs
  fragGasOriginPtrLoop fragGasOriginPtr fragExecPtr fragExec
  abiBuiltinAllocation emitHelperProps emitHelper exprLoweringProps context
  memSafeRun ptrDiscipline abiDecoderReentry exprSimAlloc decoderNavigationPtr
  ptrSafetyTransport unitTransformDefs venomWf venomInstIdsProps
  loweringStateRelDefs venomExecSemantics venomState venomInst compileEnv
  venomInstProofs abiEncoderPathProps
  actualAllocExec bodyPtrDefs blockPrefixEquiv
  finite_map list words arithmetic

Theorem grouped_dispatch_alloca_step:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn /\
  selected_registration_resources ctx fn site lo st s /\
  fn_inst_ids_distinct fn /\ n < dimword (:256) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t G' tn' q p.
    buf.buf_operand = Var q /\ not_fresh_at last q /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
    lookup_var q t = SOME (n2w p) /\ ptr_covers G' tn' q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\ p+n < dimword (:256) /\
    selected_registration_resources ctx fn site lo last t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id e. FLOOKUP s.vs_allocas id = SOME e ==> FLOOKUP t.vs_allocas id = SOME e) /\
    (!v. not_fresh_at st v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id] >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> simp[] >>
     qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       (qspecl_then [`st.cs_next_id`,`x`] (fn older =>
         qpat_assum `FLOOKUP s.vs_allocas st.cs_next_id = SOME x`
           (mp_tac o MATCH_MP older))) >>
     simp_tac (srw_ss()) []) >>
  mp_tac (Q.INST [`ctx` |-> `ctx`,`fn` |-> `fn`,`site` |-> `site`,
    `n` |-> `n`,`st` |-> `st`,`last` |-> `last`,`s` |-> `s`,
    `buf` |-> `buf`] (SPEC_ALL registration_alloc_buffer_ptr)) >>
  impl_tac >- asm_rewrite_tac[optionTheory.NOT_NONE_SOME] >>
  disch_then (qx_choosel_then [`raw`,`G'`,`tn'`,`q`,`p`] strip_assume_tac) >>
  rename1 `run_inst_seq _ s = OK raw` >>
  `emit_op ALLOCA [Lit (n2w n)] st = (Var q,last)` by
    (drule abi_builtin_alloc_buffer_shape >>
     qpat_assum `buf.buf_operand = Var q` (pure_rewrite_tac o single) >>
     simp_tac bool_ss []) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `ins = mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]` >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH last.cs_current_insts` >>
  `emitted_insts st last = [ins]` by gvs[Abbr `ins`] >>
  `last.cs_current_bb = st.cs_current_bb` by fs[same_blocks_def] >>
  `MEM ins (fn_insts fn)` by
    (drule_all (Q.SPECL [`n`,`st`,`last`,`buf`,`fn`] buffer_alloc_code) >>
     qpat_assum `Var q = Var _` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     simp[Abbr `ins`]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ins` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `ins`]) >>
  `step_inst_base ins s = OK raw` by gvs[run_inst_seq_def, AllCaseEqs()] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,G',tn')` by
    (rpt gen_tac >>
     `ptr_inst_ok D lo 0 ctx fn G tn ins s` by
       (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
        qexists_tac `0` >> simp[Abbr `ins`, ptr_inst_ok_alloca]) >>
     `LENGTH last.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     mp_tac (Q.INST [`i` |-> `ins`,`t` |-> `raw`]
       (SPEC_ALL straight_line_step_origin)) >>
     impl_tac
     >- (asm_simp_tac (srw_ss()) [Abbr `ins`, mk_inst_def, is_terminator_def,
           inst_mem_below_frontier_def, inst_dload_in_section_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def] >>
         metis_tac[]) >>
     simp[Abbr `t`]) >>
  `not_fresh_at last q` by
    fs[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  `p = s.vs_alloca_next` by
    (mp_tac (Q.INST [`inst` |-> `ins`, `out` |-> `q`]
       (SPEC_ALL actual_literal_alloca_fresh_run)) >>
     impl_tac >- simp[Abbr `ins`, mk_inst_def] >>
     disch_then (qx_choose_then `u` strip_assume_tac) >>
     `u = raw` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
     gvs[Abbr `ins`, mk_inst_def, FLOOKUP_UPDATE]) >>
  `raw.vs_code = s.vs_code` by
    (irule step_preserves_code >>
     qexistsl_tac [`ctx`,`0`,`ins`] >>
     simp[step_inst_non_invoke, Abbr `ins`, mk_inst_def, is_terminator_def]) >>
  `!v. not_fresh_at st v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v)` by
    (gen_tac >> strip_tac >>
     `v <> q` by (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     conj_tac
     >- (qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
           (qspec_then `Var v` mp_tac) >>
         qpat_assum `not_fresh_at st v`
           (assume_tac o REWRITE_RULE [not_fresh_at_def]) >>
         asm_simp_tac (srw_ss()) [Abbr `t`, eval_operand_def, lookup_var_set_inst_idx,
           abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
     qpat_assum `G' = step_prov PG G _ raw` (pure_rewrite_tac o single) >>
     qpat_assum `tn' = step_taint _ s raw tn` (pure_rewrite_tac o single) >>
     qunabbrev_tac `ins` >>
     simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `selected_registration_frame s tn t tn'` by
    (qpat_assum `tn' = step_taint _ s raw tn` (pure_rewrite_tac o single) >>
     qunabbrev_tac `ins` >>
     simp[Abbr `t`, selected_registration_frame_def, step_taint_def,
          set_var_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def]) >>
  `allocas_from lo t` by
    (rw[allocas_from_def, Abbr `t`] >>
     Cases_on `aid = st.cs_next_id` >> gvs[allocas_from_def] >> metis_tac[]) >>
  `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id` by
    (rw[Abbr `t`] >> Cases_on `id = st.cs_next_id` >> simp[] >>
     qpat_assum `!id. id <> st.cs_next_id ==> _`
       (qspec_then `id` (drule_then (full_simp_tac (srw_ss()) o single))) >>
     res_tac >> decide_tac) >>
  `!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `inst.inst_id = st.cs_next_id`
     >- (`inst = ins` by
           (mp_tac (Q.SPECL [`fn`,`inst`,`ins`] fn_inst_ids_distinct_inj) >>
            simp[Abbr `ins`, mk_inst_def]) >>
         gvs[Abbr `t`, Abbr `ins`, mk_inst_def, w2n_n2w, LESS_MOD]) >>
     qpat_assum `!id. id <> st.cs_next_id ==> _`
       (qspec_then `inst.inst_id` (drule_then (full_simp_tac (srw_ss()) o single))) >>
     gvs[Abbr `t`] >> metis_tac[]) >>
  `alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    simp[Abbr `t`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp` by
    (`gas_origin_ptr_path ((ARB:dead),lo,{},ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')` by
       metis_tac[] >>
     `t.vs_fmp = s.vs_fmp` by simp[Abbr `t`] >>
     mp_tac (Q.INST [`D` |-> `ARB:dead`,`explicit` |-> `{}`,`marks` |-> `[]`,
       `H` |-> `G'`,`u` |-> `tn'`] (SPEC_ALL decoder_origin_path_room)) >>
     asm_rewrite_tac[]) >>
  `selected_registration_resources ctx fn site lo last t` by
    (simp_tac bool_ss [selected_registration_resources_def] >>
     asm_rewrite_tac[] >> simp[Abbr `t`, fresh_vars_wrt_inst_idx] >>
     decide_tac) >>
  `lookup_var q t = SOME (n2w p)` by
    asm_simp_tac (srw_ss()) [Abbr `t`, lookup_var_set_inst_idx] >>
  `ptr_covers G' tn' q t n` by
    (qpat_assum `ptr_covers G' tn' q raw n` mp_tac >>
     simp_tac (srw_ss()) [Abbr `t`, ptr_covers_def, lookup_var_set_inst_idx]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by
    (gen_tac >> strip_tac >>
     qpat_assum `!D lower ctx' func. _`
       (qspecl_then [`D`,`lo`,`ctx`,`fn`] MATCH_MP_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)` by
    (qpat_assum `MEM ins (fn_insts fn)` mp_tac >> simp[Abbr `ins`]) >>
  qexistsl_tac [`t`,`G'`,`tn'`,`q`,`p`] >>
  asm_rewrite_tac[] >> simp[Abbr `t`]
QED

Theorem grouped_dispatch_allocas:
  !specs sa sb kwvars s G tn.
    compile_create_kwarg_allocas ce specs sa = (kwvars,sb) /\
    fn_has_code sa sb fn /\ selected_registration_resources ctx fn site lo sa s /\
    fn_inst_ids_distinct fn /\
    EVERY (\(_,ty,_). type_memory_bytes ce ty < dimword (:256)) specs /\
    unit_alloca_budget ctx < dimword (:256) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
    ?t G' tn'.
      selected_registration_resources ctx fn site lo sb t /\
      selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (!id e. FLOOKUP s.vs_allocas id = SOME e ==> FLOOKUP t.vs_allocas id = SOME e) /\
      (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
        FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v)) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
        t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
      (!name op ty e. MEM (name,op,ty,e) kwvars ==>
        ?id q base.
          op = Var q /\ not_fresh_at sb q /\ lookup_var q t = SOME (n2w base) /\
          MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [q]) (fn_insts fn) /\
          FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes ce ty) /\
          base + type_memory_bytes ce ty < dimword (:256) /\
          ptr_covers G' tn' q t (type_memory_bytes ce ty)) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Induct
  >- (simp[compile_create_kwarg_allocas_def, comp_return_def] >>
      rpt strip_tac >> qexistsl_tac [`s`,`G`,`tn`] >>
      `~s.vs_halted` by fs[selected_registration_resources_def] >>
      asm_rewrite_tac[] >> simp[selected_registration_frame_def, gas_origin_ptr_path_rules]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) sa` >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce h1) sa = (buf,mid)` >>
  Cases_on `compile_create_kwarg_allocas ce specs mid` >>
  rename1 `compile_create_kwarg_allocas ce specs mid = (rest,last)` >>
  strip_tac >> gvs[] >>
  `ci_mono sa mid /\ ci_mono mid last` by
    metis_tac[ci_mono_compile_alloc_buffer, compile_create_kwarg_allocas_mono, pairTheory.SND] >>
  `fn_has_code sa mid fn /\ fn_has_code mid last fn` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  mp_tac (Q.INST [`n` |-> `type_memory_bytes ce h1`,`st` |-> `sa`,
    `last` |-> `mid`] (SPEC_ALL grouped_dispatch_alloca_step)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u`,`G1`,`tn1`,`q`,`p0`] strip_assume_tac) >>
  qpat_assum `!sa sb kwvars s G tn. _`
    (qspecl_then [`mid`,`last`,`rest`,`u`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  `!v. not_fresh_at sa v ==> not_fresh_at mid v` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `not_fresh_at last q` by
    (irule not_fresh_at_mono >> qexists_tac `mid` >> fs[ci_mono_def]) >>
  `lookup_var q t = lookup_var q u /\ FLOOKUP G' q = FLOOKUP G1 q /\
    op_taint tn' (Var q) = op_taint tn1 (Var q)` by metis_tac[] >>
  `ptr_covers G' tn' q t (type_memory_bytes ce h1)` by
    (pure_rewrite_tac [ptr_covers_def] >>
     MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`lookup_var q t = lookup_var q u`,`FLOOKUP G' q = FLOOKUP G1 q`,
        `op_taint tn' (Var q) = op_taint tn1 (Var q)`] >>
     qpat_assum `ptr_covers G1 tn1 q u _` (ACCEPT_TAC o REWRITE_RULE [ptr_covers_def])) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- fs[selected_registration_frame_def]
  >- decide_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (simp_tac (srw_ss()) [listTheory.MEM] >>
      rpt gen_tac >> disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (gvs[] >> qexistsl_tac [`sa.cs_next_id`,`p0`] >>
          `p0 < dimword (:256)` by decide_tac >> simp[LESS_MOD] >>
          metis_tac[]) >>
      qpat_assum `!name op ty e. MEM (name,op,ty,e) rest ==> _`
        (qspecl_then [`name`,`op`,`ty`,`e`] (drule_then ACCEPT_TAC)))
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (u,G1,tn1) [] _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      metis_tac[gas_origin_ptr_path_trans, APPEND_NIL])
  >> gen_tac >> disch_tac >>
  qpat_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1 u) ==> _`
    (qspec_then `D` MATCH_MP_TAC) >>
  qpat_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==> _`
    (qspec_then `D` (drule_then ACCEPT_TAC))
QED
