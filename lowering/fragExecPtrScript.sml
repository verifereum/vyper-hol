(* Pointer ghost boundaries for lowering fragments. *)
Theory fragExecPtr
Ancestors
  bodyPtrDefs ptrSafeRun ptrDiscipline vyperLoweringCorrect
  venomExecSemantics venomInstProofs contextCodegenRelProps
  venomInst venomState contextCodegenRel codegenRel memLocDefs
  emitHelperProps allocaFootprint abiBuiltinAllocation finite_map arithmetic
  fragExec

Theorem initial_ptr_allocations:
  initial_venom_state_rel tops am tx s ==>
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\
  s.vs_vars = FEMPTY /\ s.vs_memory = [] /\ allocas_from 0 s
Proof
  simp[initial_venom_state_rel_def, allocas_from_def]
QED

Theorem ptr_inst_ok_stop:
  !cx ctx fn G tn s id fuel.
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
      (mk_inst id STOP [] []) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accfupds, instruction_accessors, opcode_case_def] >>
  simp[mk_inst_def, step_taint_def, ret_taint_def,
       stor_taint_ok_def, store_taint_def, adopt_reset_def, imm_taint_def,
       halt_state_def] >>
  gvs[stor_taint_ok_def]
QED

Theorem ptr_safe_run_stop:
  !cx ctx fn PG G tn s bb id fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
     (mk_inst id STOP [] []) s` by metis_tac[ptr_inst_ok_stop] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def,
       ptr_safe_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]
QED

(* ALLOCA records precisely the site chosen by the operational step. *)
Theorem step_prov_alloca:
  !PG G id sz p s b n.
    FLOOKUP s.vs_allocas id = SOME (b,n) ==>
    step_prov PG G (mk_inst id ALLOCA [sz] [p]) s = G |+ (p,(b,n))
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def]
QED

(* A word store kills all taint in the bytes it writes, even when the
   fresh allocation was tainted and the rest of memory remains so. *)
Theorem mstore_word_clean:
  !tn id a v s s' w value i.
    eval_operand a s = SOME w /\ eval_operand v s = SOME value /\
    op_taint tn v = {} /\
    w2n w <= i /\ i < w2n w + 32 ==>
    i NOTIN (step_taint (mk_inst id MSTORE [a;v] []) s s' tn).t_mem
Proof
  rpt strip_tac >>
  gvs[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
      source_memory_write_ranges_def, fixed_source_write_range_def,
      mk_inst_def, range_bytes_def]
QED

Theorem ptr_inst_ok_return:
  !cx ctx fn G tn s id p n.
    ptr_covers G tn p s (w2n n) /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
           i < w2n w + w2n n ==> i NOTIN tn.t_mem) ==>
    !fuel. ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
      (mk_inst id RETURN [Var p; Lit n] []) s
Proof
  rpt strip_tac >>
  gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> Cases_on `op = Var p` >> gvs[] >>
     Cases_on `op = Lit n` >> gvs[op_taint_def]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, halt_state_def, set_returndata_def,
       ret_taint_def] >>
  gvs[stor_taint_ok_def, cx_dead_def, pred_setTheory.SUBSET_DEF] >>
  gen_tac >> Cases_on `x < w2n n` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem ptr_inst_ok_alloca:
  !D ctx fn G tn s id n p fuel.
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id ALLOCA [Lit n] [p]) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, op_taint_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_inst_ok_mstore:
  !D ctx fn G tn s id p v fuel.
    ptr_covers G tn p s 32 /\ op_taint tn v = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MSTORE [Var p; v] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_inst_ok_mcopy_operand:
  !D ctx fn G tn s id dst src count_op n fuel.
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\
    ptr_covers G tn src s (w2n n) /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  `step_inst fuel ctx (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
     OK (mcopy (w2n w) (w2n w') (w2n n) s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  gvs[mk_inst_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, eval_operand_def,
       mem_write_ops_def, mem_read_ops_def, sized_source_write_range_def,
       mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `op` >>
  Cases_on `count_op` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem ptr_inst_ok_mcopy:
  !D ctx fn G tn s id dst src n fuel.
    ptr_covers G tn dst s (w2n n) /\
    ptr_covers G tn src s (w2n n) /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MCOPY [Var dst; Var src; Lit n] []) s
Proof
  rpt strip_tac >> irule ptr_inst_ok_mcopy_operand >>
  simp[eval_operand_def, op_taint_def]
QED

Theorem mcopy_range_clean:
  !tn id dst src n s s' a b i.
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    (!j. w2n b <= j /\ j < w2n b + w2n n ==> j NOTIN tn.t_mem) /\
    w2n a <= i /\ i < w2n a + w2n n ==>
    i NOTIN (step_taint (mk_inst id MCOPY [dst;src;Lit n] []) s s' tn).t_mem
Proof
  rpt strip_tac >>
  gvs[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
      source_memory_write_ranges_def, fixed_source_write_range_def,
      mk_inst_def, range_bytes_def, eval_operand_def,
      sized_source_write_range_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem ptr_safe_run_copy_return:
  !cx ctx fn PG G tn s bb id dst src n fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; Lit n] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [Var dst; Lit n] []) /\
    ptr_covers G tn dst s (w2n n) /\
    ptr_covers G tn src s (w2n n) /\
    (!w i. lookup_var src s = SOME w /\ w2n w <= i /\
           i < w2n w + w2n n ==> i NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst; Var src; Lit n] []) s` by
    metis_tac[ptr_inst_ok_mcopy] >>
  `?a. lookup_var dst s = SOME a` by gvs[ptr_covers_def] >>
  `?b. lookup_var src s = SOME b` by gvs[ptr_covers_def] >>
  qabbrev_tac `i = mk_inst id MCOPY [Var dst; Var src; Lit n] []` >>
  qabbrev_tac `t = mcopy (w2n a) (w2n b) (w2n n) s` >>
  `step_inst fuel ctx i s = OK t` by
    (simp[Abbr `i`, Abbr `t`, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def, eval_operand_def]) >>
  qabbrev_tac `tn' = step_taint i s t tn` >>
  qabbrev_tac `s' = t with vs_inst_idx := s.vs_inst_idx + 1` >>
  `ptr_covers G tn' dst s' (w2n n) /\ stor_taint_ok cx tn' s'` by
    gvs[ptr_covers_def, stor_taint_ok_def, Abbr `tn'`, Abbr `i`,
        Abbr `s'`, Abbr `t`, mcopy_def, write_memory_with_expansion_def,
        lookup_var_def, step_taint_def, set_var_taint_def, out_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
        op_taint_def, finite_mapTheory.DRESTRICT_UNIV] >>
  `!j. w2n a <= j /\ j < w2n a + w2n n ==> j NOTIN tn'.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn'`, Abbr `i`] >>
     irule mcopy_range_clean >> simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn'
    (mk_inst (id + 1) RETURN [Var dst; Lit n] []) s'` by
    (irule ptr_inst_ok_return >> simp[] >>
     gvs[Abbr `s'`, Abbr `t`, mcopy_def,
         write_memory_with_expansion_def, lookup_var_def]) >>
  `s'.vs_inst_idx = s.vs_inst_idx + 1 /\ lookup_var dst s' = SOME a` by
    gvs[Abbr `s'`, Abbr `t`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  qunabbrev_tac `i` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, step_prov_def, set_prov_def,
       arithmeticTheory.ADD1, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def]
QED

Theorem ptr_safe_run_store_return_word:
  !cx ctx fn PG G tn s bb id p v w fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var p; v] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [Var p; Lit 32w] []) /\
    ptr_covers G tn p s 32 /\ eval_operand v s = SOME w /\
    op_taint tn v = {} /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
     (mk_inst id MSTORE [Var p; v] []) s` by
    metis_tac[ptr_inst_ok_mstore] >>
  `?a. lookup_var p s = SOME a` by gvs[ptr_covers_def] >>
  qabbrev_tac `i = mk_inst id MSTORE [Var p; v] []` >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  `step_inst fuel ctx i s = OK t` by
    simp[Abbr `i`, Abbr `t`, step_inst_non_invoke, step_MSTORE,
         eval_operand_def] >>
  qabbrev_tac `tn' = step_taint i s t tn` >>
  qabbrev_tac `s' = t with vs_inst_idx := s.vs_inst_idx + 1` >>
  `ptr_covers G tn' p s' 32 /\ stor_taint_ok cx tn' s'` by
    gvs[ptr_covers_def, stor_taint_ok_def, Abbr `tn'`, Abbr `i`,
        Abbr `s'`, Abbr `t`, mstore_def, lookup_var_def,
        step_taint_def, set_var_taint_def, out_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
        op_taint_def, finite_mapTheory.DRESTRICT_UNIV] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn'.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn'`, Abbr `i`] >>
     irule mstore_word_clean >> simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn'
     (mk_inst (id + 1) RETURN [Var p; Lit 32w] []) s'` by
    (irule ptr_inst_ok_return >> simp[wordsTheory.dimword_def] >>
     gvs[Abbr `s'`, Abbr `t`, mstore_def, lookup_var_def]) >>
  `s'.vs_inst_idx = s.vs_inst_idx + 1 /\
   lookup_var p s' = SOME a` by
    gvs[Abbr `s'`, Abbr `t`, mstore_def, lookup_var_def] >>
  qunabbrev_tac `i` >>
  gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, step_prov_def, set_prov_def,
       arithmeticTheory.ADD1, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def]
QED

Theorem ptr_safe_run_return_word:
  !cx ctx fn PG G tn s bb id buf op w base fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit 32w] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) MSTORE [Var buf; op] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var buf; Lit 32w] []) /\
    FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id =
      SOME (base,32) /\ base < dimword (:256) /\
    eval_operand op s = SOME w /\ op <> Var buf /\
    op_taint tn op = {} /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit 32w] [buf]` >>
  rename1 `SOME (addr,32)` >>
  qabbrev_tac `t = update_var buf (n2w addr)
    (abi_builtin_allocate_state id 32 s)` >>
  `step_inst fuel ctx i s = OK t` by
    (simp[Abbr `i`, Abbr `t`, step_inst_non_invoke] >>
     irule step_alloca_site >> simp[wordsTheory.dimword_def]) >>
  qabbrev_tac `G' = step_prov PG G i t` >>
  qabbrev_tac `tn' = step_taint i s t tn` >>
  qabbrev_tac `s' = t with vs_inst_idx := s.vs_inst_idx + 1` >>
  `ptr_covers G' tn' buf s' 32` by
    (simp[ptr_covers_def, Abbr `G'`, Abbr `tn'`, Abbr `i`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
          op_taint_def, Abbr `s'`, Abbr `t`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, LESS_MOD] >> metis_tac[]) >>
  `eval_operand op s' = SOME w /\ op_taint tn' op = {}` by
    (Cases_on `op` >>
     gvs[Abbr `tn'`, Abbr `i`, Abbr `s'`, Abbr `t`,
         abi_builtin_allocate_state_def, update_var_def, eval_operand_def,
         lookup_var_def, op_taint_def, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  `stor_taint_ok cx tn' s' /\ s'.vs_current_bb = s.vs_current_bb /\
   s'.vs_inst_idx = s.vs_inst_idx + 1` by
    (Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
     simp[stor_taint_ok_def, Abbr `tn'`, Abbr `i`, Abbr `s'`, Abbr `t`,
          step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
          abi_builtin_allocate_state_def, update_var_def, mk_inst_def] >>
     gvs[stor_taint_ok_def]) >>
  `ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G' tn' s'` by
    (irule ptr_safe_run_store_return_word >> simp[] >>
     qexistsl_tac [`id + 1`, `buf`, `op`, `w`] >> simp[]) >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qunabbrev_tac `i` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, arithmeticTheory.ADD1] >>
  gvs[ptr_safe_run_def]
QED

Theorem frag_exec_ptr_seq:
  !cx ctx PG st1 st2 st3 P Q Q2 R.
    frag_exec_ptr cx ctx PG st1 st2 P Q R /\
    frag_exec_ptr cx ctx PG st2 st3 Q Q2 R /\
    cs_extends st1 st2 /\ cs_extends st2 st3 ==>
    frag_exec_ptr cx ctx PG st1 st3 P Q2 R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  `fn_has_code st1 st2 fn /\ fn_has_code st2 st3 fn` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `frag_exec_ptr _ _ _ st1 st2 _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_ptr_def]) >>
  disch_then (qspecl_then [`fn`, `G`, `tn`, `s`] mp_tac) >>
  simp[] >> strip_tac
  >- (rename1 `Q G2 tn2 s2` >>
      qpat_x_assum `frag_exec_ptr _ _ _ st2 st3 _ _ _`
        (mp_tac o SIMP_RULE std_ss [frag_exec_ptr_def]) >>
      disch_then (qspecl_then [`fn`, `G2`, `tn2`, `s2`] mp_tac) >>
      simp[] >> strip_tac
      >- (disj1_tac >> rename1 `Q2 G3 tn3 s3` >>
          qexistsl_tac [`G3`, `tn3`, `s3`] >> simp[] >>
          rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >>
          rename1 `run_from k ctx fn s2 = _` >>
          `!e. run_from k ctx fn s2 <> Error e` by metis_tac[] >>
          first_x_assum drule_all >> strip_tac >>
          metis_tac[]) >>
      disj2_tac >>
      `!e. run_from fuel ctx fn s2 <> Error e` by
        metis_tac[exit_result_not_error] >>
      first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem ptr_safe_run_all_fuel:
  !D lo fuel ctx fn PG G tn s.
    ptr_safe_run D lo fuel ctx fn PG G tn s /\
    (!e. run_from fuel ctx fn s <> Error e) ==>
    !m. ptr_safe_run D lo m ctx fn PG G tn s
Proof
  rpt strip_tac >> Cases_on `m <= fuel`
  >- metis_tac[ptr_safe_run_fuel_mono_down] >>
  gvs[ptr_safe_run_def, run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  irule (cj 2 ptr_safe_fuel_mono_up) >> qexists_tac `fuel` >>
  simp[block_run_def]
QED

(* Conditional fragment transport needs a non-error continuation witness;
   all-fuel safety alone does not supply one. *)
Theorem frag_exec_ptr_complete:
  !cx ctx PG sa sb P Q R fn G0 tn0 s0.
    frag_exec_ptr cx ctx PG sa sb P Q R /\ fn_has_code sa sb fn /\
    ~ctx_has_dalloca ctx /\ P G0 tn0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!G tn s. Q G tn s /\ ~s.vs_halted /\
         s.vs_current_bb = sb.cs_current_bb /\
         s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
         ?fuel r. run_from fuel ctx fn s = r /\ (!e. r <> Error e) /\
                  ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s) ==>
    !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G0 tn0 s0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_ptr_def]) >>
  disch_then (qspecl_then [`fn`, `G0`, `tn0`, `s0`] mp_tac) >>
  simp[] >> strip_tac
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      metis_tac[ptr_safe_run_all_fuel]) >>
  metis_tac[exit_result_not_error, ptr_safe_run_all_fuel]
QED

(* Empty ranges require evaluated, untainted addresses, not provenance. *)
Theorem ptr_inst_ok_mcopy_zero:
  !D ctx fn G tn s id dst src a b fuel.
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    op_taint tn dst = {} /\ op_taint tn src = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MCOPY [dst; src; Lit 0w] []) s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [dst; src; Lit 0w] []) s =
     OK (mcopy (w2n a) (w2n b) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, eval_operand_def,
       mcopy_def, write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = dst` >> gvs[] >>
  Cases_on `op = src` >> gvs[] >>
  Cases_on `op = Lit 0w` >> gvs[op_taint_def]
QED

Theorem ptr_inst_ok_return_zero:
  !cx ctx fn G tn s id op a fuel.
    eval_operand op s = SOME a /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
      (mk_inst id RETURN [op; Lit 0w] []) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, halt_state_def, set_returndata_def,
       ret_taint_def] >>
  gvs[stor_taint_ok_def, cx_dead_def, pred_setTheory.SUBSET_DEF] >>
  qx_gen_tac `operand` >> Cases_on `operand = op` >> gvs[] >>
  Cases_on `operand = Lit 0w` >> gvs[op_taint_def]
QED

Theorem ptr_safe_run_copy_return_zero:
  !cx ctx fn PG G tn s bb id dst src a b fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [dst; src; Lit 0w] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [dst; Lit 0w] []) /\
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    op_taint tn dst = {} /\ op_taint tn src = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
    (mk_inst id MCOPY [dst; src; Lit 0w] []) s` by
    metis_tac[ptr_inst_ok_mcopy_zero] >>
  qabbrev_tac `i = mk_inst id MCOPY [dst; src; Lit 0w] []` >>
  qabbrev_tac `t = mcopy (w2n a) (w2n b) 0 s` >>
  `step_inst fuel ctx i s = OK t` by
    (simp[Abbr `i`, Abbr `t`, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accfupds,
                      instruction_accessors, opcode_case_def] >>
     simp[eval_operand_def]) >>
  qabbrev_tac `tn' = step_taint i s t tn` >>
  qabbrev_tac `s' = t with vs_inst_idx := s.vs_inst_idx + 1` >>
  `stor_taint_ok cx tn' s' /\ op_taint tn' dst = {} /\
   eval_operand dst s' = SOME a /\
   s'.vs_current_bb = s.vs_current_bb /\
   s'.vs_inst_idx = s.vs_inst_idx + 1` by
    (gvs[stor_taint_ok_def, Abbr `tn'`, Abbr `i`, Abbr `s'`, Abbr `t`,
        mcopy_def, write_memory_with_expansion_def, eval_operand_def,
        lookup_var_def, step_taint_def, set_var_taint_def, out_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
        op_taint_def, finite_mapTheory.DRESTRICT_UNIV] >>
    Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def]) >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn'
    (mk_inst (id + 1) RETURN [dst; Lit 0w] []) s'` by
    metis_tac[ptr_inst_ok_return_zero] >>
  qunabbrev_tac `i` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, step_prov_def, set_prov_def,
       arithmeticTheory.ADD1, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def]
QED
