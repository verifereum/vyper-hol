Theory extRetCountedPtr
Ancestors
  entryHaltPtr fragGasPathPtr fragExec
  stmtLowering compileEnv emitHelper contextCodegenRelProps
  loweringHalt ptrSafeRun ptrDiscipline gasCount venomExecSemantics
  fragExecPtr venomInst venomState fragGasSeqPtr bodyPtrDefs venomInstProofs
  emitHelperProps abiBuiltinAllocation finite_map allocaFootprint arithmetic
  allocationPtr memLocDefs contextCodegenRel codegenRel
  typedCopyPtr typedCopyLoopHeaderPtr wordLoadStorePtr
Theorem stop_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (s with vs_returndata := [])))
Proof
  strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn
     (mk_inst id STOP [] []) s` by simp[ptr_inst_ok_stop] >>
  `step_inst_base (mk_inst id STOP [] []) s =
     Halt (halt_state (s with vs_returndata := []))` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  irule (cj 3 gas_path_ptr_rules) >>
  simp[exit_result_def] >>
  simp[gas_path_ptr_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def,
       gas_count_step_def, ptr_safe_step_def, ptr_inst_ok_stop,
       exit_result_def]
QED

Theorem compile_return_none_external_gas_path_ptr:
  compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G tn
    (Halt (halt_state (s with vs_returndata := [])))
Proof
  strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_inst_def,
          fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule stop_gas_path_ptr >> simp[] >>
  qexists_tac `st.cs_next_id` >>
  qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]
QED

Theorem gas_path_ptr_halt_base:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = Halt t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (Halt t)
Proof
  strip_tac >> irule (cj 3 gas_path_ptr_rules) >>
  simp[exit_result_def] >>
  `step_inst 0 ctx i s = Halt t` by simp[step_inst_non_invoke] >>
  asm_rewrite_tac[gas_path_ptr_edge_def] >>
  qexistsl_tac [`0`, `bb`, `i`, `Halt t`] >>
  simp[gas_count_step_def, ptr_safe_step_def, exit_result_def]
QED

Theorem return_zero_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [op; Lit 0w] []) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (set_returndata [] s)))
Proof
  strip_tac >> irule gas_path_ptr_halt_base >> simp[] >>
  reverse conj_tac
  >- (irule ptr_inst_ok_return_zero >> simp[] >> metis_tac[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED

Theorem return_lit_size_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [Var p; Lit n] []) /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s (w2n n) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n w <= j /\ j < w2n w + w2n n ==> j NOTIN tn.t_mem) ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (set_returndata
      (TAKE (w2n n) (DROP (w2n w) s.vs_memory ++ REPLICATE (w2n n) 0w)) s)))
Proof
  strip_tac >> irule gas_path_ptr_halt_base >> simp[] >>
  reverse conj_tac
  >- (irule ptr_inst_ok_return >> simp[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED

Theorem mstore_return_word_gas_path_ptr:
  !cx ctx fn PG G tn s bb id p v w a.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var p; v] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [Var p; Lit 32w] []) /\
    lookup_var p s = SOME a /\ ptr_covers G tn p s 32 /\
    eval_operand v s = SOME w /\ op_taint tn v = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    let u = mstore (w2n a) w s in
    let t = u with vs_inst_idx := SUC s.vs_inst_idx in
    ?G' tn'. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn'
      (Halt (halt_state (set_returndata
        (TAKE 32 (DROP (w2n a) t.vs_memory ++ REPLICATE 32 0w)) t)))
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  qabbrev_tac `i = mk_inst id MSTORE [Var p; v] []` >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_MSTORE, eval_operand_def] >>
  `ptr_covers G tn' p t 32 /\ stor_taint_ok cx tn' t` by
    gvs[ptr_covers_def, stor_taint_ok_def, Abbr `tn'`, Abbr `i`,
        Abbr `t`, Abbr `u`, mstore_def, lookup_var_def,
        step_taint_def, set_var_taint_def, out_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
        op_taint_def, finite_mapTheory.DRESTRICT_UNIV] >>
  `!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn'.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn'`, Abbr `i`] >>
     irule mstore_word_clean >> simp[eval_operand_def] >> metis_tac[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn' t 0 G tn'
     (Halt (halt_state (set_returndata
       (TAKE 32 (DROP (w2n a) t.vs_memory ++ REPLICATE 32 0w)) t)))` by
    (`~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1 /\ lookup_var p t = SOME a` by
       fs[Abbr `t`, Abbr `u`, mstore_def, lookup_var_def,
            arithmeticTheory.ADD1] >>
     irule (return_lit_size_gas_path_ptr |> SPEC_ALL |>
       Q.INST [`n` |-> `32w`] |> SRULE [wordsTheory.dimword_def]) >>
     simp[] >> qexistsl_tac [`id + 1`, `p`] >> simp[]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mstore >> simp[]) >>
  qexistsl_tac [`G`, `tn'`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |>
    Q.INST [`i` |-> `mk_inst id MSTORE [Var p; v] []`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`id`, `p`, `u`, `v`] >>
  gvs[Abbr `t`, Abbr `tn'`, Abbr `i`, step_prov_def,
      set_prov_def, mk_inst_def, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem alloca_return_word_gas_path_ptr:
  !cx ctx fn PG G tn s bb id buf op w base.
    ~s.vs_halted /\
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
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt strip_tac >> rename1 `SOME (addr,32)` >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit 32w] [buf]` >>
  qabbrev_tac `u = update_var buf (n2w addr)
    (abi_builtin_allocate_state id 32 s)` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >>
     irule step_alloca_site >> simp[wordsTheory.dimword_def]) >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G1 tn1 buf s1 32` by
    (simp[ptr_covers_def, Abbr `G1`, Abbr `tn1`, Abbr `i`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
          op_taint_def, Abbr `s1`, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, LESS_MOD] >> metis_tac[]) >>
  `eval_operand op s1 = SOME w /\ op_taint tn1 op = {}` by
    (Cases_on `op` >>
     gvs[Abbr `tn1`, Abbr `i`, Abbr `s1`, Abbr `u`,
         abi_builtin_allocate_state_def, update_var_def, eval_operand_def,
         lookup_var_def, op_taint_def, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  `stor_taint_ok cx tn1 s1 /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = s.vs_inst_idx + 1 /\ ~s1.vs_halted /\
   lookup_var buf s1 = SOME (n2w addr)` by
    (Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
     fs[stor_taint_ok_def, Abbr `tn1`, Abbr `i`, Abbr `s1`, Abbr `u`,
        step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
        abi_builtin_allocate_state_def, update_var_def, lookup_var_def,
        mk_inst_def, arithmeticTheory.ADD1, FLOOKUP_UPDATE]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s1.vs_inst_idx + 1) =
     SOME (mk_inst ((id + 1) + 1) RETURN [Var buf; Lit 32w] [])` by simp[] >>
  drule_all mstore_return_word_gas_path_ptr >> simp[] >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (Halt h)` >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `h`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |>
    Q.INST [`i` |-> `mk_inst id ALLOCA [Lit 32w] [buf]`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`buf`, `id`, `u`] >>
  gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]
QED

Theorem compile_external_return_word_gas_path_ptr:
  !cx ctx fn PG G tn s op ei msz nkey ut iv st x st' w base.
    compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    fn_has_code st st' fn /\ ~block_is_terminated st /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
      st.cs_next_id = SOME (base,32) /\ base < dimword (:256) ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_word_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
     SOME (mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
     SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >> simp[]) >>
  irule alloca_return_word_gas_path_ptr >> simp[] >> metis_tac[]
QED

Theorem mcopy_return_gas_path_ptr:
  !cx ctx fn PG G tn s bb id dst src n a b.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; Lit n] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [Var dst; Lit n] []) /\
    lookup_var dst s = SOME a /\ lookup_var src s = SOME b /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
    (!j. w2n b <= j /\ j < w2n b + w2n n ==> j NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst id MCOPY [Var dst; Var src; Lit n] []` >>
  qabbrev_tac `u = mcopy (w2n a) (w2n b) (w2n n) s` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, eval_operand_def]) >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G tn1 dst s1 (w2n n) /\ stor_taint_ok cx tn1 s1` by
    gvs[ptr_covers_def, stor_taint_ok_def, Abbr `tn1`, Abbr `i`,
        Abbr `s1`, Abbr `u`, mcopy_def, write_memory_with_expansion_def,
        lookup_var_def, step_taint_def, set_var_taint_def, out_taint_def,
        store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
        op_taint_def, DRESTRICT_UNIV] >>
  `!j. w2n a <= j /\ j < w2n a + w2n n ==> j NOTIN tn1.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn1`, Abbr `i`] >>
     irule mcopy_range_clean >> simp[eval_operand_def] >> metis_tac[]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = s.vs_inst_idx + 1 /\ lookup_var dst s1 = SOME a` by
    fs[Abbr `s1`, Abbr `u`, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, ADD1] >>
  `?t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn1 s1 0 G tn1 (Halt t)` by
    (irule_at (Pos hd) return_lit_size_gas_path_ptr >>
     simp[] >> qexistsl_tac [`a`, `dst`, `n`, `id + 1`] >> simp[ADD_COMM]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mcopy >> simp[]) >>
  qexistsl_tac [`G`, `tn1`, `t`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |> Q.INST [`n` |-> `0`] |>
    Q.INST [`i` |-> `mk_inst id MCOPY [Var dst; Var src; Lit n] []`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`dst`, `id`, `n`, `src`, `u`] >>
  gvs[Abbr `s1`, Abbr `tn1`, Abbr `i`, step_prov_def,
      set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem alloca_copy_return_gas_path_ptr:
  !cx ctx fn PG G tn s bb id buf src m n cenv es ty sa sb v tv w u.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id+1) MCOPY [Var buf; Var src; Lit (n2w m)] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id+2) RETURN [Var buf; Lit (n2w m)] []) /\
    stmt_state_rel ctx fn cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (Var src) s = SOME w /\ src <> buf /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn) /\
    n < dimword (:256) /\ m <= n /\ m <= val_footprint tv v /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [buf]) s = OK u /\
    ptr_covers G tn src s m /\
    (!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G1 tn1 buf u n` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_ptr_covers >> metis_tac[]) >>
  `ptr_covers G1 tn1 src u m` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  `stor_taint_ok cx tn1 u` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_stor_taint_ok >> metis_tac[]) >>
  `eval_operand (Var src) u = SOME w` by
    (`eval_operand (Var src) u = eval_operand (Var src) s` by
       (irule alloca_step_operand_preserved >> simp[] >> metis_tac[Abbr `i`]) >>
     simp[]) >>
  `!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn1.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn1`, Abbr `i`] >>
     `j < w2n w + val_footprint tv v` by decide_tac >>
     irule alloca_step_expr_read_clean >> metis_tac[]) >>
  `step_inst 0 ctx i s = OK u` by simp[Abbr `i`, step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (`~is_terminator i.inst_opcode` by simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
     drule_all step_preserves_halted >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `m < dimword (:256)` by decide_tac >>
  `?a. lookup_var buf u = SOME a` by gvs[ptr_covers_def] >>
  `?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G1 tn1 s1 0 G' tn' (Halt t)` by
    (irule mcopy_return_gas_path_ptr >>
     simp[Abbr `s1`, ADD1] >>
     (conj_tac >- gvs[stor_taint_ok_def]) >>
     qexistsl_tac [`a`, `w`, `buf`, `id+1`, `n2w m`, `src`] >>
     gvs[ptr_covers_def, lookup_var_def, eval_operand_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |> Q.INST [`n` |-> `0`] |>
    Q.INST [`i` |-> `mk_inst id ALLOCA [Lit (n2w n)] [buf]`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`buf`, `id`, `n`, `u`] >>
  gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]
QED

Theorem compile_external_return_copy_gas_path_ptr:
  !cx ctx fn PG G tn s src m n nkey ut iv st x st' cenv es ty sa sb v tv w.
    compile_external_return (SOME (Var src)) F F (AbiCopy m) n F nkey ut iv st =
      (x,st') /\ not_fresh_at st src /\
    fn_has_code st st' fn /\ ~block_is_terminated st /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (Var src) s = SOME w /\
    n < dimword (:256) /\ m <= n /\ m <= val_footprint tv v /\
    ptr_covers G tn src s m /\
    (!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `src <> buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; Var src; Lit (n2w m)] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit (n2w m)] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  qspecl_then [`st.cs_next_id`, `n2w n`, `buf`, `s`]
    strip_assume_tac step_alloca_frame >>
  qpat_x_assum `!i. i < _ ==> _` kall_tac >>
  gvs[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) alloca_copy_return_gas_path_ptr >>
  simp[] >> disch_then drule_all >> simp[ADD_COMM]
QED

Theorem mcopy_return_zero_gas_path_ptr:
  !cx ctx fn PG G tn s bb id dst src a b.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [dst; src; Lit 0w] []) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) RETURN [dst; Lit 0w] []) /\
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    op_taint tn dst = {} /\ op_taint tn src = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst id MCOPY [dst; src; Lit 0w] []` >>
  qabbrev_tac `u = mcopy (w2n a) (w2n b) 0 s` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >>
     pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, eval_operand_def]) >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `stor_taint_ok cx tn1 s1 /\ op_taint tn1 dst = {} /\
   eval_operand dst s1 = SOME a /\ ~s1.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = s.vs_inst_idx + 1` by
    (gvs[stor_taint_ok_def, Abbr `tn1`, Abbr `i`, Abbr `s1`, Abbr `u`,
         mcopy_def, write_memory_with_expansion_def, eval_operand_def,
         lookup_var_def, step_taint_def, set_var_taint_def, out_taint_def,
         store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
         op_taint_def, DRESTRICT_UNIV, ADD1] >>
     Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def]) >>
  `?t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn1 s1 0 G tn1 (Halt t)` by
    (irule_at (Pos hd) return_zero_gas_path_ptr >>
     simp[] >> qexistsl_tac [`dst`, `id + 1`, `a`] >> simp[]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mcopy_zero >> metis_tac[]) >>
  qexistsl_tac [`G`, `tn1`, `t`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |>
    Q.INST [`i` |-> `mk_inst id MCOPY [dst; src; Lit 0w] []`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`dst`, `id`, `src`, `u`] >>
  gvs[Abbr `s1`, Abbr `tn1`, Abbr `i`, step_prov_def,
      set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem alloca_copy_zero_gas_path_ptr:
  !cx ctx fn PG G tn s bb id buf op w n cenv es.
    ~s.vs_halted /\ stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn) /\
    n < dimword (:256) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id+1) MCOPY [Var buf; op; Lit 0w] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id+2) RETURN [Var buf; Lit 0w] []) /\
    eval_operand op s = SOME w /\ op <> Var buf /\
    op_taint tn op = {} /\ stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt strip_tac >>
  qspecl_then [`id`, `n2w n`, `buf`, `s`] strip_assume_tac step_alloca_frame >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `G1 = step_prov PG G i s1` >>
  qabbrev_tac `tn1 = step_taint i s s1 tn` >>
  qabbrev_tac `s2 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand op s1 = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `stor_taint_ok cx tn1 s1` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_stor_taint_ok >> metis_tac[]) >>
  `op_taint tn1 op = {} /\ op_taint tn1 (Var buf) = {}` by
    (Cases_on `op` >>
     gvs[Abbr `tn1`, Abbr `i`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, eval_operand_def, FLOOKUP_UPDATE]) >>
  `step_inst 0 ctx i s = OK s1` by simp[Abbr `i`, step_inst_non_invoke] >>
  `~s1.vs_halted` by
    (`~is_terminator i.inst_opcode` by simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
     drule_all step_preserves_halted >> simp[]) >>
  `?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G1 tn1 s2 0 G' tn' (Halt t)` by
    (irule mcopy_return_zero_gas_path_ptr >> simp[Abbr `s2`, ADD1] >>
     (reverse conj_tac >- gvs[stor_taint_ok_def]) >>
     qexistsl_tac [`a`, `w`, `Var buf`, `id+1`, `op`] >> simp[eval_operand_def]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |> Q.INST [`n` |-> `0`] |>
    Q.INST [`i` |-> `mk_inst id ALLOCA [Lit (n2w n)] [buf]`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`buf`, `id`, `n`, `s1`] >>
  gvs[Abbr `s2`, Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]
QED

Theorem compile_external_return_copy_zero_gas_path_ptr:
  !cx ctx fn PG G tn s op n nkey ut iv st x st' cenv es w.
    compile_external_return (SOME op) F F (AbiCopy 0) n F nkey ut iv st = (x,st') /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    fn_has_code st st' fn /\ ~block_is_terminated st /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; op; Lit 0w] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit 0w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  qpat_x_assum `!i. i < _ ==> _` kall_tac >>
  gvs[] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) alloca_copy_zero_gas_path_ptr >>
  simp[] >> metis_tac[]
QED

Theorem ptr_inst_ok_return_var_size:
  ptr_covers G tn p s (w2n n) /\ lookup_var len s = SOME n /\
  op_taint tn (Var len) = {} /\ stor_taint_ok cx tn s /\
  ~ctx_has_dalloca ctx /\
  (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
         i < w2n w + w2n n ==> i NOTIN tn.t_mem) ==>
  ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
    (mk_inst id RETURN [Var p; Var len] []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> Cases_on `op = Var p` >> gvs[] >>
     Cases_on `op = Var len` >> gvs[]) >>
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

Theorem return_var_size_gas_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id RETURN [Var p; Var len] []) /\
  lookup_var p s = SOME w /\ lookup_var len s = SOME n /\
  op_taint tn (Var len) = {} /\ ptr_covers G tn p s (w2n n) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n w <= j /\ j < w2n w + w2n n ==> j NOTIN tn.t_mem) ==>
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn
    (Halt (halt_state (set_returndata
      (TAKE (w2n n) (DROP (w2n w) s.vs_memory ++ REPLICATE (w2n n) 0w)) s)))
Proof
  strip_tac >> irule gas_path_ptr_halt_base >> simp[] >>
  reverse conj_tac
  >- (irule ptr_inst_ok_return_var_size >> simp[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED

Theorem add_return_raw_gas_path_ptr:
  !cx ctx fn PG G tn s bb id src off len a n total.
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var src; Lit 32w] [off]) /\
  get_instruction bb (s.vs_inst_idx + 1) =
    SOME (mk_inst (id + 1) RETURN [Var off; Var len] []) /\
  src <> off /\ len <> off /\ lookup_var src s = SOME a /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} /\
  ptr_covers G tn src s total /\ 32 <= total /\
  32 + w2n n <= total /\ w2n a + 32 < dimword(:256) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n (a + 32w) <= j /\ j < w2n (a + 32w) + w2n n ==>
        j NOTIN tn.t_mem) ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn'
    (Halt t)
Proof
  rpt gen_tac >> strip_tac >> rename1 `ptr_covers G tn src s cap` >>
  qabbrev_tac `i = mk_inst id ADD [Var src; Lit 32w] [off]` >>
  qabbrev_tac `u = update_var off (a + 32w) s` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `ptr_covers G' tn' off u (w2n n)` by
    (Cases_on `32 < cap`
     >- (simp[Abbr `G'`, Abbr `tn'`, Abbr `i`, Abbr `u`] >>
         irule typed_copy_loop_dynamic_offset_covers >> simp[eval_operand_def] >>
         qexists_tac `cap` >> simp[]) >>
     `cap = 32 /\ w2n n = 0` by decide_tac >>
     `op_taint tn' (Var off) = {}` by
       simp[Abbr `tn'`, Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame] >>
     gvs[ptr_covers_def, wordsTheory.dimword_def] >>
     simp[Abbr `G'`, Abbr `i`, Abbr `u`, step_prov_def, set_prov_def,
          out_prov_def, first_prov_def, op_prov_def, mk_inst_def,
          FLOOKUP_UPDATE, lookup_var_def, update_var_def,
          wordsTheory.w2n_add_2, wordsTheory.dimword_def] >> decide_tac) >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ op_taint tn' (Var len) = {}` by
    (simp[Abbr `tn'`, Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame]) >>
  `tn'.t_imm = tn.t_imm` by
    simp[Abbr `tn'`, Abbr `i`, step_taint_def, store_taint_def,
         adopt_reset_def, imm_taint_def, mk_inst_def] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = s.vs_inst_idx + 1 /\
   lookup_var off t = SOME (a + 32w) /\ lookup_var len t = SOME n /\
   ptr_covers G' tn' off t (w2n n) /\ stor_taint_ok cx tn' t /\
   t.vs_memory = s.vs_memory` by
    gvs[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE, ADD1, ptr_covers_def, stor_taint_ok_def] >>
  `?ss. gas_path_ptr (cx_dead cx) 0 ctx fn PG G' tn' t 0 G' tn' (Halt ss)` by
    (irule_at Any return_var_size_gas_path_ptr >> simp[] >>
     qexistsl_tac [`a + 32w`, `off`, `n`, `len`, `id + 1`] >> simp[]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >>
     gvs[ptr_covers_def, op_taint_def]) >>
  qexistsl_tac [`G'`, `tn'`, `ss`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |> Q.INST
    [`i` |-> `mk_inst id ADD [Var src; Lit 32w] [off]`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`id`, `off`, `src`, `u`] >>
  gvs[Abbr `t`, Abbr `G'`, Abbr `tn'`, Abbr `i`, mk_inst_def]
QED

Theorem mload_return_raw_gas_path_ptr:
  !cx ctx fn PG G tn s bb id src off len a n cap.
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MLOAD [Var src] [len]) /\
  get_instruction bb (s.vs_inst_idx + 1) =
    SOME (mk_inst (id + 1) ADD [Var src; Lit 32w] [off]) /\
  get_instruction bb (s.vs_inst_idx + 2) =
    SOME (mk_inst (id + 2) RETURN [Var off; Var len] []) /\
  src <> len /\ src <> off /\ len <> off /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n /\
  ptr_covers G tn src s cap /\ 32 <= cap /\
  32 + w2n n <= cap /\ w2n a + 32 < dimword(:256) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem) /\
  (!j. w2n (a + 32w) <= j /\ j < w2n (a + 32w) + w2n n ==>
        j NOTIN tn.t_mem) ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn'
    (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst id MLOAD [Var src] [len]` >>
  qabbrev_tac `u = update_var len n s` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base i s = OK u` by
    (`eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
     drule step_MLOAD >> simp[Abbr `i`, Abbr `u`]) >>
  `ptr_covers G1 tn1 src u cap` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `u`] >>
     qpat_x_assum `mload _ _ = n` (fn th => rewrite_tac[GSYM th]) >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn1 (Var len) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `i`, Abbr `u`] >>
     qpat_x_assum `mload _ _ = n` (fn th => rewrite_tac[GSYM th]) >>
     irule mload_ghost_clean >> simp[eval_operand_def]) >>
  `tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `i`, step_taint_def, store_taint_def,
         adopt_reset_def, imm_taint_def, mk_inst_def] >>
  `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = s.vs_inst_idx + 1 /\
   lookup_var src s1 = SOME a /\ lookup_var len s1 = SOME n /\
   ptr_covers G1 tn1 src s1 cap /\ stor_taint_ok cx tn1 s1` by
    gvs[Abbr `s1`, Abbr `u`, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE, ADD1, ptr_covers_def, stor_taint_ok_def] >>
  `?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G1 tn1 s1 0 G' tn'
     (Halt t)` by
    (irule add_return_raw_gas_path_ptr >> simp[] >>
     qexistsl_tac [`a`, `id + 1`, `len`, `n`, `off`, `src`, `cap`] >>
     simp[]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mload >> simp[] >>
     gvs[ptr_covers_def] >> qexistsl_tac [`a`, `b`, `sz'`] >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
  irule (gas_path_ptr_step |> SPEC_ALL |> Q.INST
    [`i` |-> `mk_inst id MLOAD [Var src] [len]`] |>
    SRULE [mk_inst_def, is_terminator_def]) >>
  simp[] >> qexistsl_tac [`id`, `len`, `src`, `u`] >>
  gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]
QED

Theorem compile_external_return_raw_gas_path_ptr:
  !cx ctx fn PG G tn s src prim ei msz nkey ut iv st x st' a n cap.
  compile_external_return (SOME (Var src)) prim T ei msz F nkey ut iv st = (x,st') /\
  not_fresh_at st src /\ fn_has_code st st' fn /\ ~block_is_terminated st /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n /\
  ptr_covers G tn src s cap /\ 32 <= cap /\
  32 + w2n n <= cap /\ w2n a + 32 < dimword(:256) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem) /\
  (!j. w2n (a + 32w) <= j /\ j < w2n (a + 32w) + w2n n ==>
        j NOTIN tn.t_mem) ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  (* rawReturnHalt's shape theorem is local and is not an exported interface. *)
  `?len off. ~not_fresh_at st len /\ ~not_fresh_at st off /\ len <> off /\
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id MLOAD [Var src] [len];
       mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off];
       mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] []]` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, optional_unlock_view,
          emit_op_def, emit_void_def, emit_inst_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     qexistsl_tac [`STRING #"%" (toString st.cs_next_var)`,
                   `STRING #"%" (toString (st.cs_next_var + 1))`] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `src <> len /\ src <> off` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
      SOME (mk_inst st.cs_next_id MLOAD [Var src] [len]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off]) /\
   get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  irule mload_return_raw_gas_path_ptr >> simp[] >>
  qexistsl_tac [`a`, `cap`, `st.cs_next_id`, `len`, `off`, `src`] >> gvs[]
QED
