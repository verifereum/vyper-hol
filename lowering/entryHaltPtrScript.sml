(* Pointer-safe external return fragments. *)
Theory entryHaltPtr
Ancestors
  fragExecPtr loweringHalt bodyPtrDefs ptrSafeRun ptrDiscipline
  fragExec venomInst venomState venomExecSemantics
  stmtLowering compileEnv contextCodegenRelProps emitHelper
  abiBuiltinAllocation finite_map representationCleanPtr allocationPtr

Theorem stop_frag_ptr:
  !cx ctx PG st st' id P Q R.
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [mk_inst id STOP [] []] /\
    (!G tn s. P G tn s ==> stor_taint_ok cx tn s /\
       R (G,tn) (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_ptr cx ctx PG st st' P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  disj2_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst id STOP [] []) s =
     Halt (halt_state (s with vs_returndata := []))` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accfupds,
                      instruction_accessors, opcode_case_def, combinTheory.K_THM] >> simp[]) >>
  `run_from 0 ctx fn s = Halt (halt_state (s with vs_returndata := []))` by
    (irule run_from_halt >>
     qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >> simp[mk_inst_def]) >>
  `ghost_run 0 ctx fn PG G tn s = (G,tn)` by
    (gvs[mk_inst_def] >> simp[ghost_run_def, Once ghost_block_def,
                             step_inst_non_invoke]) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  irule ptr_safe_run_stop >> simp[] >> metis_tac[]
QED

Theorem compile_return_none_external_frag_ptr:
  !cx ctx PG cenv lctx ty st x st' nr nkey ut iv P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr ==> iv) /\
    (!G tn s. P G tn s ==> stor_taint_ok cx tn s /\
       R (G,tn) (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_ptr cx ctx PG st st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_inst_def,
          fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  irule stop_frag_ptr >> simp[] >> metis_tac[]
QED

Theorem compile_external_return_word_frag_ptr:
  !cx ctx PG op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!G tn s. P G tn s ==>
       eval_operand op s = SOME w /\ op_taint tn op = {} /\
       stor_taint_ok cx tn s /\
       ?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
             st.cs_next_id = SOME (b,32) /\ b < dimword (:256)) /\
    (!G tn s ss gt. P G tn s /\
       ss.vs_returndata = word_to_bytes w T /\
       ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
       ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
       R gt (Halt ss)) ==>
    frag_exec_ptr cx ctx PG st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_word_parts >> strip_tac >>
  simp[frag_exec_ptr_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
     SOME (mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
     SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
     simp[]) >>
  `?ss. run_from 0 ctx fn s = Halt ss /\
        ss.vs_returndata = word_to_bytes w T /\
        ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
        ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests` by
    (qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`, `buf`, `op`, `w`]
       mp_tac return_word_run >> simp[] >> strip_tac >> metis_tac[]) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  conj_tac >- metis_tac[] >>
  irule ptr_safe_run_return_word >> simp[] >> metis_tac[]
QED

Theorem ptr_safe_run_return_copy:
  !cx ctx func PG G tn s bb id buf src m n cenv es ty sa sb v tv w s1 fuel.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id+1) MCOPY [Var buf; Var src; Lit (n2w m)] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id+2) RETURN [Var buf; Lit (n2w m)] []) /\
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (Var src) s = SOME w /\ src <> buf /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [buf]) (fn_insts func) /\
    n < dimword (:256) /\ m <= n /\ m <= val_footprint tv v /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [buf]) s = OK s1 /\
    ptr_covers G tn src s m /\
    (!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G tn s
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `G' = step_prov PG G i s1` >>
  qabbrev_tac `tn' = step_taint i s s1 tn` >>
  qabbrev_tac `s' = s1 with vs_inst_idx := s.vs_inst_idx + 1` >>
  `ptr_covers G' tn' buf s1 n` by
    (simp[Abbr `G'`, Abbr `tn'`, Abbr `i`] >>
     irule alloca_step_ptr_covers >> metis_tac[]) >>
  `ptr_covers G' tn' src s1 m` by
    (simp[Abbr `G'`, Abbr `tn'`, Abbr `i`] >>
     irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  `stor_taint_ok cx tn' s1` by
    (simp[Abbr `tn'`, Abbr `i`] >>
     irule alloca_step_stor_taint_ok >> metis_tac[]) >>
  `eval_operand (Var src) s1 = SOME w` by
    (`eval_operand (Var src) s1 = eval_operand (Var src) s` by
       (irule alloca_step_operand_preserved >>
        simp[] >> metis_tac[Abbr `i`]) >> simp[]) >>
  `!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn'.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn'`, Abbr `i`] >>
     `j < w2n w + val_footprint tv v` by decide_tac >>
     irule alloca_step_expr_read_clean >> metis_tac[]) >>
  `s1.vs_current_bb = s.vs_current_bb` by
    (qspecl_then [`id`, `n2w n`, `buf`, `s`] strip_assume_tac step_alloca_frame >>
     gvs[Abbr `i`]) >>
  `m < dimword (:256)` by decide_tac >>
  `ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G' tn' s'` by
    (irule ptr_safe_run_copy_return >> simp[Abbr `s'`] >>
     (conj_tac >- gvs[stor_taint_ok_def]) >>
     qexistsl_tac [`buf`, `id+1`, `n2w m`, `src`] >>
     gvs[ptr_covers_def, lookup_var_def, eval_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_LESS_EQ_MONO, arithmeticTheory.LESS_EQ_TRANS]) >>
  `step_inst fuel ctx i s = OK s1` by
    simp[step_inst_non_invoke, Abbr `i`] >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qunabbrev_tac `i` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, arithmeticTheory.ADD1] >>
  gvs[ptr_safe_run_def, Abbr `s'`, Abbr `G'`, Abbr `tn'`]
QED

Theorem compile_external_return_copy_frag_ptr:
  !cx ctx PG src m n nr nkey ut iv st x st' cenv es ty sa sb v tv P Q R.
    compile_external_return (SOME (Var src)) F F (AbiCopy m) n nr nkey ut iv st =
      (x, st') /\ (nr ==> iv) /\ not_fresh_at st src /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    ~is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\ value_has_type tv v /\
    n < dimword (:256) /\ m <= n /\ m <= type_memory_size tv /\
    m <= val_footprint tv v /\
    (!fn G tn s. fn_has_code st st' fn /\ P G tn s ==>
       stmt_state_rel ctx fn cenv cx es s /\
       expr_val_at cenv cx ty sa sb es v (Var src) s /\
       ptr_val_ok cx ty v (Var src) G tn s /\ ptr_covers G tn src s m /\
       stor_taint_ok cx tn s) /\
    (!G tn s ss gt. P G tn s /\
       ss.vs_returndata = mem_bytes_at
         (w2n (THE (lookup_var src s))) m s.vs_memory /\
       ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
       ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
       R gt (Halt ss)) ==>
    frag_exec_ptr cx ctx PG st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_copy_parts >> strip_tac >>
  simp[frag_exec_ptr_def] >> rpt strip_tac >> disj2_tac >>
  `src <> buf` by metis_tac[] >>
  `stmt_state_rel ctx fn cenv cx es s /\
   expr_val_at cenv cx ty sa sb es v (Var src) s /\
   ptr_val_ok cx ty v (Var src) G tn s /\ ptr_covers G tn src s m /\
   stor_taint_ok cx tn s` by metis_tac[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; Var src; Lit (n2w m)] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit (n2w m)] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `?w. eval_operand (Var src) s = SOME w` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `m < dimword (:256)` by decide_tac >>
  `?ss. run_from 0 ctx fn s = Halt ss /\
        ss.vs_returndata = mem_bytes_at (w2n w) m s.vs_memory /\
        ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
        ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests` by
    (qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`, `buf`,
                  `Var src`, `w`, `m`, `n`] mp_tac return_copy_run >>
     impl_tac >- gvs[] >> strip_tac >> metis_tac[]) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  (conj_tac >-
    (gvs[eval_operand_def] >>
     qpat_x_assum `!G tn s ss gt. _` (qspecl_then [`G`, `tn`, `s`, `ss`] mp_tac) >>
     simp[])) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  `!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn.t_mem` by
    (`!j. w2n w <= j /\ j < w2n w + type_memory_size tv ==> j NOTIN tn.t_mem` by
       metis_tac[ptr_val_ok_static_clean] >>
     gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  qspecl_then [`st.cs_next_id`, `n2w n`, `buf`, `s`]
    strip_assume_tac step_alloca_frame >>
  qpat_x_assum `!G tn s ss gt. _` kall_tac >>
  qpat_x_assum `!fn G tn s. _` kall_tac >>
  qpat_x_assum `!i. i < _ ==> _` kall_tac >>
  gvs[] >> drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) ptr_safe_run_return_copy >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem ptr_safe_run_return_copy_zero:
  !cx ctx fn PG G tn s bb id buf op w n cenv es fuel.
    stmt_state_rel ctx fn cenv cx es s /\
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
    op_taint tn op = {} /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx ==>
    ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s
Proof
  rpt strip_tac >>
  qspecl_then [`id`, `n2w n`, `buf`, `s`] strip_assume_tac step_alloca_frame >>
  qabbrev_tac `i = mk_inst id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `G' = step_prov PG G i s1` >>
  qabbrev_tac `tn' = step_taint i s s1 tn` >>
  qabbrev_tac `s' = s1 with vs_inst_idx := s.vs_inst_idx + 1` >>
  `eval_operand op s1 = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `stor_taint_ok cx tn' s1` by
    (simp[Abbr `tn'`, Abbr `i`] >>
     irule alloca_step_stor_taint_ok >> metis_tac[]) >>
  `op_taint tn' op = {} /\ op_taint tn' (Var buf) = {}` by
    (Cases_on `op` >>
     gvs[Abbr `tn'`, Abbr `i`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, eval_operand_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G' tn' s'` by
    (irule ptr_safe_run_copy_return_zero >> simp[Abbr `s'`] >>
     (reverse conj_tac >- gvs[stor_taint_ok_def]) >>
     qexistsl_tac [`a`, `w`, `Var buf`, `id+1`, `op`] >>
     simp[eval_operand_def]) >>
  `step_inst fuel ctx i s = OK s1` by
    simp[step_inst_non_invoke, Abbr `i`] >>
  `ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  qunabbrev_tac `i` >> gvs[mk_inst_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       is_terminator_def, ghost_step_def, arithmeticTheory.ADD1] >>
  gvs[ptr_safe_run_def, Abbr `s'`, Abbr `G'`, Abbr `tn'`]
QED

Theorem compile_external_return_copy_zero_frag_ptr:
  !cx ctx PG op n nr nkey ut iv st x st' cenv es P Q R.
    compile_external_return (SOME op) F F (AbiCopy 0) n nr nkey ut iv st =
      (x, st') /\ (nr ==> iv) /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    n < dimword (:256) /\
    (!fn G tn s. fn_has_code st st' fn /\ P G tn s ==>
       stmt_state_rel ctx fn cenv cx es s /\
       (?w. eval_operand op s = SOME w) /\ op_taint tn op = {} /\
       stor_taint_ok cx tn s) /\
    (!G tn s ss gt. P G tn s /\ ss.vs_returndata = [] /\
       ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
       ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
       R gt (Halt ss)) ==>
    frag_exec_ptr cx ctx PG st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_copy_parts >> strip_tac >>
  simp[frag_exec_ptr_def] >> rpt strip_tac >> disj2_tac >>
  `op <> Var buf` by
    metis_tac[] >>
  `stmt_state_rel ctx fn cenv cx es s /\
   (?w. eval_operand op s = SOME w) /\ op_taint tn op = {} /\
   stor_taint_ok cx tn s` by metis_tac[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; op; Lit 0w] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit 0w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `?ss. run_from 0 ctx fn s = Halt ss /\ ss.vs_returndata = [] /\
        ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
        ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests` by
    (qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`, `buf`,
                  `op`, `w`, `0`, `n`] mp_tac return_copy_run >>
     impl_tac >- gvs[] >>
     simp[valueEncodingTheory.mem_bytes_at_def] >> strip_tac >> metis_tac[]) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  (conj_tac >- metis_tac[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  irule ptr_safe_run_return_copy_zero >> simp[] >> metis_tac[]
QED
