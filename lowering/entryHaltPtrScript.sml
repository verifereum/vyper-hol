(* Pointer-safe external return fragments. *)
Theory entryHaltPtr
Ancestors
  fragExecPtr loweringHalt bodyPtrDefs ptrSafeRun ptrDiscipline
  fragExec venomInst venomState venomExecSemantics
  stmtLowering compileEnv contextCodegenRelProps emitHelper
  abiBuiltinAllocation finite_map representationCleanPtr allocationPtr
  fragGasOriginPtrExec fragGasSeqPtr allocaSiteResource

Theorem external_return_word_suffix_full:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x, st') /\
  fn_has_code st st' func /\
  stmt_state_rel ctx func cenv cx es s /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  stor_taint_ok_at D tn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ss G' tn'.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (Halt ss, G', tn') /\
    ss.vs_returndata = word_to_bytes w T /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  drule (Q.INST [`nr` |-> `F`] compile_external_return_word_parts) >>
  simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
     SOME (mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
     SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
     simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >> simp[listTheory.MEM_EL] >>
     qexists_tac `LENGTH st.cs_current_insts` >> simp[]) >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
      sz = 32 /\ b + 32 < dimword (:256)` by
    (rpt strip_tac >> drule_all stmt_state_rel_alloca_site_bound >> simp[]) >>
  `alloca_room ctx func s /\ alloca_inv s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  mp_tac (Q.INST [`inst` |-> `mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]`,
                 `out` |-> `buf`] alloca_site32_execute) >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds] >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[combinTheory.K_THM, mk_inst_def])) >> strip_tac >>
  fs[combinTheory.K_THM, GSYM mk_inst_def] >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) s = OK t` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def, eval_operand_def] >>
     simp_tac (srw_ss()) [GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  `b + 32 < dimword (:256)` by
    (drule_all alloca_step_site >> simp[] >> strip_tac >>
     gvs[eval_operand_def]) >>
  qabbrev_tac `ia = mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]` >>
  qabbrev_tac `Ga = step_prov PG G ia t` >>
  qabbrev_tac `ta = step_taint ia s t tn` >>
  qabbrev_tac `sa = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers Ga ta buf t 32` by
    (simp[Abbr `Ga`, Abbr `ta`, Abbr `ia`] >>
     irule alloca_step_ptr_covers >> metis_tac[]) >>
  `ptr_covers Ga ta buf sa 32` by
    gvs[Abbr `sa`, ptr_covers_def, lookup_var_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn ia s` by
    (`ptr_inst_ok D 0 0 ctx func G tn ia s` by
       (simp[Abbr `ia`] >> irule ptr_inst_ok_alloca >> simp[]) >>
     qpat_x_assum `ptr_inst_ok D 0 _ _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [ptr_inst_ok_def, access_ok_def, Abbr `ia`, mk_inst_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def] >>
     asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK sa,Ga,ta)` by
    (simp[Abbr `sa`, Abbr `Ga`, Abbr `ta`] >>
     mp_tac (Q.INST [`i` |-> `ia`, `u` |-> `t`] straight_line_origin_ptr_edge) >>
     simp[Abbr `ia`, is_terminator_def] >> disch_then irule >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          mk_inst_def]) >>
  `eval_operand op sa = SOME w /\ op_taint ta op = {}` by
    (`eval_operand op t = eval_operand op s` by
       (irule alloca_step_operand_preserved >>
        qexistsl_tac [`st.cs_next_id`, `32`, `buf`] >> simp[] >>
        metis_tac[]) >>
     conj_tac
     >- simp[Abbr `sa`, eval_operand_def, lookup_var_def] >>
     Cases_on `op` >>
     simp_tac (srw_ss()) [Abbr `ta`, Abbr `ia`, op_taint_def,
         step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
         FLOOKUP_UPDATE] >>
     fs[op_taint_def, FLOOKUP_UPDATE, eval_operand_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (irule ptrSafetyTransportTheory.step_inst_allocas_from >>
     qexistsl_tac [`ctx`, `0`, `ia`, `s`] >>
     simp[step_inst_non_invoke, Abbr `ia`]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables /\ t.vs_logs = s.vs_logs /\
   t.vs_requests = s.vs_requests /\
   t.vs_pending_deletions = s.vs_pending_deletions` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ia`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exec_alloca_def, mk_inst_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def, AllCaseEqs()]) >>
  `ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
   ta.t_imm = tn.t_imm` by
    simp_tac (srw_ss()) [Abbr `ta`, Abbr `ia`, step_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      LET_THM] >>
  `stor_taint_ok_at D ta sa /\
   sa.vs_current_bb = s.vs_current_bb /\ ~sa.vs_halted /\
   allocas_from lo sa /\ lookup_var buf sa = SOME (n2w b)` by
    (simp[Abbr `sa`, allocas_from_def, lookup_var_def] >>
     fs[stor_taint_ok_at_def, allocas_from_def, lookup_var_def] >>
     metis_tac[]) >>
  qabbrev_tac `im = mk_inst (st.cs_next_id + 1) MSTORE [Var buf;op] []` >>
  qabbrev_tac `u = mstore b w sa` >>
  qabbrev_tac `tm = step_taint im sa u ta` >>
  qabbrev_tac `Gm = step_prov PG Ga im u` >>
  qabbrev_tac `sm = u with vs_inst_idx := SUC sa.vs_inst_idx` >>
  `step_inst_base im sa = OK u` by
    (`eval_operand (Var buf) sa = SOME (n2w b)` by simp[eval_operand_def] >>
     mp_tac (Q.SPECL [`Var buf`, `op`, `n2w b`, `w`]
       emitHelperPropsTheory.step_MSTORE) >>
     disch_then (qspec_then `st.cs_next_id + 1`
       (qspec_then `sa` mp_tac)) >>
     `b < dimword (:256)` by decide_tac >>
     simp[Abbr `im`, Abbr `u`, wordsTheory.w2n_n2w]) >>
  `ptr_inst_ok D lo 0 ctx func Ga ta im sa` by
    (`ptr_inst_ok D 0 0 ctx func Ga ta im sa` by
       (simp[Abbr `im`] >> irule ptr_inst_ok_mstore >> simp[]) >>
     qpat_x_assum `ptr_inst_ok D 0 _ _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [ptr_inst_ok_def, access_ok_def, Abbr `im`,
       mk_inst_def, contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
     asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >>
     simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (sa,Ga,ta) [] (OK sm,Gm,tm)` by
    (simp[Abbr `sm`, Abbr `Gm`, Abbr `tm`] >>
     mp_tac (Q.INST [`i` |-> `im`, `u` |-> `u`, `s` |-> `sa`,
       `G` |-> `Ga`, `tn` |-> `ta`]
       straight_line_origin_ptr_edge) >>
     simp[Abbr `im`, is_terminator_def] >> disch_then irule >>
     simp[Abbr `sa`, unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       eval_operand_def, mk_inst_def, wordsTheory.w2n_n2w] >>
     conj_tac
     >- metis_tac[arithmeticTheory.ADD1, mk_inst_def] >>
     Cases_on `eval_operand op t` >> simp[] >> decide_tac) >>
  `Gm = Ga /\ tm.t_var = ta.t_var /\
   tm.t_stor = ta.t_stor /\ tm.t_trans = ta.t_trans /\
   tm.t_imm = ta.t_imm` by
    simp_tac (srw_ss()) [Abbr `Gm`, Abbr `tm`, Abbr `im`,
      step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def, LET_THM,
      finite_mapTheory.DRESTRICT_UNIV] >>
  `(!v. lookup_var v sm = lookup_var v sa) /\
   sm.vs_allocas = sa.vs_allocas /\
   sm.vs_call_ctx = sa.vs_call_ctx /\ sm.vs_accounts = sa.vs_accounts /\
   sm.vs_transient = sa.vs_transient /\ sm.vs_immutables = sa.vs_immutables /\
   sm.vs_current_bb = sa.vs_current_bb /\ sm.vs_halted = sa.vs_halted` by
    simp_tac (srw_ss()) [Abbr `sm`, Abbr `u`, mstore_def,
      lookup_var_def, LET_THM] >>
  `ptr_covers Gm tm buf sm 32` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`ptr_covers Ga ta buf sa 32`, `Gm = Ga`,
        `tm.t_var = ta.t_var`, `!v. lookup_var v sm = lookup_var v sa`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ptr_covers_def, op_taint_def]) >>
  `allocas_from lo sm` by
    (qpat_x_assum `allocas_from lo sa` mp_tac >>
     qpat_x_assum `sm.vs_allocas = sa.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
  `stor_taint_ok_at D tm sm` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`stor_taint_ok_at D ta sa`, `tm.t_stor = ta.t_stor`,
        `tm.t_trans = ta.t_trans`, `tm.t_imm = ta.t_imm`,
        `sm.vs_call_ctx = sa.vs_call_ctx`, `sm.vs_accounts = sa.vs_accounts`,
        `sm.vs_transient = sa.vs_transient`, `sm.vs_immutables = sa.vs_immutables`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stor_taint_ok_at_def]) >>
  `lookup_var buf sm = SOME (n2w b) /\
   sm.vs_current_bb = s.vs_current_bb /\ ~sm.vs_halted` by
    (asm_rewrite_tac[]) >>
  `!i. b <= i /\ i < b + 32 ==> i NOTIN tm.t_mem` by
    (gen_tac >> strip_tac >>
     simp_tac (srw_ss()) [Abbr `tm`, Abbr `im`] >>
     irule mstore_word_clean >>
     simp[eval_operand_def, wordsTheory.w2n_n2w] >>
     `b < dimword (:256)` by decide_tac >> simp[]) >>
  qabbrev_tac `ir = mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []` >>
  `ptr_inst_ok D lo 0 ctx func Gm tm ir sm` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`ptr_covers Gm tm buf sm 32`, `allocas_from lo sm`,
        `stor_taint_ok_at D tm sm`, `lookup_var buf sm = SOME (n2w b)`,
        `!i. b <= i /\ i < b + 32 ==> i NOTIN tm.t_mem`,
        `b + 32 < dimword (:256)`, `~ctx_has_dalloca ctx`] >>
     simp_tac (srw_ss()) [Abbr `ir`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[ptr_covers_def] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def,
       mk_inst_def, eval_operand_def] >>
     conj_tac >- (rpt strip_tac >> fs[memLocDefsTheory.mem_read_ops_def] >> gvs[]) >>
     conj_tac >-
       (gen_tac >> Cases_on `op = Var buf` >> simp[] >>
        Cases_on `op = Lit 32w` >> simp[op_taint_def]) >>
     simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[eval_operand_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, halt_state_def, set_returndata_def,
       ret_taint_def] >>
     gvs[stor_taint_ok_at_def, pred_setTheory.SUBSET_DEF] >>
     gen_tac >> strip_tac >>
     first_x_assum (qspec_then `x + b` mp_tac) >> simp[]) >>
  `sm.vs_inst_idx = s.vs_inst_idx + 2` by
    (simp_tac (srw_ss()) [Abbr `sm`, Abbr `u`, Abbr `sa`, mstore_def,
      LET_THM, arithmeticTheory.ADD1] >> decide_tac) >>
  qabbrev_tac `ss = halt_state (set_returndata (TAKE 32 (DROP b sm.vs_memory ++ REPLICATE 32 0w)) sm)` >>
  `step_inst_base ir sm = Halt ss` by
    (qpat_x_assum `lookup_var buf sm = SOME (n2w b)` mp_tac >>
     qpat_x_assum `b + 32 < dimword (:256)` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ir`, Abbr `ss`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def, wordsTheory.w2n_n2w]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (sm,Gm,tm) [] (Halt ss,Gm,tm)` by
    (rewrite_tac[fragGasOriginPtrTheory.gas_origin_ptr_edge_def] >>
     conj_tac
     >- (rewrite_tac[fragGasOriginTheory.gas_origin_edge_def] >>
         simp[] >> qexistsl_tac [`0`, `ir`] >>
         simp[step_inst_non_invoke, Abbr `ir`, mk_inst_def,
           gasEventsTheory.gas_events_step_def, exit_result_def] >>
         conj_tac >- metis_tac[mk_inst_def] >>
         disj2_tac >>
         simp[memSafeRunTheory.mem_safe_step_non_invoke,
           GSYM mk_inst_def, instMemFrontierTheory.below_frontier_RETURN,
           eval_operand_def, wordsTheory.w2n_n2w] >>
         qpat_x_assum `b + 32 <= t.vs_alloca_next` mp_tac >>
         simp_tac (srw_ss()) [Abbr `sm`, Abbr `u`, Abbr `sa`, mstore_def,
           LET_THM]) >>
     rewrite_tac[fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     simp[] >> qexistsl_tac [`0`, `ir`] >>
     simp[step_inst_non_invoke, Abbr `ir`, mk_inst_def,
       ptr_safe_defs, gasCountTheory.gas_count_step_def, exit_result_def] >>
     metis_tac[mk_inst_def]) >>
  qexistsl_tac [`ss`, `Gm`, `tm`] >>
  conj_tac
  >- (map_every (fn q => qpat_x_assum q mp_tac)
        [`gas_origin_ptr_edge _ (s,G,tn) [] (OK sa,Ga,ta)`,
         `gas_origin_ptr_edge _ (sa,Ga,ta) [] (OK sm,Gm,tm)`,
         `gas_origin_ptr_edge _ (sm,Gm,tm) [] (Halt ss,Gm,tm)`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
        listTheory.APPEND_NIL, exit_result_def]) >>
  conj_tac
  >- simp_tac (srw_ss()) [Abbr `ss`, halt_state_def, set_returndata_def,
       Abbr `sm`, Abbr `u`, GSYM valueEncodingTheory.mem_bytes_at_def,
       valueEncodingPropsTheory.mem_bytes_at_mstore_same] >>
  simp_tac (srw_ss()) [Abbr `ss`, halt_state_def, set_returndata_def,
    Abbr `sm`, Abbr `u`, Abbr `sa`, mstore_def, LET_THM] >>
  metis_tac[]
QED

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
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accfupds,
                      instruction_accessors, opcode_case_def] >> simp[]) >>
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
