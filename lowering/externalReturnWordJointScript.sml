Theory externalReturnWordJoint
Ancestors
  externalReturnRawJoint allocaSiteResource ptrSafetyTransport
  bodyFullAllocGeneric wordLoadStorePtr instMemFrontier
  fragGasEmitCtrl bodyPtrPrecompileBuiltinsAllocationFrame
  loweringHalt bodyPtrDefs fragGasOriginPtrExec fragGasOriginPtr
  fragGasPathPtr fragGasPathMem fragGasSeqPtr fragGasSeqMem
  ptrSafeRun ptrDiscipline compileEnv venomState venomExecSemantics
  venomMemDefs venomMemProofs venomInst words finite_map contextCodegenRel
  emitHelperProps emitHelper valueEncodingProps valueEncodingDefs

Theorem compile_external_return_word_joint:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st =
    (x,st') /\
  fn_has_code st st' func /\ (!y. op = Var y ==> not_fresh_at st y) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  alloca_inv s /\ alloca_room ctx func s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) ==>
  ?ss G' tn'.
    ss.vs_returndata = word_to_bytes w T /\
    ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient = s.vs_transient /\
    ss.vs_immutables = s.vs_immutables /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions /\
    !D. stor_taint_ok_at D tn s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Halt ss,G',tn')
Proof
  strip_tac >>
  `w2n (32w:bytes32) = 32 /\ 32 < dimword (:256)` by
    simp_tac (srw_ss()) [w2n_n2w, dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule compile_external_return_word_parts >> simp[] >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    map_every (fn k => mp_tac (Q.SPEC k th)) [`0`, `1`, `2`]) >>
  simp[] >> rpt strip_tac >>
  qabbrev_tac `i = mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]` >>
  qabbrev_tac `j = mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []` >>
  qabbrev_tac `k = mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []` >>
  `MEM i (fn_insts func)` by
    (irule fragExecTheory.lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[Abbr `i`, get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  `?u b. exec_alloca i s (32w:bytes32) = OK u /\
    alloca_room ctx func u /\ alloca_inv u /\
    lookup_var buf u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ b + 32 <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory` by suspend "allocation" >>
  qpat_x_assum `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> _`
    kall_tac >>
  `step_inst_base i s = OK u` by
    (qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
     qunabbrev_tac `i` >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = mstore b w s1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `ss = halt_state (set_returndata (word_to_bytes w T) s2)` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 j v` >>
  qabbrev_tac `tn2 = step_taint j s1 v tn1` >>
  `allocas_from lo s1 /\ lo <= s1.vs_alloca_next /\
   ~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb /\
   b < dimword (:256) /\
   lookup_var buf s1 = SOME (n2w b) /\
   eval_operand op s1 = SOME w /\
   ptr_covers G1 tn1 buf s1 32 /\ op_taint tn1 op = {}` by
    suspend "allocation_resources" >>
  `b MOD dimword (:256) = b` by
    (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac[]) >>
  `step_inst_base j s1 = OK v` by suspend "store" >>
  `step_inst_base k s2 = Halt ss` by suspend "halt" >>
  qexistsl_tac [`ss`, `G2`, `tn2`] >>
  `(!D. stor_taint_ok_at D tn s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Halt ss,G2,tn2))` suffices_by suspend "world" >>
  gen_tac >> strip_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK s1,G1,tn1)` by suspend "allocation_edge" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (s1,G1,tn1) [] (OK s2,G2,tn2)` by suspend "store_edge" >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s2,G2,tn2) [] (Halt ss,G2,tn2)` by suspend "return_path" >>
  metis_tac[gas_origin_ptr_path_rules, listTheory.APPEND,
            fragExecTheory.exit_result_def]
QED

Resume compile_external_return_word_joint[allocation]:
  `i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w] /\
   i.inst_outputs = [buf] /\ i.inst_id = st.cs_next_id` by
    simp_tac (srw_ss()) [Abbr `i`, mk_inst_def, instruction_accessors] >>
  `(!b sz. FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = 32)` by asm_rewrite_tac[] >>
  drule_all alloca_site32_execute >> strip_tac >>
  qexistsl_tac [`t`,`b`] >> asm_rewrite_tac[] >>
  qpat_x_assum `FLOOKUP t.vs_allocas _ = SOME _` mp_tac >> asm_rewrite_tac[]
QED

Resume compile_external_return_word_joint[allocation_resources]:
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  `b < dimword (:256)` by
    (fs[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `allocas_from lo u` by
    (irule (cj 1 step_inst_allocas_from) >>
     qexistsl_tac [`ctx`,`0`,`i`,`s`] >>
     simp[step_inst_non_invoke, Abbr `i`, mk_inst_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   eval_operand op u = SOME w` by
    (qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
     simp_tac (srw_ss()) [Abbr `i`, exec_alloca_def, mk_inst_def,
       AllCaseEqs(), update_var_def, LET_THM] >>
     rpt strip_tac >>
     qpat_x_assum `_ = u`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
                 PURE_REWRITE_TAC [GSYM th]) >>
     Cases_on `op` >>
     fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qpat_assum `allocas_from lo u`
    (assume_tac o REWRITE_RULE [allocas_from_def]) >>
  qpat_assum `lookup_var buf u = SOME _`
    (assume_tac o REWRITE_RULE [lookup_var_def]) >>
  simp[Abbr `s1`, allocas_from_def] >>
  simp[ptr_covers_def, Abbr `G1`, Abbr `tn1`,
    step_prov_def, out_prov_def, set_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, Abbr `i`, mk_inst_def,
    op_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  Cases_on `op` >>
  asm_simp_tac (srw_ss()) [op_taint_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[allocas_from_def, op_taint_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_external_return_word_joint[store]:
  qspecl_then [`Var buf`,`op`,`(n2w b:bytes32)`,`w`,
                `st.cs_next_id + 1`,`s1`] mp_tac step_MSTORE >>
  impl_tac >- simp[eval_operand_def] >>
  simp[Abbr `j`, Abbr `v`, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Resume compile_external_return_word_joint[halt]:
  `w2n (32w:bytes32) = 32` by
    simp_tac (srw_ss()) [w2n_n2w, dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `eval_operand (Var buf) s2 = SOME (n2w b)` by
    fs[Abbr `s2`, Abbr `v`, mstore_def,
         write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  `read_memory b 32 s2 = word_to_bytes w T` by
    simp[Abbr `s2`, Abbr `v`, read_memory_def,
         GSYM mem_bytes_at_def, mem_bytes_at_mstore_same] >>
  qspecl_then [`Var buf`,`Lit 32w`,`(n2w b:bytes32)`,`(32w:bytes32)`,
                `st.cs_next_id+2`,`s2`] mp_tac step_RETURN >>
  impl_tac >- simp[eval_operand_def] >>
  fs[Abbr `k`, Abbr `ss`, read_memory_def, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Resume compile_external_return_word_joint[world]:
  disch_tac >> simp[Abbr `ss`, Abbr `s2`, Abbr `v`, Abbr `s1`,
    halt_state_def, set_returndata_def, mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
  simp_tac (srw_ss()) [Abbr `i`, exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def, LET_THM] >> rpt strip_tac >> gvs[]
QED

Resume compile_external_return_word_joint[allocation_edge]:
  map_every qunabbrev_tac [`G1`,`tn1`,`s1`,`i`] >>
  irule bodyFullAllocGenericTheory.ifexp_alloca_origin_ptr_edge >> simp[]
QED

Resume compile_external_return_word_joint[store_edge]:
  `ptr_inst_ok D lo 0 ctx func G1 tn1 j s1` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[] >> simp[Abbr `j`] >>
     irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[]) >>
  `inst_mem_below_frontier j s1 /\ inst_dload_in_section j s1` by
    (simp[Abbr `j`, instruction_accessors,
          instMemFrontierTheory.below_frontier_MSTORE,
          eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
     gvs[Abbr `s1`]) >>
  map_every qunabbrev_tac [`G2`,`tn2`,`s2`,`j`] >>
  irule (straight_line_origin_ptr_edge |> Q.INST
    [`i` |-> `mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []`] |>
    SRULE [instruction_accessors, is_terminator_def]) >>
  gvs[Abbr `s1`, arithmeticTheory.ADD1] >> metis_tac[]
QED

Resume compile_external_return_word_joint[return_path]:
  `ptr_covers G2 tn2 buf s2 32 /\
   op_taint tn2 (Var buf) = {} /\
   lookup_var buf s2 = SOME (n2w b) /\
   allocas_from lo s2 /\
   (!a. b <= a /\ a < b + 32 ==> a NOTIN tn2.t_mem) /\
   stor_taint_ok_at D tn2 s2` by suspend "stored_resources" >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 k s2` by
    (simp[Abbr `k`] >> irule raw_return_operand_check >>
     simp[eval_operand_def, op_taint_def] >>
     fs[ptr_covers_def, access_ok_def, mk_inst_def,
        source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
        memory_range_of_operands_def, memLocDefsTheory.mem_read_ops_def,
        memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
     rpt strip_tac >>
     qpat_assum `b < dimword (:256)`
       (fn th => RULE_ASSUM_TAC
         (PURE_REWRITE_RULE [MATCH_MP arithmeticTheory.LESS_MOD th])) >>
     decide_tac) >>
  `inst_mem_below_frontier k s2 /\ inst_dload_in_section k s2` by
    (simp[Abbr `k`, instruction_accessors,
          instMemFrontierTheory.below_frontier_RETURN,
          eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
     gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, mstore_def,
         write_memory_with_expansion_def]) >>
  `k.inst_opcode = RETURN` by simp[Abbr `k`, mk_inst_def] >>
  `!fuel. step_inst fuel ctx k s2 = Halt ss` by
    asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  `mem_safe_step 0 ctx k s2` by
    asm_simp_tac (srw_ss()) [memSafeRunTheory.mem_safe_step_non_invoke] >>
  irule (Q.INST [`bb` |-> `bb`, `i` |-> `k`] exit_inst_origin_ptr) >>
  asm_simp_tac (srw_ss()) [gasEventsTheory.gas_events_step_def,
    gasCountTheory.gas_count_step_def, fragExecTheory.exit_result_def] >>
  gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, mstore_def,
      write_memory_with_expansion_def, arithmeticTheory.ADD1]
QED

Resume compile_external_return_word_joint[stored_resources]:
  `G2 = G1 /\ tn2.t_var = tn1.t_var /\
   tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
   tn2.t_mem = tn1.t_mem DIFF {a | b <= a /\ a < b+32}` by
    (qspecl_then [`PG`,`G1`,`tn1`,`s1`,`st.cs_next_id+1`,
                   `buf`,`op`,`(n2w b:bytes32)`,`w`] mp_tac mstore_ghost_frame >>
     impl_tac >- simp[] >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `j`, Abbr `v`, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `tn2.t_imm = tn1.t_imm` by
    simp[Abbr `tn2`, Abbr `j`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `stor_taint_ok_at D tn1 s1` by
    (simp[stor_taint_ok_at_def, Abbr `tn1`, Abbr `i`,
          alloca_ghost_frames, Abbr `s1`] >>
     qpat_x_assum `exec_alloca _ s _ = OK u` mp_tac >>
     simp_tac (srw_ss()) [exec_alloca_def, mk_inst_def,
       AllCaseEqs(), update_var_def, LET_THM] >>
     rpt strip_tac >> gvs[stor_taint_ok_at_def]) >>
  `allocas_from lo s2 /\ lookup_var buf s2 = SOME (n2w b)` by
    (fs[Abbr `s2`, Abbr `v`, mstore_def, write_memory_with_expansion_def,
        allocas_from_def, lookup_var_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (fs[ptr_covers_def, op_taint_def, Abbr `s2`, Abbr `v`,
         mstore_def, write_memory_with_expansion_def, lookup_var_def]) >>
  conj_tac
  >- (fs[ptr_covers_def, op_taint_def]) >>
  conj_tac >- simp[pred_setTheory.IN_DIFF] >>
  fs[stor_taint_ok_at_def, Abbr `s2`, Abbr `v`, mstore_def,
     write_memory_with_expansion_def]
QED

Finalise compile_external_return_word_joint
