(* The static ABI-copy suffix fixes its terminal state and ghosts before
   every dead mask. Empty returns require no source allocation witness. *)
Theory externalReturnCopyJoint
Ancestors
  externalReturnRawJoint allocaSiteResource ptrSafetyTransport
  loweringHalt bodyPtrDefs fragGasOriginPtrExec fragGasOriginPtr
  fragGasPathPtr fragGasPathMem fragGasSeqPtr fragGasSeqMem
  ptrSafeRun ptrDiscipline compileEnv venomState venomExecSemantics
  venomMemDefs venomInst words finite_map contextCodegenRel emitHelperProps

Theorem compile_external_return_copy_joint:
  compile_external_return (SOME op) F F (AbiCopy m) n F nkey ut iv st =
    (x,st') /\
  fn_has_code st st' func /\ (!y. op = Var y ==> not_fresh_at st y) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  alloca_inv s /\ alloca_room ctx func s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME p /\ op_taint tn op = {} /\
  m <= n /\ n < dimword (:256) /\
  (0 < m ==> w2n p + m <= s.vs_alloca_next) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = n) /\
  (0 < m ==> ?src. op = Var src /\ ptr_covers G tn src s m) /\
  (!i. w2n p <= i /\ i < w2n p + m ==> i NOTIN tn.t_mem) ==>
  ?ss G' tn'.
    ss.vs_returndata = read_memory (w2n p) m s /\
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
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    map_every (fn k => mp_tac (Q.SPEC k th)) [`0`, `1`, `2`]) >>
  simp[] >> rpt strip_tac >>
  qabbrev_tac `i = mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]` >>
  qabbrev_tac `j = mk_inst (st.cs_next_id + 1) MCOPY [Var buf; op; Lit (n2w m)] []` >>
  qabbrev_tac `k = mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit (n2w m)] []` >>
  `MEM i (fn_insts func)` by
    (irule fragExecTheory.lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[Abbr `i`, get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  `?u b. exec_alloca i s (n2w n : bytes32) = OK u /\
    alloca_room ctx func u /\ alloca_inv u /\
    lookup_var buf u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,n) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ b + n <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory` by
    (`i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit (n2w n)] /\
      i.inst_outputs = [buf] /\
      (!b sz. FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
        sz = w2n (n2w n : bytes32))` by
       simp[Abbr `i`, instruction_accessors, mk_inst_def, w2n_n2w] >>
     drule_all alloca_site_execute >> strip_tac >>
     qexistsl_tac [`t`, `b`] >>
     `i.inst_id = st.cs_next_id` by simp[Abbr `i`, mk_inst_def] >>
     `w2n (n2w n : bytes32) = n` by simp[w2n_n2w] >>
     qpat_x_assum `w2n (n2w n : bytes32) = n`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     qpat_x_assum `i.inst_id = st.cs_next_id`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> _`
    kall_tac >>
  `step_inst_base i s = OK u` by
    (qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
     qunabbrev_tac `i` >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp_tac (srw_ss()) [mk_inst_def]) >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = mcopy (w2n (n2w b : bytes32)) (w2n p) m s1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `ss = halt_state (set_returndata (read_memory (w2n p) m s) s2)` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 j v` >>
  qabbrev_tac `tn2 = step_taint j s1 v tn1` >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_alloca_next = u.vs_alloca_next` by suspend "alloca_fields" >>
  `ptr_covers G1 tn1 buf s1 n /\ op_taint tn1 op = {}` by
    suspend "alloca_ghost" >>
  `(0 < m ==> ?src. op = Var src /\ ptr_covers G1 tn1 src s1 m)` by
    suspend "source_ghost" >>
  `(!a. w2n p <= a /\ a < w2n p + m ==> a NOTIN tn1.t_mem)` by
    suspend "source_clean" >>
  `eval_operand op s1 = SOME p` by suspend "source" >>
  `step_inst_base j s1 = OK v` by suspend "copy" >>
  `step_inst_base k s2 = Halt ss` by suspend "halt" >>
  qexistsl_tac [`ss`, `G2`, `tn2`] >>
  `(!D. stor_taint_ok_at D tn s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Halt ss,G2,tn2))` suffices_by suspend "world" >>
  gen_tac >> strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by suspend "alloca_check" >>
  `ptr_inst_ok D lo 0 ctx func G1 tn1 j s1` by suspend "copy_check" >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 k s2` by suspend "return_check" >>
  `gas_path_mem ctx func s 0 (Halt ss)` by suspend "memory_path" >>
  irule gas_zero_paths_joint >> simp[fragExecTheory.exit_result_def] >>
  suspend "pointer_path"
QED

Resume compile_external_return_copy_joint[alloca_fields]:
  qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
  simp_tac (srw_ss()) [Abbr `i`, Abbr `s1`, exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[allocas_from_def]
QED
Resume compile_external_return_copy_joint[alloca_ghost]:
  `b < dimword (:256)` by
    (fs[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  simp[ptr_covers_def, Abbr `G1`, Abbr `tn1`, Abbr `s1`,
    step_prov_def, out_prov_def, set_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, Abbr `i`, mk_inst_def,
    op_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w] >>
  Cases_on `op` >> gvs[op_taint_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w]
QED
Resume compile_external_return_copy_joint[source_ghost]:
  strip_tac >>
  qpat_x_assum `0 < m ==> ?src. _` drule >> strip_tac >>
  qexists_tac `src` >> simp[] >>
  qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
  simp_tac (srw_ss()) [Abbr `i`, exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[ptr_covers_def, Abbr `G1`, Abbr `tn1`, Abbr `s1`,
    step_prov_def, out_prov_def, set_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, mk_inst_def, op_taint_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED
Resume compile_external_return_copy_joint[source_clean]:
  Cases_on `m = 0` >- simp[] >>
  `w2n p + m <= s.vs_alloca_next` by simp[] >>
  qunabbrev_tac `tn1` >> qunabbrev_tac `i` >>
  qpat_x_assum `exec_alloca _ s _ = OK u` mp_tac >>
  qpat_x_assum `!i. w2n p <= i /\ i < _ ==> _` mp_tac >>
  qpat_x_assum `w2n p + m <= s.vs_alloca_next` mp_tac >>
  qpat_x_assum `n < dimword (:256)` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[exec_alloca_def, mk_inst_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    range_bytes_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
    written_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[step_taint_def, mem_taint_def, new_site_bytes_def,
    range_bytes_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
    written_taint_def, AllCaseEqs(), FLOOKUP_UPDATE, FLOOKUP_DEF] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
Resume compile_external_return_copy_joint[source]:
  qpat_x_assum `exec_alloca i s _ = OK u` mp_tac >>
  simp_tac (srw_ss()) [Abbr `i`, Abbr `s1`, exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED
Resume compile_external_return_copy_joint[copy]:
  `m < dimword (:256)` by decide_tac >>
  qunabbrev_tac `j` >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  fs[Abbr `v`, Abbr `s1`, eval_operand_def, lookup_var_def, w2n_n2w]
QED
Resume compile_external_return_copy_joint[halt]:
  `m < dimword (:256)` by decide_tac >>
  `eval_operand (Var buf) s2 = SOME (n2w b)` by
    fs[Abbr `s2`, Abbr `v`, Abbr `s1`, eval_operand_def, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def] >>
  `read_memory (w2n (n2w b : bytes32)) m s2 = read_memory (w2n p) m s` by
    (`read_memory (w2n (n2w b : bytes32)) m s2 =
       read_memory (w2n (n2w b : bytes32)) m v` by
       simp[Abbr `s2`, read_memory_def] >>
     simp[Abbr `v`, memoryReadPropsTheory.read_memory_mcopy_self] >>
     simp[Abbr `s1`, read_memory_def]) >>
  qunabbrev_tac `k` >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  fs[Abbr `ss`, eval_operand_def, w2n_n2w, read_memory_def]
QED
Resume compile_external_return_copy_joint[world]:
  strip_tac >>
  map_every qunabbrev_tac [`ss`, `s2`, `v`, `s1`, `i`] >>
  qpat_x_assum `exec_alloca _ s _ = OK u` mp_tac >>
  qpat_x_assum `!D. _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac (srw_ss()) [exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  simp[halt_state_def, set_returndata_def, mcopy_def,
       write_memory_with_expansion_def]
QED
Resume compile_external_return_copy_joint[alloca_check]:
  simp[ptr_inst_ok_def, Abbr `i`, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, op_taint_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp_tac (srw_ss()) [instruction_accessors, opcode_case_def,
       exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[stor_taint_ok_at_def]
QED
Resume compile_external_return_copy_joint[copy_check]:
  `lookup_var buf s1 = SOME (n2w b)` by fs[Abbr `s1`, lookup_var_def] >>
  simp[ptr_inst_ok_def, Abbr `j`, taint_ok_def, mk_inst_def,
       step_inst_non_invoke] >>
  reverse conj_tac >-
    (simp[Abbr `v`, mcopy_def, write_memory_with_expansion_def] >>
     gvs[ptr_covers_def] >> gen_tac >>
     Cases_on `op' = Var buf` >- simp[] >>
     Cases_on `op' = op` >- simp[] >>
     Cases_on `op' = Lit (n2w m)` >> simp[op_taint_def]) >>
  (Cases_on `m = 0`
     >- simp[access_ok_def, source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memory_range_of_operands_def, codegenRelTheory.sized_source_write_range_def,
          eval_operand_def] >>
     `?src. op = Var src /\ ptr_covers G1 tn1 src s1 m` by simp[] >>
     gvs[ptr_covers_def] >>
     simp[access_ok_def, source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memory_range_of_operands_def, codegenRelTheory.sized_source_write_range_def,
          memLocDefsTheory.mem_read_ops_def,
          memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_n2w] >>
     gvs[eval_operand_def] >> rpt strip_tac >> decide_tac)
QED
Resume compile_external_return_copy_joint[return_check]:
  `m < dimword (:256)` by decide_tac >>
  `lookup_var buf s1 = SOME (n2w b)` by fs[Abbr `s1`, lookup_var_def] >>
  `lookup_var buf s2 = SOME (n2w b)` by
    fs[Abbr `s2`, Abbr `v`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  qunabbrev_tac `k` >> irule raw_return_operand_check >>
  simp[eval_operand_def, op_taint_def, w2n_n2w] >>
  conj_tac >-
    (fs[ptr_covers_def] >>
     simp[Abbr `tn2`, Abbr `j`, step_taint_def, set_var_taint_def,
          mk_inst_def, FLOOKUP_DRESTRICT, op_taint_def] >> gvs[op_taint_def]) >>
  conj_tac >-
    (rpt strip_tac >>
     qunabbrev_tac `tn2` >> qunabbrev_tac `j` >>
     gvs[step_taint_def, mem_taint_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def, mk_inst_def,
       range_bytes_def, eval_operand_def, w2n_n2w] >>
     qpat_x_assum `!a. _ ==> a NOTIN tn1.t_mem` irule >> decide_tac) >>
  conj_tac >-
    (fs[Abbr `s2`, Abbr `v`, mcopy_def, write_memory_with_expansion_def,
        allocas_from_def] >> metis_tac[]) >>
  conj_tac >- suspend "storage" >>
  gvs[ptr_covers_def] >>
  simp[access_ok_def, mk_inst_def, source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memory_range_of_operands_def, memLocDefsTheory.mem_read_ops_def,
       memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_n2w,
       Abbr `G2`, Abbr `j`, step_prov_def, set_prov_def,
       FLOOKUP_DRESTRICT] >> rpt strip_tac >> decide_tac
QED
Resume compile_external_return_copy_joint[storage]:
  simp[stor_taint_ok_at_def, Abbr `tn2`, Abbr `j`, Abbr `tn1`, Abbr `i`,
       step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       mk_inst_def, Abbr `s2`, Abbr `v`, Abbr `s1`,
       mcopy_def, write_memory_with_expansion_def] >>
  qpat_x_assum `exec_alloca _ s _ = OK u` mp_tac >>
  simp_tac (srw_ss()) [exec_alloca_def, mk_inst_def,
    AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[stor_taint_ok_at_def]
QED
Resume compile_external_return_copy_joint[memory_path]:
  `b < dimword (:256)` by
    (fs[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `m < dimword (:256)` by decide_tac >>
  `lookup_var buf s1 = SOME (n2w b)` by fs[Abbr `s1`, lookup_var_def] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    (simp[Abbr `i`, instruction_accessors] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >>
     simp[instruction_accessors]) >>
  `inst_mem_below_frontier j s1 /\ inst_dload_in_section j s1` by
    (simp[Abbr `j`, instruction_accessors,
          instMemFrontierTheory.below_frontier_MCOPY,
          eval_operand_def, w2n_n2w] >>
     gvs[eval_operand_def] >> Cases_on `m = 0` >> gvs[] >> decide_tac) >>
  `inst_mem_below_frontier k s2 /\ inst_dload_in_section k s2` by
    (simp[Abbr `k`, instruction_accessors,
          instMemFrontierTheory.below_frontier_RETURN,
          Abbr `s2`, Abbr `v`, mcopy_def, write_memory_with_expansion_def,
          eval_operand_def, lookup_var_def, w2n_n2w] >>
     gvs[lookup_var_def] >> decide_tac) >>
  `gas_path_mem_edge ctx func s 0 (OK s1)` by
    (map_every qunabbrev_tac [`s1`, `i`] >>
     irule (straight_line_mem_edge |> Q.INST
       [`i` |-> `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >> metis_tac[]) >>
  `gas_path_mem_edge ctx func s1 0 (OK s2)` by
    (map_every qunabbrev_tac [`s2`, `j`] >>
     irule (straight_line_mem_edge |> Q.INST
       [`i` |-> `mk_inst (st.cs_next_id + 1) MCOPY [Var buf; op; Lit (n2w m)] []`] |>
       SRULE [instruction_accessors, is_terminator_def]) >>
     gvs[Abbr `s1`, arithmeticTheory.ADD1] >> metis_tac[]) >>
  `gas_path_mem_edge ctx func s2 0 (Halt ss)` by
    (rewrite_tac[gas_path_mem_edge_def] >>
     conj_tac >-
       simp[Abbr `s2`, Abbr `v`, mcopy_def, write_memory_with_expansion_def] >>
     qexistsl_tac [`0`, `bb`, `k`, `Halt ss`] >>
     simp[gasCountTheory.gas_count_step_def, memSafeRunTheory.mem_safe_step_non_invoke,
          step_inst_non_invoke, fragExecTheory.exit_result_def,
          Abbr `k`, instruction_accessors] >>
     gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, mcopy_def,
         write_memory_with_expansion_def, arithmeticTheory.ADD1]) >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES,
            fragExecTheory.exit_result_def]
QED
Resume compile_external_return_copy_joint[pointer_path]:
  `gas_path_ptr_edge D lo ctx func PG G tn s 0 G1 tn1 (OK s1)` by
    (map_every qunabbrev_tac [`G1`, `tn1`, `s1`, `i`] >>
     irule (straight_line_ptr_edge |> Q.INST
       [`i` |-> `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx func PG G1 tn1 s1 0 G2 tn2 (OK s2)` by
    (map_every qunabbrev_tac [`G2`, `tn2`, `s2`, `j`] >>
     irule (straight_line_ptr_edge |> Q.INST
       [`i` |-> `mk_inst (st.cs_next_id + 1) MCOPY [Var buf; op; Lit (n2w m)] []`] |>
       SRULE [instruction_accessors, is_terminator_def]) >>
     gvs[Abbr `s1`, arithmeticTheory.ADD1] >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx func PG G2 tn2 s2 0 G2 tn2 (Halt ss)` by
    (rewrite_tac[gas_path_ptr_edge_def] >>
     conj_tac >- simp[Abbr `s2`, Abbr `v`, mcopy_def, write_memory_with_expansion_def] >>
     qexistsl_tac [`0`, `bb`, `k`] >>
     simp[gasCountTheory.gas_count_step_def, ptr_safe_step_def, step_inst_non_invoke,
          fragExecTheory.exit_result_def, Abbr `k`, instruction_accessors] >>
     gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, mcopy_def,
         write_memory_with_expansion_def, arithmeticTheory.ADD1]) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES,
            fragExecTheory.exit_result_def]
QED

Finalise compile_external_return_copy_joint
