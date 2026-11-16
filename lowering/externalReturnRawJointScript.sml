(* A raw external return keeps one terminal state and ghost pair for every
   dead mask. Only the actual length prefix and payload must be clean. *)
Theory externalReturnRawJoint
Ancestors
  rawReturnHalt rawReturnMem bodyPtrDefs fragGasOriginPtrExec
  fragGasOriginPtr fragGasPathPtr fragGasPathMem ptrSafeRun ptrDiscipline
  loweringHalt compileEnv venomState venomExecSemantics venomInst
  words finite_map contextCodegenRel ptrSafetyTransport
  fragGasSeqPtr fragGasSeqMem emitHelperProps

(* Unlike literal-count return fragments, the actual suffix obtains its
   count from a clean MLOAD. The halt check works for every dead mask. *)
Theorem raw_return_operand_check:
  eval_operand a s = SOME w /\ eval_operand n s = SOME k /\
  op_taint tn a = {} /\ op_taint tn n = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  access_ok lo G fn (mk_inst id RETURN [a;n] []) s /\
  stor_taint_ok_at D tn s /\
  (!i. w2n w <= i /\ i < w2n w + w2n k ==> i NOTIN tn.t_mem) ==>
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id RETURN [a;n] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, memory_range_of_operands_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       halt_state_def, set_returndata_def, ret_taint_def] >>
  gvs[stor_taint_ok_at_def, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >>
  qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem`
    (qspec_then `w2n w + x` mp_tac) >> simp[]
QED

Theorem compile_external_return_raw_joint:
  compile_external_return (SOME (Var src)) prim T ei msz F nkey ut iv st =
    (x, st') /\
  fn_has_code st st' func /\ not_fresh_at st src /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var src) s = SOME p /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  read_memory (w2n (p + 32w)) (LENGTH bs) s = bs /\
  LENGTH bs < dimword (:256) /\
  w2n p + 32 + LENGTH bs <= dimword (:256) /\
  w2n p + 32 + LENGTH bs <= s.vs_alloca_next /\
  ptr_covers G tn src s (32 + LENGTH bs) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==>
       i NOTIN tn.t_mem) ==>
  ?ss G' tn'.
    ss.vs_returndata = bs /\
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
  drule compile_external_return_raw_mem_parts >> simp[] >> strip_tac >>
  `src <> len /\ src <> off` by metis_tac[] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
  simp[] >> rpt strip_tac >>
  qabbrev_tac `i = mk_inst st.cs_next_id MLOAD [Var src] [len]` >>
  qabbrev_tac `j = mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off]` >>
  qabbrev_tac `k = mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] []` >>
  qabbrev_tac `u = update_var len (n2w (LENGTH bs)) s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var off (p + 32w) s1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `ss = halt_state (set_returndata bs s2)` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 j v` >>
  qabbrev_tac `tn2 = step_taint j s1 v tn1` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >> metis_tac[step_MLOAD]) >>
  `eval_operand (Var src) s1 = SOME p` by
    gvs[Abbr `s1`, Abbr `u`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base j s1 = OK v` by
    (simp[Abbr `j`, Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base k s2 = Halt ss` by
    (qspecl_then [`Var off`, `Var len`, `p + 32w`,
                  `n2w (LENGTH bs)`, `st.cs_next_id + 2`, `s2`]
       mp_tac step_RETURN >>
     gvs[Abbr `k`, Abbr `ss`, Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         read_memory_def]) >>
  qexistsl_tac [`ss`, `G2`, `tn2`] >>
  `(!D. stor_taint_ok_at D tn s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Halt ss,G2,tn2))` suffices_by
    (strip_tac >> simp[Abbr `ss`, Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`,
       halt_state_def, set_returndata_def, update_var_def]) >>
  gen_tac >> strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by suspend "load_check" >>
  `ptr_inst_ok D lo 0 ctx func G1 tn1 j s1` by suspend "add_check" >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 k s2` by suspend "return_check" >>
  `gas_path_mem ctx func s 0 (Halt ss)` by suspend "memory_path" >>
  irule gas_zero_paths_joint >> simp[fragExecTheory.exit_result_def] >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0 G1 tn1 (OK s1)` by
    (map_every qunabbrev_tac [`G1`, `tn1`, `s1`, `i`] >>
     irule (straight_line_ptr_edge |> Q.INST
       [`i` |-> `mk_inst st.cs_next_id MLOAD [Var src] [len]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >>
     metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx func PG G1 tn1 s1 0 G2 tn2 (OK s2)` by
    (map_every qunabbrev_tac [`G2`, `tn2`, `s2`, `j`] >>
     irule (straight_line_ptr_edge |> Q.INST
       [`i` |-> `mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >>
     gvs[Abbr `s1`, Abbr `u`, update_var_def,
         arithmeticTheory.ADD1] >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx func PG G2 tn2 s2 0 G2 tn2 (Halt ss)` by
    suspend "return_edge" >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES,
            fragExecTheory.exit_result_def]
QED

Resume compile_external_return_raw_joint[load_check]:
  gvs[ptr_covers_def, eval_operand_def] >>
  simp[ptr_inst_ok_def, Abbr `i`, taint_ok_def, instruction_accessors,
       step_inst_non_invoke] >>
  conj_tac >-
    (simp[access_ok_def, instruction_accessors,
          codegenRelTheory.source_memory_write_ranges_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, memLocDefsTheory.mem_read_ops_def,
          memLocDefsTheory.mem_write_ops_def,
          eval_operand_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                        arithmeticTheory.LESS_EQ_ADD]) >>
  simp[Abbr `u`, update_var_def]
QED

Resume compile_external_return_raw_joint[add_check]:
  simp[ptr_inst_ok_def, Abbr `j`, instruction_accessors,
       access_ok_def, taint_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  conj_tac >-
    (qpat_x_assum `Abbrev (tn2 = _)` kall_tac >>
     gvs[ptr_covers_def] >>
     simp[Abbr `tn1`, Abbr `i`, step_taint_def,
          set_var_taint_def, op_taint_def, FLOOKUP_UPDATE,
          instruction_accessors] >>
     gen_tac >> Cases_on `op = Var src` >- gvs[op_taint_def] >>
     Cases_on `op = Lit 32w` >> simp[op_taint_def]) >>
  simp[Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def, allocas_from_def] >>
  gvs[allocas_from_def]
QED

Resume compile_external_return_raw_joint[return_check]:
  qunabbrev_tac `k` >> irule raw_return_operand_check >>
  simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
  conj_tac >-
    (gvs[eval_operand_def, lookup_var_def] >>
     simp[Abbr `tn2`, Abbr `j`, step_taint_def, set_var_taint_def,
         op_taint_def, instruction_accessors, FLOOKUP_UPDATE, out_taint_def,
         eval_operand_def, lookup_var_def, update_var_def]) >>
  conj_tac >-
    (simp[Abbr `tn2`, Abbr `tn1`, Abbr `j`, Abbr `i`,
          step_taint_def, set_var_taint_def, op_taint_def,
          instruction_accessors, FLOOKUP_UPDATE, out_taint_def,
          eval_operand_def] >>
     gvs[eval_operand_def] >>
     simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
     rpt strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem`
       (qspec_then `w2n p + x` mp_tac) >> simp[] >>
     Cases_on `x < 32` >> simp[]) >>
  conj_tac >-
    (simp[Abbr `tn2`, Abbr `tn1`, Abbr `j`, Abbr `i`,
          step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
          written_taint_def, range_bytes_def, instruction_accessors,
          codegenRelTheory.source_memory_write_ranges_def, update_var_def,
          FLOOKUP_DEF] >>
     Cases_on `LENGTH bs = 0` >- simp[] >>
     `w2n (p + 32w) = w2n p + 32` by
       (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
              wordsTheory.dimword_def] >>
        gvs[wordsTheory.dimword_def] >>
        Cases_on `bs` >> gvs[]) >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem`
       (qspec_then `i` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac >- gvs[allocas_from_def] >>
  conj_tac >-
    gvs[stor_taint_ok_at_def, Abbr `tn2`, Abbr `tn1`, Abbr `j`, Abbr `i`,
        step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
        instruction_accessors] >>
  gvs[ptr_covers_def, eval_operand_def, lookup_var_def] >>
  simp[access_ok_def, instruction_accessors,
       codegenRelTheory.source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, memLocDefsTheory.mem_read_ops_def,
       memLocDefsTheory.mem_write_ops_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `j`, Abbr `i`, step_prov_def,
       out_prov_def, set_prov_def, first_prov_def, op_prov_def,
       instruction_accessors, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `w2n (p + 32w) = w2n p + 32` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          wordsTheory.dimword_def] >>
     gvs[wordsTheory.dimword_def] >> Cases_on `bs` >> gvs[]) >>
  simp[]
QED

Resume compile_external_return_raw_joint[memory_path]:
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    (simp[Abbr `i`, instMemFrontierTheory.below_frontier_MLOAD,
          instruction_accessors] >> gvs[]) >>
  `inst_mem_below_frontier j s1 /\ inst_dload_in_section j s1` by
    (simp[Abbr `j`, instruction_accessors] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >>
     simp[instruction_accessors]) >>
  `gas_path_mem_edge ctx func s 0 (OK s1)` by
    (map_every qunabbrev_tac [`s1`, `i`] >>
     irule (straight_line_mem_edge |> Q.INST
       [`i` |-> `mk_inst st.cs_next_id MLOAD [Var src] [len]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >> metis_tac[]) >>
  `gas_path_mem_edge ctx func s1 0 (OK s2)` by
    (map_every qunabbrev_tac [`s2`, `j`] >>
     irule (straight_line_mem_edge |> Q.INST
       [`i` |-> `mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off]`] |>
       SRULE [instruction_accessors, is_terminator_def]) >>
     gvs[Abbr `s1`, Abbr `u`, update_var_def,
         arithmeticTheory.ADD1] >> metis_tac[]) >>
  `inst_mem_below_frontier k s2 /\ inst_dload_in_section k s2` by
    (simp[Abbr `k`, instruction_accessors,
          instMemFrontierTheory.below_frontier_RETURN,
          Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def,
          eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     Cases_on `bs = []` >- simp[] >>
     `w2n (p + 32w) = w2n p + 32` by
       (simp[word_add_def, w2n_n2w, dimword_def] >>
        gvs[dimword_def] >> Cases_on `bs` >> gvs[]) >> simp[]) >>
  `gas_path_mem_edge ctx func s2 0 (Halt ss)` by
    (rewrite_tac[gas_path_mem_edge_def] >>
     conj_tac >-
       simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def] >>
     qexistsl_tac [`0`, `bb`, `k`, `Halt ss`] >>
     simp[gasCountTheory.gas_count_step_def, memSafeRunTheory.mem_safe_step_non_invoke,
          step_inst_non_invoke, fragExecTheory.exit_result_def,
          Abbr `k`, instruction_accessors] >>
     gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def,
         arithmeticTheory.ADD1]) >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES,
            fragExecTheory.exit_result_def]
QED

Resume compile_external_return_raw_joint[return_edge]:
  rewrite_tac[gas_path_ptr_edge_def] >>
  conj_tac >-
    simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def] >>
  qexistsl_tac [`0`, `bb`, `k`] >>
  simp[gasCountTheory.gas_count_step_def, ptr_safe_step_def, step_inst_non_invoke,
       fragExecTheory.exit_result_def, Abbr `k`, instruction_accessors] >>
  gvs[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def,
      arithmeticTheory.ADD1]
QED

Finalise compile_external_return_raw_joint
