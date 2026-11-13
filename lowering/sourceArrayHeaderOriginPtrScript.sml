Theory sourceArrayHeaderOriginPtr
Ancestors decoderLoopHeaderCorePtr fragGasSeqPtr fragGasSeqMem fragGasOriginPtr
  sourceArrayHeaderGasMem instMemFrontier fragGasPathMem fragGasOrigin
  instIdxIndep ghostPcTransportPtr typedCopyArrayPtr fragGasPathPtr
  compileEnv loweringStateRelDefs abiDecoderContract memLocDefs bodyPtrDefs
  decoderGhostFramePtr decoderProtectedScratchPtr typedCopyPtr abiDecoderExecution abiDecoderFrame
  entryDispatchPtr ptrSafeRun ptrDiscipline codegenRel emitHelperProps contextCodegenRel
  exprLoweringProps venomExecSemantics venomExecProofs venomInstProofs venomState venomInst finite_map pred_set words list arithmetic

Theorem header_forward_step[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_safe_step D lo 0 ctx fn PG G tn i s /\ step_inst_base i s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u, step_taint i s u tn)
Proof
  strip_tac >>
  `~u.vs_halted` by metis_tac[step_preserves_halted, step_inst_non_invoke] >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G i u) (step_taint i s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (`gas_path_ptr_edge D lo ctx fn PG G tn s
       (if i.inst_opcode = GAS then 1 else 0)
       (step_prov PG G i u) (step_taint i s u tn)
       (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     irule straight_line_ptr_edge >> gvs[ptr_safe_step_def]) >>
  `gas_path_mem_edge ctx fn s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (`gas_path_mem_edge ctx fn s (if i.inst_opcode = GAS then 1 else 0)
       (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     irule straight_line_mem_edge >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u, step_taint i s u tn)` by
    (simp[gas_origin_ptr_edge_def] >> metis_tac[gas_path_mem_edge_zero_origin]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem header_joint_then[local]:
  gas_origin_ptr_path cx a [] (OK b,G,tn) /\
  gas_origin_ptr_path cx (b,G,tn) [] (r,H,u) ==>
  gas_origin_ptr_path cx a [] (r,H,u)
Proof
  strip_tac >> qpat_x_assum `gas_origin_ptr_path cx a _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`b`,`G`,`tn`,`[]`,`r`,`H`,`u`] mp_tac) >> simp[]
QED

Theorem header_jnz_joint[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [op;Label yes;Label no] []) /\
  ~s.vs_halted /\ eval_operand op s = SOME v /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to (if v <> 0w then yes else no) s),G,tn)
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id JNZ [op;Label yes;Label no] []` >>
  qabbrev_tac `t = jump_to (if v <> 0w then yes else no) s` >>
  `step_inst_base i s = OK t` by
    (Cases_on `v = 0w` >> simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs, mk_inst_def]) >>
  `ptr_safe_step D lo 0 ctx fn PG G tn i s` by
    (simp[Abbr `i`, ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       jump_to_def, op_taint_def] >>
     (conj_tac >- (gen_tac >> Cases_on `op' = op` >>
       Cases_on `op' = Label yes` >> Cases_on `op' = Label no` >> gvs[op_taint_def])) >>
     Cases_on `v = 0w` >> simp[jump_to_def] >>
     gvs[Abbr `t`, jump_to_def, allocas_from_def, allocas_below_fmp_def]) >>
  `gas_path_mem_edge ctx fn s 0 (OK t)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[Abbr `i`, gasCountTheory.gas_count_step_def,
       step_inst_non_invoke, memSafeRunTheory.mem_safe_step_non_invoke,
       below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other,
       mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn (OK t)` by
    (simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
     simp[Abbr `i`, gasCountTheory.gas_count_step_def,
       step_inst_non_invoke, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G,tn)` by
    (simp[gas_origin_ptr_edge_def] >> metis_tac[gas_path_mem_edge_zero_origin]) >>
  `~t.vs_halted` by simp[Abbr `t`, jump_to_def] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem source_array_header_origin_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts id (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\ src <> Var iv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\ slot + 32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  eval_operand src s = SOME srcaddr /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w ncount /\
  j <= ncount /\ ncount < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?H u t.
    t = jump_to (if j < ncount then body_lbl else exit_lbl)
          (abi_decode_header_state iv cv cmp done j ncount s) /\
    t.vs_allocas = s.vs_allocas /\
    t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_fmp = s.vs_fmp /\
    ptr_covers H u q t 32 /\ mload slot t = n2w j /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!x. MEM x [iv;cv;cmp;done] ==>
       op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qabbrev_tac `a = update_var iv (n2w j) s` >>
  qabbrev_tac `b = update_var cv (n2w ncount) a` >>
  qabbrev_tac `c = update_var cmp (bool_to_word (j < ncount)) b` >>
  qabbrev_tac `d = update_var done (bool_to_word (~(j < ncount))) c` >>
  qabbrev_tac `i0 = mk_inst id MLOAD [Var q] [iv]` >>
  qabbrev_tac `i1 = mk_inst (id+1) CALLDATALOAD [src] [cv]` >>
  qabbrev_tac `i2 = mk_inst (id+2) LT [Var iv;Var cv] [cmp]` >>
  qabbrev_tac `i3 = mk_inst (id+3) ISZERO [Var cmp] [done]` >>
  qabbrev_tac `H1 = step_prov PG G i0 a` >>
  qabbrev_tac `u1 = step_taint i0 s a tn` >>
  qabbrev_tac `H2 = step_prov PG H1 i1 b` >>
  qabbrev_tac `u2 = step_taint i1 a b u1` >>
  qabbrev_tac `H3 = step_prov PG H2 i2 c` >>
  qabbrev_tac `u3 = step_taint i2 b c u2` >>
  qabbrev_tac `H4 = step_prov PG H3 i3 d` >>
  qabbrev_tac `u4 = step_taint i3 c d u3` >>
  `abi_decode_header_state iv cv cmp done j ncount s = d` by
    simp[abi_decode_header_state_def, Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`] >>
  `mem_word_taint tn.t_mem slot = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
     Cases_on `x < 32` >> simp[] >>
     `slot <= slot + x /\ slot + x < slot + 32` by decide_tac >>
     qpat_x_assum `DISJOINT _ _` mp_tac >>
     simp[DISJOINT_DEF, EXTENSION] >>
     disch_then (qspec_then `slot + x` mp_tac) >> simp[]) >>
  `H1 = DRESTRICT G (COMPL {iv}) /\ H2 = DRESTRICT H1 (COMPL {cv}) /\
   H3 = DRESTRICT H2 (COMPL {cmp}) /\ H4 = DRESTRICT H3 (COMPL {done})` by
    simp[Abbr `H1`, Abbr `H2`, Abbr `H3`, Abbr `H4`,
      Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, step_prov_def,
      set_prov_def, out_prov_def, mk_inst_def] >>
  `u1.t_var = tn.t_var |+ (iv,{})` by
    simp[Abbr `u1`, Abbr `i0`, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def, w2n_n2w] >>
  `u2.t_var = u1.t_var |+ (cv,{})` by
    (Cases_on `eval_operand src a` >>
     simp[Abbr `u2`, Abbr `i1`, step_taint_def,
       set_var_taint_def, out_taint_def, mk_inst_def]) >>
  `u3.t_var = u2.t_var |+ (cmp,{})` by
    (Cases_on `eval_operand (Var iv) b` >>
     simp[Abbr `u3`, Abbr `i2`, step_taint_def,
       set_var_taint_def, out_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_UPDATE, ALL_DISTINCT]) >>
  `u4.t_var = u3.t_var |+ (done,{})` by
    (Cases_on `eval_operand (Var cmp) c` >>
     simp[Abbr `u4`, Abbr `i3`, step_taint_def,
       set_var_taint_def, out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `u1.t_mem = tn.t_mem /\ u1.t_stor = tn.t_stor /\ u1.t_trans = tn.t_trans /\
   u1.t_imm = tn.t_imm` by
    (simp[Abbr `u1`, Abbr `i0`, step_taint_def, mem_taint_def, imm_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u2.t_mem = u1.t_mem /\ u2.t_stor = u1.t_stor /\ u2.t_trans = u1.t_trans /\
   u2.t_imm = u1.t_imm` by
    (simp[Abbr `u2`, Abbr `i1`, step_taint_def, mem_taint_def, imm_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u3.t_mem = u2.t_mem /\ u3.t_stor = u2.t_stor /\ u3.t_trans = u2.t_trans /\
   u3.t_imm = u2.t_imm` by
    (simp[Abbr `u3`, Abbr `i2`, step_taint_def, mem_taint_def, imm_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u4.t_mem = u3.t_mem /\ u4.t_stor = u3.t_stor /\ u4.t_trans = u3.t_trans /\
   u4.t_imm = u3.t_imm` by
    (simp[Abbr `u4`, Abbr `i3`, step_taint_def, mem_taint_def, imm_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  qabbrev_tac `t = jump_to (if j < ncount then body_lbl else exit_lbl) d` >>
  `(!x. ~MEM x [iv;cv;cmp;done] ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H4 x = FLOOKUP G x /\
      op_taint u4 (Var x) = op_taint tn (Var x)) /\
   (!x. MEM x [iv;cv;cmp;done] ==>
      op_taint u4 (Var x) = {} /\ op_prov H4 (Var x) = NONE)` by
    (simp[Abbr `t`, Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`,
       jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, op_prov_def] >> rpt strip_tac >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_fmp = s.vs_fmp /\ mload slot t = n2w j` by
    (simp[Abbr `t`, Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`,
       jump_to_def, update_var_def, mload_def, read_memory_def] >>
     fs[mload_def, read_memory_def]) >>
  `ptr_covers H4 u4 q t 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> gvs[ALL_DISTINCT]) >>
  `step_inst_base i0 s = OK a /\ step_inst_base i1 a = OK b /\
   step_inst_base i2 b = OK c /\ step_inst_base i3 c = OK d` by
    (`eval_operand src a = SOME srcaddr` by
       (Cases_on `src` >> gvs[Abbr `a`, eval_operand_def, lookup_var_update_var]) >>
     `j < dimword(:256)` by decide_tac >>
     simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, mk_inst_def, w2n_n2w,
       abi_decode_load_def] >>
     gvs[ALL_DISTINCT, abi_decode_load_def, abi_decode_source_def, update_var_def]) >>
  `!D fuel. ptr_safe_step D lo fuel ctx fn PG G tn i0 s` by
    (rpt gen_tac >> qpat_x_assum `ptr_covers G tn q s 32` mp_tac >>
     simp[ptr_covers_def] >> strip_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i0`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, eval_operand_def, w2n_n2w] >>
     simp[mem_read_ops_def, op_prov_def] >>
     simp[step_inst_non_invoke, mk_inst_def] >> gvs[mk_inst_def] >>
     simp[Abbr `a`, update_var_def] >> rpt strip_tac >> gvs[]) >>
  `!D fuel n. ptr_safe_step D lo fuel ctx fn PG H1 u1 i1 (a with vs_inst_idx := n)` by
    (rpt gen_tac >>
     `op_taint u1 src = {}` by
       (Cases_on `src` >> simp[op_taint_def, FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i1`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
     simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def,
       exec_result_map_def] >> gvs[mk_inst_def] >>
     simp[Abbr `a`, Abbr `b`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     gvs[exec_result_map_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D fuel n. ptr_safe_step D lo fuel ctx fn PG H2 u2 i2 (b with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i2`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ALL_DISTINCT] >>
     simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def] >> gvs[mk_inst_def] >>
     simp[Abbr `b`, Abbr `a`, Abbr `c`, update_var_def, FDOM_DRESTRICT] >>
     (conj_tac >- (gen_tac >> Cases_on `op = Var iv` >> Cases_on `op = Var cv` >> gvs[])) >>
     gvs[exec_result_map_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D fuel n. ptr_safe_step D lo fuel ctx fn PG H3 u3 i3 (c with vs_inst_idx := n)` by
    (rpt gen_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i3`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def] >>
     simp[Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`, update_var_def] >>
     gvs[mk_inst_def, abi_decode_header_state_def, update_var_def] >>
     gvs[exec_result_map_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (a with vs_inst_idx := 1),H1,u1)` by
    (rpt gen_tac >>
     `slot < dimword (:256)` by decide_tac >>
     simp_tac bool_ss [Abbr `H1`, Abbr `u1`] >>
     `1 = SUC s.vs_inst_idx` by simp[] >> pop_assum SUBST1_TAC >>
     irule header_forward_step >>

     simp[Abbr `i0`, mk_inst_def, is_terminator_def, get_instruction_def,
       abi_decode_header_insts_def, below_frontier_MLOAD, memSafeRunTheory.inst_dload_in_section_other,
       eval_operand_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (a with vs_inst_idx := 1,H1,u1) []
      (OK (b with vs_inst_idx := 2),H2,u2)` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `H2`, Abbr `u2`] >>
     `step_prov PG H1 i1 (b with vs_inst_idx := 1) = step_prov PG H1 i1 b /\
      step_taint i1 (a with vs_inst_idx := 1) (b with vs_inst_idx := 1) u1 =
        step_taint i1 a b u1` by simp[step_prov_inst_idx, step_taint_inst_idx] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (a with vs_inst_idx := 1,H1,u1) []
       (OK ((b with vs_inst_idx := 1) with vs_inst_idx := SUC (a with vs_inst_idx := 1).vs_inst_idx),
        step_prov PG H1 i1 (b with vs_inst_idx := 1),
        step_taint i1 (a with vs_inst_idx := 1) (b with vs_inst_idx := 1) u1)` suffices_by simp[] >>
     irule header_forward_step >>
     simp[Abbr `i1`, mk_inst_def, is_terminator_def, get_instruction_def,
       abi_decode_header_insts_def, below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other,
       Abbr `a`, update_var_def, step_inst_inst_idx_indep, exec_result_map_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (b with vs_inst_idx := 2,H2,u2) []
      (OK (c with vs_inst_idx := 3),H3,u3)` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `H3`, Abbr `u3`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (b with vs_inst_idx := 2,H2,u2) []
       (OK ((c with vs_inst_idx := 2) with vs_inst_idx := SUC (b with vs_inst_idx := 2).vs_inst_idx),
        step_prov PG H2 i2 (c with vs_inst_idx := 2),
        step_taint i2 (b with vs_inst_idx := 2) (c with vs_inst_idx := 2) u2)` suffices_by
       simp[step_prov_inst_idx, step_taint_inst_idx] >>
     irule header_forward_step >>
     simp[Abbr `i2`, mk_inst_def, is_terminator_def, get_instruction_def,
       abi_decode_header_insts_def, below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other,
       Abbr `b`, Abbr `a`, update_var_def, step_inst_inst_idx_indep, exec_result_map_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (c with vs_inst_idx := 3,H3,u3) []
      (OK (d with vs_inst_idx := 4),H4,u4)` by
    (rpt gen_tac >>
     simp_tac bool_ss [Abbr `H4`, Abbr `u4`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (c with vs_inst_idx := 3,H3,u3) []
       (OK ((d with vs_inst_idx := 3) with vs_inst_idx := SUC (c with vs_inst_idx := 3).vs_inst_idx),
        step_prov PG H3 i3 (d with vs_inst_idx := 3),
        step_taint i3 (c with vs_inst_idx := 3) (d with vs_inst_idx := 3) u3)` suffices_by
       simp[step_prov_inst_idx, step_taint_inst_idx] >>
     irule header_forward_step >>
     simp[Abbr `i3`, mk_inst_def, is_terminator_def, get_instruction_def,
       abi_decode_header_insts_def, below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other,
       Abbr `c`, Abbr `b`, Abbr `a`, update_var_def, step_inst_inst_idx_indep, exec_result_map_def]) >>
  `allocas_from lo d /\ (ctx_has_dalloca ctx ==> allocas_below_fmp d)` by
    (simp[Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`, update_var_def,
       allocas_from_def, allocas_below_fmp_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (d with vs_inst_idx := 4,H4,u4) [] (OK t,H4,u4)` by
    (rpt gen_tac >>
     `t = jump_to (if bool_to_word (~(j < ncount)) <> 0w then exit_lbl else body_lbl)
        (d with vs_inst_idx := 4)` by
       (Cases_on `j < ncount` >> simp[Abbr `t`, bool_to_word_def, jump_to_def]) >>
     pop_assum SUBST1_TAC >> irule header_jnz_joint >>
     simp[get_instruction_def, abi_decode_header_insts_def,
       Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`, update_var_def,
       exprPtrUnwrapFramesTheory.copy_allocas_inst_idx] >>
     qexistsl_tac [`id+4`, `Var done`] >>
     simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H4,u4)` by
    (rpt gen_tac >> irule header_joint_then >>
     qexistsl_tac [`H1`, `a with vs_inst_idx := 1`, `u1`] >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     irule header_joint_then >> qexistsl_tac [`H2`, `b with vs_inst_idx := 2`, `u2`] >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     irule header_joint_then >> qexistsl_tac [`H3`, `c with vs_inst_idx := 3`, `u3`] >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     irule header_joint_then >> qexistsl_tac [`H4`, `d with vs_inst_idx := 4`, `u4`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qexistsl_tac [`H4`,`u4`,`t`] >> simp[] >>
  rpt strip_tac >>
  rpt (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` kall_tac) >>
  `i0.inst_opcode <> INVOKE /\ ~is_terminator i0.inst_opcode /\
   i1.inst_opcode <> INVOKE /\ ~is_terminator i1.inst_opcode /\
   i2.inst_opcode <> INVOKE /\ ~is_terminator i2.inst_opcode /\
   i3.inst_opcode <> INVOKE /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  `a.vs_halted = s.vs_halted /\ b.vs_halted = s.vs_halted /\
   c.vs_halted = s.vs_halted /\ d.vs_halted = s.vs_halted` by
    simp[Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def] >>
  simp[ptr_safe_run_def] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  simp[step_inst_non_invoke, ghost_step_def, Abbr `H1`, Abbr `u1`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx] >>
  (conj_tac >- metis_tac[]) >>
  simp[Abbr `H2`, Abbr `u2`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  (conj_tac >- metis_tac[]) >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx,
       Abbr `H3`, Abbr `u3`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  (conj_tac >- metis_tac[]) >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx,
       Abbr `H4`, Abbr `u4`] >>
  qmatch_goalsub_abbrev_tac `ptr_safe_block D lo fuel ctx fn PG H u bb _` >>
  `op_taint u (Var done) = {}` by
    simp[Abbr `u`, op_taint_def, FLOOKUP_UPDATE] >>
  `H = DRESTRICT G (COMPL {iv} INTER COMPL {cv} INTER COMPL {cmp} INTER COMPL {done})` by
    (simp[Abbr `H`] >> gvs[]) >>
  `eval_operand (Var done) d = SOME (bool_to_word (~(j < ncount)))` by
    simp[Abbr `d`, eval_operand_def, lookup_var_update_var] >>
  fs[Abbr `t`] >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `H = _` mp_tac >>
  qpat_x_assum `eval_operand (Var done) d = _` mp_tac >>
  qpat_x_assum `op_taint u (Var done) = {}` mp_tac >>
  qpat_x_assum `allocas_from lo d` mp_tac >>
  qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp d` mp_tac >>
  qpat_x_assum `d.vs_halted = _` mp_tac >>
  qpat_x_assum `~s.vs_halted` mp_tac >>
  qpat_x_assum `bb.bb_instructions = _` mp_tac >>
  qpat_x_assum `lookup_block body_lbl _ = _` mp_tac >>
  qpat_x_assum `lookup_block exit_lbl _ = _` mp_tac >>
  qpat_x_assum `phi_prefix_length body_bb.bb_instructions = 0` mp_tac >>
  qpat_x_assum `phi_prefix_length exit_bb.bb_instructions = 0` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def,
       allocas_from_def, allocas_below_fmp_def] >>
      (conj_tac >- (gen_tac >> Cases_on `op = Var done` >>
         Cases_on `op = Label exit_lbl` >> Cases_on `op = Label body_lbl` >>
         gvs[op_taint_def])) >>
      Cases_on `j < ncount` >>
      gvs[jump_to_def, allocas_from_def, allocas_below_fmp_def] >>
      qpat_x_assum `!aid b sz. _ ==> lo <= b` mp_tac >>
      qpat_x_assum `ctx_has_dalloca ctx ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  Cases_on `j < ncount` >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
      is_terminator_def, eval_operand_inst_idx, bool_to_word_def] >>
  rename1 `jump_to target d` >>
  qmatch_goalsub_abbrev_tac `entry_prov fn _ gg` >>
  `jump_to target (d with vs_inst_idx := 4) = jump_to target d` by
    simp[jump_to_def] >>
  simp[] >>
  `entry_prov fn (jump_to target d) gg = gg /\
   entry_taint_vars fn (jump_to target d) u = u` by
    (irule entry_ghost_no_phi >> simp[jump_to_def] >> metis_tac[]) >>
  `?dest. lookup_block target fn.fn_blocks = SOME dest /\
          phi_prefix_length dest.bb_instructions = 0` by metis_tac[] >>
  `eval_phis (jump_to target d) dest.bb_instructions = OK (jump_to target d)` by
    (Cases_on `dest.bb_instructions` >- simp[eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def]) >>
  simp[] >> disj2_tac >>
  Cases_on `fuel` >- simp[ptr_safe_blocks_def] >>
  simp[Once ptr_safe_blocks_def] >>
  gvs[ptr_safe_run_def, Abbr `gg`, jump_to_def] >>
  qpat_x_assum `!fuel. option_CASE _ _ _` (qspec_then `n` mp_tac) >> simp[]
QED
