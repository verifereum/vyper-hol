(* Concrete pointer-safe control edges of the calldata decoder loop. *)
Theory decoderLoopControlPtr
Ancestors abiDecoderContract instIdxIndep ghostPcTransportPtr memLocDefs bodyPtrDefs decoderGhostFramePtr decoderProtectedScratchPtr typedCopyPtr abiDecoderExecution abiDecoderFrame
  entryDispatchPtr typedCopyArrayPtr ptrSafeRun ptrDiscipline
  codegenRel emitHelperProps contextCodegenRel exprLoweringProps
  venomExecSemantics venomState venomInst finite_map pred_set words list arithmetic

Theorem decoder_index_backedge_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ q <> nv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < ncount /\ ncount < dimword (:256) /\ DISJOINT P tn.t_mem /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ?H u t.
    t = jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_fmp = s.vs_fmp /\ ptr_covers H u q t 32 /\
    mload slot t = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem /\
    DISJOINT P u.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. x <> nv ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `jump_to hdr ss` >>
  qabbrev_tac `a = update_var nv (n2w (SUC j)) s` >>
  qabbrev_tac `ainst = mk_inst id ADD [Var iv; Lit 1w] [nv]` >>
  qabbrev_tac `store = mk_inst (id+1) MSTORE [Var q; Var nv] []` >>
  qabbrev_tac `H = step_prov PG G ainst a` >>
  qabbrev_tac `v = step_taint ainst s a tn` >>
  qabbrev_tac `u = step_taint store a ss v` >>
  `FLOOKUP G iv = NONE` by gvs[op_prov_def] >>
  `H = DRESTRICT G (COMPL {nv})` by
    simp[Abbr `H`, Abbr `ainst`, step_prov_def, set_prov_def,
         out_prov_def, first_prov_def, op_prov_def, mk_inst_def] >>
  `v.t_mem = tn.t_mem /\ v.t_var = tn.t_var |+ (nv,{}) /\
   v.t_stor = tn.t_stor /\ v.t_trans = tn.t_trans` by
    (simp[Abbr `v`, Abbr `ainst`, Abbr `a`, step_taint_def,
       mem_taint_def, new_site_bytes_def, update_var_def,
       set_var_taint_def, out_taint_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, mk_inst_def,
       store_taint_def, adopt_reset_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  `lookup_var q a = SOME (n2w slot) /\
   eval_operand (Var nv) a = SOME (n2w (SUC j)) /\
   op_taint v (Var nv) = {}` by
    simp[Abbr `a`, lookup_var_update_var, eval_operand_def, op_taint_def,
         FLOOKUP_UPDATE] >>
  `step_prov PG H store ss = H /\ u.t_var = v.t_var /\
   u.t_stor = v.t_stor /\ u.t_trans = v.t_trans /\
   u.t_mem = v.t_mem DIFF {i | slot <= i /\ i < slot+32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `H`, `id+1`] mp_tac) >>
     simp[Abbr `u`, Abbr `store`, Abbr `ss`, w2n_n2w]) >>
  `(!x. lookup_var x (jump_to hdr ss) = lookup_var x a) /\
   (jump_to hdr ss).vs_allocas = s.vs_allocas /\
   (jump_to hdr ss).vs_initial_fmp = s.vs_initial_fmp /\
   (jump_to hdr ss).vs_fmp = s.vs_fmp` by
    simp[Abbr `ss`, Abbr `a`, jump_to_def, mstore_def, update_var_def,
         lookup_var_def] >>
  `(!x. x <> nv ==> lookup_var x (jump_to hdr ss) = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
   op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE` by
    simp[Abbr `a`, lookup_var_update_var, FLOOKUP_DRESTRICT,
         op_taint_def, op_prov_def, FLOOKUP_UPDATE] >>
  `ptr_covers H u q (jump_to hdr ss) 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\ DISJOINT P u.t_mem`
    by (simp[] >> ASM_SET_TAC[]) >>
  `mload slot (jump_to hdr ss) = n2w (SUC j)` by
    simp[Abbr `ss`, abi_decode_mload_jump, venomMemProofsTheory.mload_mstore_same_proof] >>
  qexistsl_tac [`H`, `u`, `jump_to hdr ss`] >>
  simp[] >> strip_tac >> gen_tac >>
  `step_inst_base ainst s = OK a` by
    (drule_all abi_decode_loop_increment_word >> strip_tac >>
     simp[Abbr `ainst`, Abbr `a`, step_inst_base_opcode_eqs,
          exec_pure2_def, mk_inst_def, eval_operand_def]) >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def,
       get_instruction_def, abi_decode_backedge_insts_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           Abbr `ainst`, mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, op_taint_def] >>
      conj_tac >- (gen_tac >> Cases_on `op = Var iv` >> gvs[op_taint_def] >>
                   Cases_on `op = Lit 1w` >> gvs[]) >>
      simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
           eval_operand_def, update_var_def] >> rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke, Abbr `ainst`, mk_inst_def, is_terminator_def,
       ghost_step_def] >>
  qsuff_tac `ptr_safe_block D lo fuel ctx fn PG H v bb
    (a with vs_inst_idx := SUC (LENGTH prefix))`
  >- gvs[Abbr `H`, Abbr `v`, mk_inst_def] >>
  `ptr_covers H v q a 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[Abbr `a`, lookup_var_update_var, FLOOKUP_DRESTRICT,
          op_taint_def, FLOOKUP_UPDATE]) >>
  `step_inst_base store a = OK ss` by
    simp[Abbr `store`, Abbr `ss`, step_inst_base_opcode_eqs,
         exec_write2_def, mk_inst_def, eval_operand_def, w2n_n2w] >>
  `!k n. ptr_safe_step D lo k ctx fn PG H v store (a with vs_inst_idx := n)` by
    (rpt gen_tac >> simp[ptr_safe_step_def] >>
     `allocas_from lo a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
       (simp[Abbr `a`, allocas_from_def, allocas_below_fmp_def, update_var_def] >>
        metis_tac[allocas_from_def, allocas_below_fmp_def]) >>
     fs[allocas_from_def, allocas_below_fmp_def] >>
     qpat_x_assum `ptr_covers H v q a 32` mp_tac >>
     simp[ptr_covers_def] >> strip_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `store`,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, eval_operand_def, w2n_n2w,
       allocas_from_def, allocas_below_fmp_def] >>
     conj_tac
     >- (simp[mem_write_ops_def, op_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
     conj_tac >- (rpt strip_tac >> gvs[]) >>
     `step_inst k ctx (mk_inst (id+1) MSTORE [Var q; Var nv] []) a = OK ss` by
       gvs[step_inst_non_invoke, mk_inst_def] >>
     `step_inst k ctx (mk_inst (id+1) MSTORE [Var q; Var nv] [])
        (a with vs_inst_idx := n) = OK (ss with vs_inst_idx := n)` by
       (simp[step_inst_non_invoke, mk_inst_def] >>
        mp_tac step_inst_inst_idx_indep >>
        disch_then (qspecl_then [`mk_inst (id+1) MSTORE [Var q;Var nv] []`, `a`, `n`] mp_tac) >>
        gvs[mk_inst_def, is_terminator_def, exec_result_map_def]) >>
     gvs[mk_inst_def] >>
     simp[Abbr `ss`, mstore_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `step_inst_base store (a with vs_inst_idx := SUC (LENGTH prefix)) =
     OK (ss with vs_inst_idx := SUC (LENGTH prefix))` by
    ( `~is_terminator store.inst_opcode` by
        simp[Abbr `store`, mk_inst_def, is_terminator_def] >>
      simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  simp[Once ptr_safe_block_def, get_instruction_def,
       abi_decode_backedge_insts_def, EL_APPEND_EQN, ADD1] >>
  conj_tac >- gvs[] >>
  `store.inst_opcode <> INVOKE /\ ~is_terminator store.inst_opcode` by
    simp[Abbr `store`, mk_inst_def, is_terminator_def] >>
  simp[step_inst_non_invoke, GSYM ADD1] >>
  simp[ghost_step_def, step_inst_non_invoke, step_prov_inst_idx,
       step_taint_inst_idx] >>
  qsuff_tac `ptr_safe_block D lo fuel ctx fn PG H u bb
       (ss with vs_inst_idx := LENGTH prefix + 2)`
  >- gvs[Abbr `u`] >>
  simp[Once ptr_safe_block_def, get_instruction_def,
       abi_decode_backedge_insts_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       jump_to_def, Abbr `ss`, Abbr `a`, update_var_def, mstore_def,
       allocas_from_def, allocas_below_fmp_def] >>
      metis_tac[allocas_from_def, allocas_below_fmp_def]) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       is_terminator_def, jump_to_def] >>
  `entry_prov fn (jump_to hdr ss) H = H /\
   entry_taint_vars fn (jump_to hdr ss) u = u` by
    (irule entry_ghost_no_phi >> simp[jump_to_def] >> metis_tac[]) >>
  `eval_phis (jump_to hdr ss) hdr_bb.bb_instructions = OK (jump_to hdr ss)` by
    (Cases_on `hdr_bb.bb_instructions` >- simp[eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def]) >>
  disj2_tac >>
  Cases_on `fuel` >- simp[ptr_safe_blocks_def] >>
  simp[Once ptr_safe_blocks_def, GSYM jump_to_def] >>
  gvs[GSYM jump_to_def, ptr_safe_run_def] >>
  qpat_x_assum `!fuel. option_CASE _ _ _` (qspec_then `n` mp_tac) >>
  simp[jump_to_def]
QED

Theorem decoder_index_header_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts id (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\ src <> Var iv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\ mload slot s = n2w j /\
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
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!x. MEM x [iv;cv;cmp;done] ==>
       op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `run_inst_seq (TAKE 4 (abi_decode_header_insts id (Var q) src CALLDATALOAD
      iv cv cmp done body_lbl exit_lbl)) s =
    OK (abi_decode_header_state iv cv cmp done j ncount s)` by
    (irule abi_decode_header_prefix >>
     simp[abi_decode_source_opcode_def, eval_operand_def, w2n_n2w] >>
     gvs[ALL_DISTINCT]) >>
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
  `H1 = DRESTRICT G (COMPL {iv}) /\
   H2 = DRESTRICT H1 (COMPL {cv}) /\
   H3 = DRESTRICT H2 (COMPL {cmp}) /\
   H4 = DRESTRICT H3 (COMPL {done})` by
    simp[Abbr `H1`, Abbr `H2`, Abbr `H3`, Abbr `H4`,
      Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, step_prov_def,
      set_prov_def, out_prov_def, mk_inst_def] >>
  `u1.t_var = tn.t_var |+ (iv,{})` by
    (simp[Abbr `u1`, Abbr `i0`, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
      w2n_n2w] >> FAIL_TAC "index taint") >>
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
       set_var_taint_def, out_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_UPDATE]) >>
  `u1.t_mem = tn.t_mem /\ u1.t_stor = tn.t_stor /\ u1.t_trans = tn.t_trans` by
    (simp[Abbr `u1`, Abbr `i0`, step_taint_def, mem_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u2.t_mem = u1.t_mem /\ u2.t_stor = u1.t_stor /\ u2.t_trans = u1.t_trans` by
    (simp[Abbr `u2`, Abbr `i1`, step_taint_def, mem_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u3.t_mem = u2.t_mem /\ u3.t_stor = u2.t_stor /\ u3.t_trans = u2.t_trans` by
    (simp[Abbr `u3`, Abbr `i2`, step_taint_def, mem_taint_def,
      new_site_bytes_def, adopt_reset_def, store_taint_def, mk_inst_def,
      Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `u4.t_mem = u3.t_mem /\ u4.t_stor = u3.t_stor /\ u4.t_trans = u3.t_trans` by
    (simp[Abbr `u4`, Abbr `i3`, step_taint_def, mem_taint_def,
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
       FLOOKUP_DRESTRICT, op_taint_def, op_prov_def] >>
     rpt strip_tac >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_fmp = s.vs_fmp /\ mload slot t = n2w j` by
    (simp[Abbr `t`, Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`,
       jump_to_def, update_var_def, mload_def, read_memory_def] >>
     fs[mload_def, read_memory_def]) >>
  `ptr_covers H4 u4 q t 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     gvs[ALL_DISTINCT]) >>
  qexistsl_tac [`H4`, `u4`, `t`] >> simp[Abbr `t`] >>
  strip_tac >> gen_tac >>
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
  `ptr_safe_step D lo fuel ctx fn PG G tn i0 s` by
    (qpat_x_assum `ptr_covers G tn q s 32` mp_tac >>
     simp[ptr_covers_def] >> strip_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i0`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def,
       eval_operand_def, w2n_n2w] >>
     simp[mem_read_ops_def, op_prov_def] >>
     simp[step_inst_non_invoke, mk_inst_def] >>
     gvs[mk_inst_def] >>
     simp[Abbr `a`, update_var_def] >> rpt strip_tac >> gvs[]) >>
  `!n. ptr_safe_step D lo fuel ctx fn PG H1 u1 i1 (a with vs_inst_idx := n)` by
    (gen_tac >>
     `op_taint u1 src = {}` by
       (Cases_on `src` >> simp[op_taint_def, FLOOKUP_UPDATE] >>
        gvs[op_taint_def]) >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i1`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
     simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def,
       exec_result_map_def] >> gvs[mk_inst_def] >>
     simp[Abbr `a`, Abbr `b`, update_var_def,
       allocas_from_def, allocas_below_fmp_def] >>
     gvs[exec_result_map_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!n. ptr_safe_step D lo fuel ctx fn PG H2 u2 i2 (b with vs_inst_idx := n)` by
    (gen_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `i2`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       ALL_DISTINCT] >>
     simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def] >>
     gvs[mk_inst_def] >>
     simp[Abbr `b`, Abbr `a`, Abbr `c`, update_var_def, FDOM_DRESTRICT] >>
     (conj_tac >- (gen_tac >> Cases_on `op = Var iv` >>
       Cases_on `op = Var cv` >> gvs[])) >>
     gvs[exec_result_map_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!n. ptr_safe_step D lo fuel ctx fn PG H3 u3 i3 (c with vs_inst_idx := n)` by
    (gen_tac >>
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
  `i0.inst_opcode <> INVOKE /\ ~is_terminator i0.inst_opcode /\
   i1.inst_opcode <> INVOKE /\ ~is_terminator i1.inst_opcode /\
   i2.inst_opcode <> INVOKE /\ ~is_terminator i2.inst_opcode /\
   i3.inst_opcode <> INVOKE /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  qpat_x_assum `!x. ~MEM x _ ==> _` kall_tac >>
  qpat_x_assum `!x. MEM x _ ==> _` kall_tac >>
  qpat_x_assum `ptr_covers H4 u4 q _ 32` kall_tac >>
  qpat_x_assum `ptr_covers G tn q s 32` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  `a.vs_halted = s.vs_halted /\ b.vs_halted = s.vs_halted /\
   c.vs_halted = s.vs_halted /\ d.vs_halted = s.vs_halted` by
    simp[Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, update_var_def] >>
  simp[ptr_safe_run_def] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  simp[step_inst_non_invoke, ghost_step_def, Abbr `H1`, Abbr `u1`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx] >>
  (conj_tac >- (qpat_x_assum `!n. ptr_safe_step _ _ _ _ _ _ _ _ i1 _`
     (qspec_then `1` mp_tac) >> simp[])) >>
  simp[Abbr `H2`, Abbr `u2`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  (conj_tac >- (qpat_x_assum `!n. ptr_safe_step _ _ _ _ _ _ _ _ i2 _`
     (qspec_then `2` mp_tac) >> gvs[])) >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx,
       Abbr `H3`, Abbr `u3`] >>
  simp[Once ptr_safe_block_def, get_instruction_def, abi_decode_header_insts_def] >>
  (conj_tac >- (qpat_x_assum `!n. ptr_safe_step _ _ _ _ _ _ _ _ i3 _`
     (qspec_then `3` mp_tac) >> gvs[])) >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       ghost_step_def, step_prov_inst_idx, step_taint_inst_idx,
       Abbr `H4`, Abbr `u4`] >>
  qmatch_goalsub_abbrev_tac `ptr_safe_block D lo fuel ctx fn PG H u bb _` >>
  `op_taint u (Var done) = {}` by
    simp[Abbr `u`, op_taint_def, FLOOKUP_UPDATE] >>
  `H = DRESTRICT G (COMPL {iv} INTER COMPL {cv} INTER COMPL {cmp} INTER COMPL {done})` by
    (simp[Abbr `H`] >> gvs[]) >>
  `allocas_from lo d /\ (ctx_has_dalloca ctx ==> allocas_below_fmp d)` by
    (simp[Abbr `d`, Abbr `c`, Abbr `b`, Abbr `a`, update_var_def,
       allocas_from_def, allocas_below_fmp_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `eval_operand (Var done) d = SOME (bool_to_word (~(j < ncount)))` by
    simp[Abbr `d`, eval_operand_def, lookup_var_update_var] >>
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
