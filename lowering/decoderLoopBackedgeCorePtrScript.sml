(* Same-witness frames for the decoder loop backedge. *)
Theory decoderLoopBackedgeCorePtr
Ancestors compileEnv wordLoadStorePtr abiDecoderContract instIdxIndep ghostPcTransportPtr memLocDefs bodyPtrDefs decoderGhostFramePtr decoderProtectedScratchPtr typedCopyPtr abiDecoderExecution abiDecoderFrame
  entryDispatchPtr typedCopyArrayPtr ptrSafeRun ptrDiscipline
  codegenRel emitHelperProps contextCodegenRel exprLoweringProps
  venomExecSemantics venomState venomInst finite_map pred_set words list arithmetic

Theorem decoder_index_backedge_ptr_core_uniform:
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
    u.t_imm = tn.t_imm /\ u.t_mem SUBSET tn.t_mem /\
    (!x. x <> nv ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
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
   v.t_stor = tn.t_stor /\ v.t_trans = tn.t_trans /\ v.t_imm = tn.t_imm` by
    (simp[Abbr `v`, Abbr `ainst`, Abbr `a`, step_taint_def,
       mem_taint_def, imm_taint_def, new_site_bytes_def, update_var_def,
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
  `u.t_imm = v.t_imm` by
    simp[Abbr `u`, Abbr `store`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `u.t_mem SUBSET tn.t_mem` by simp[] >>
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
  simp[] >> gen_tac >> strip_tac >> gen_tac >>
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

Theorem decoder_index_backedge_ptr_core:
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
    u.t_imm = tn.t_imm /\ u.t_mem SUBSET tn.t_mem /\
    (!x. x <> nv ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all decoder_index_backedge_ptr_core_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`t`] >> simp[]
QED

Theorem decoder_index_backedge_replay_frame:
  t = jump_to hdr (mstore slot w (update_var nv w s)) /\
  fresh_vars_wrt limit s /\
  nv = STRING #"%" (toString k) /\ k < limit.cs_next_var ==>
  fresh_vars_wrt limit t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `fresh_vars_wrt limit (update_var nv w s)` by
    (irule fresh_vars_wrt_update_var >> metis_tac[]) >>
  gvs[jump_to_def, mstore_def, update_var_def, fresh_vars_wrt_def]
QED
