(* Joint emitted operations for runtime-code and memory array selection. *)
Theory bodyFullSubscriptArrayCodeOps
Ancestors
  exprSimSubscriptArrayFramed loweringShapeRules exprLoweringProps
  typedCopyOriginPtrBase loweringStateRelDefs compileEnv
  fragGasSeqPtr fragGasOriginPtr fragExec memSafeRun unitTransformDefs
  emitHelperProps exprPtrUnwrapCodeEdges stmtAppendStorageRunPtr bodyPtrDefs
  context contextCodegenRel codegenRel ptrDiscipline venomExecSemantics venomInstProofs
  venomState venomInst finite_map words list arithmetic
  storageCopyBodyPtr[qualified,ignore_grammar]

Theorem runtime_load_joint_path[local]:
  emit_op DLOAD [arg] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  w2n a <= LENGTH s.vs_data_section /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  i = mk_inst sa.cs_next_id DLOAD [arg] [out] /\
  u = update_var out (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s ==>
  emitted_insts sa sb = [i] /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  !D lo explicit. allocas_from lo s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G i u,step_taint i s u tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by (drule emit_op_facts >> simp[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id DLOAD [arg]
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG G i u` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, exprSimUnwrapTheory.step_DLOAD] >>
  conj_tac >- fs[run_inst_seq_def, Abbr `i`] >>
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_code_load >> simp[]) >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, inst_mem_below_frontier_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` by
    (mp_tac (straight_line_origin_ptr_edge |> Q.INST [`i` |-> `i`, `u` |-> `u`]) >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[Abbr `u`, update_var_def] >>
  drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
  metis_tac[cj 2 gas_origin_ptr_path_rules, APPEND]
QED

(* The raw DLOAD and the joint path share their endpoint up to the PC. *)
Theorem compile_imm_load_word_runtime_joint_run:
  compile_imm_load_word F imm arg sa = (op,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  w2n a <= LENGTH s.vs_data_section /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out Gf tnf sf.
    op = Var out /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id DLOAD [arg] [out]] /\
    (?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
      sf = (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id DLOAD [arg] [out]` >>
  qabbrev_tac `u = update_var out (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  qexistsl_tac [`step_prov PG G i u`, `step_taint i s u tn`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `emitted_insts sa sb = [i] /\
   run_inst_seq (emitted_insts sa sb) s = OK u /\
   (!D lo explicit. allocas_from lo s ==>
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
        step_prov PG G i u,step_taint i s u tn))` by
    metis_tac[runtime_load_joint_path] >>
  conj_tac >- simp[Abbr `i`] >>
  conj_tac >- (qexists_tac `u` >> simp[ADD1]) >>
  conj_tac >- simp[] >>
  `!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==>
      stmt_state_rel H ctx func cenv cx es (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >>
     drule_all (cj 1 compile_imm_load_word_runtime_frame |>
       REWRITE_RULE [compile_imm_load_word_runtime]) >>
     disch_then (qspec_then `word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))` mp_tac) >>
     simp[Abbr `u`, ADD1]) >>
  `op_prov (step_prov PG G i u) (Var out) = NONE` by
    (simp[Abbr `i`] >> irule step_prov_out_none >>
     simp[mk_inst_def] >> irule out_prov_other_none >> simp[mk_inst_def]) >>
  `!p. p <> out ==> FLOOKUP (step_prov PG G i u) p = FLOOKUP G p /\
    op_taint (step_taint i s u tn) (Var p) = op_taint tn (Var p)` by
    simp[Abbr `i`, scalar_step_old_prov, scalar_step_old_taint] >>
  `!p. not_fresh_at sa p ==> p <> out` by metis_tac[] >>
  simp[Abbr `i`, runtime_code_load_clean] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def,
       mem_taint_def, store_taint_def, imm_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       adopt_reset_def, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]
QED

Theorem compile_imm_load_word_runtime_joint_frame_run:
  compile_imm_load_word F imm arg sa = (op,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  w2n a <= LENGTH s.vs_data_section /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out Gf tnf sf.
    op = Var out /\
    (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
         sf = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  disch_then (mp_tac o MATCH_MP compile_imm_load_word_runtime_joint_run) >>
  disch_then (qx_choosel_then [`out`,`Gf`,`tnf`,`sf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`out`,`Gf`,`tnf`,`sf`] >> simp[]
QED
Theorem compile_imm_load_word_runtime_joint_frame:
  compile_imm_load_word F imm arg sa = (op,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  w2n a <= LENGTH s.vs_data_section /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out Gf tnf sf.
    op = Var out /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all compile_imm_load_word_runtime_joint_run >>
  disch_then (qspecl_then [`PG`, `G`]
    (qx_choosel_then [`out`, `Gf`, `tnf`, `sf`] strip_assume_tac)) >>
  qexistsl_tac [`out`, `Gf`, `tnf`, `sf`] >> simp[]
QED

(* ADD keeps the left operand's provenance when the right is scalar. *)
Theorem scalar_binop_joint_frame_run_endpoint[local]:
  (opc = ADD /\ w = a + b \/ opc = MUL /\ w = a * b) /\
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    sf = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
         sf = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\
    op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = (if opc = ADD then op_prov G left else NONE) /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\
    sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emit_op_facts >> strip_tac >>
  qpat_x_assum `Var _ = Var _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
  rename1 `emit_op opc [left;right] sa = (Var out,sb)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc [left;right] [out]` >>
  qabbrev_tac `u = update_var out w s` >>
  qexistsl_tac [`step_prov PG G i u`, `step_taint i s u tn`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac
  >- (`step_inst_base i s = OK u` by
        (simp[Abbr `i`, Abbr `u`] >> gvs[] >> metis_tac[step_ADD, step_MUL]) >>
      qexists_tac `u` >> drule emitted_insts_emit_op >> strip_tac >>
      gvs[Abbr `i`, run_inst_seq_def, ADD1]) >>
  conj_tac
  >- (rpt strip_tac >>
      `?o' t K tau. Var out = Var o' /\
        t = (update_var o' w s with vs_inst_idx := SUC s.vs_inst_idx) /\
        K = step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [o'])
          (update_var o' w s) /\
        tau = step_taint (mk_inst sa.cs_next_id opc [left;right] [o']) s
          (update_var o' w s) tn /\
        gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,K,tau)` by
        (drule typed_copy_origin_ptr_binop_path >> simp[] >> metis_tac[]) >>
      gvs[Abbr `i`, Abbr `u`]) >>
  `!q. not_fresh_at sa q ==> q <> out` by metis_tac[] >>
  `out = STRING #"%" (toString sa.cs_next_var)` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==>
      stmt_state_rel H ctx func cenv cx es (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     metis_tac[local_ptrs_reserved_fresh, LESS_EQ_REFL]) >>
  `opc = MUL \/ opc = ADD` by metis_tac[] >>
  `op_prov (step_prov PG G i u) (Var out) =
     (if opc = ADD then op_prov G left else NONE)` by
    (gvs[Abbr `i`] >>
     simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
          mk_inst_def, FLOOKUP_UPDATE, first_prov_def, FLOOKUP_DRESTRICT] >>
     Cases_on `left` >> gvs[FLOOKUP_DRESTRICT] >>
     rename1 `FLOOKUP G p` >> Cases_on `FLOOKUP G p` >>
     gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  simp[Abbr `i`, Abbr `u`, typed_copy_origin_ptr_binop_ghost_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, ADD1,
       scalar_step_old_prov, scalar_step_old_taint, SF CONJ_ss] >>
  metis_tac[]
QED
Theorem scalar_binop_joint_frame_endpoint:
  (opc = ADD /\ w = a + b \/ opc = MUL /\ w = a * b) /\
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    sf = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\
    op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = (if opc = ADD then op_prov G left else NONE) /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\
    sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  disch_then (mp_tac o MATCH_MP scalar_binop_joint_frame_run_endpoint) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED

Theorem scalar_binop_joint_frame_run:
  (opc = ADD /\ w = a + b \/ opc = MUL /\ w = a * b) /\
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
         sf = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\
    op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = (if opc = ADD then op_prov G left else NONE) /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\
    sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  disch_then (mp_tac o MATCH_MP scalar_binop_joint_frame_run_endpoint) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `sf = update_var _ _ _ with vs_inst_idx := _` kall_tac >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED

Theorem scalar_binop_joint_frame:
  (opc = ADD /\ w = a + b \/ opc = MUL /\ w = a * b) /\
  emit_op opc [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\
    op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = (if opc = ADD then op_prov G left else NONE) /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\
    sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  disch_then (mp_tac o MATCH_MP scalar_binop_joint_frame_endpoint) >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED

Theorem scalar_emit_landing_layout[local]:
  emit_op opc ops sa = (out,sb) /\ (opc = ADD \/ opc = MUL) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]
QED

Theorem scalar_address_landing_append[local]:
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  m = (u with vs_inst_idx := LENGTH sm.cs_current_insts) /\
  run_inst_seq (emitted_insts sm sb) m = OK v /\
  t = (v with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  ?r. run_inst_seq (emitted_insts sa sb) s = OK r /\
      t = (r with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
  drule_all storageCopyBodyPtrTheory.run_inst_seq_cursor_append >> simp[]
QED

(* The final ADD retains the captured base's provenance. *)
Theorem scalar_mul_add_joint_frame_run:
  emit_op MUL [idx;Lit (n2w elem_size)] sa = (Var offset,sm) /\
  emit_op ADD [base_op;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q ==> not_fresh_at sa q) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
         sf = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov G base_op /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `eval_operand (Lit (n2w elem_size)) s = SOME (n2w elem_size) /\
   op_taint tn (Lit (n2w elem_size)) = {} /\
   op_prov G (Lit (n2w elem_size)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (scalar_binop_joint_frame_run |>
    Q.INST [`opc` |-> `MUL`, `w` |-> `a * b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >> simp[word_mul_n2w] >>
  disch_then (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac) >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = op_prov G base_op` by
    (Cases_on `base_op` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `eval_operand (Var offset) s1 = SOME (n2w (i * elem_size))` by
    simp[eval_operand_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all (scalar_binop_joint_frame_run |>
    Q.INST [`opc` |-> `ADD`, `w` |-> `a + b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac) >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       s2 = (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (imp_res_tac (SIMP_RULE (srw_ss()) []
       (Q.INST [`opc` |-> `ADD`] scalar_emit_landing_layout)) >>
     imp_res_tac (SIMP_RULE (srw_ss()) []
       (Q.INST [`opc` |-> `MUL`] scalar_emit_landing_layout)) >>
     drule_all scalar_address_landing_append >> simp[]) >>
  qexistsl [`G2`,`tn2`,`s2`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `allocas_from lo s1` by (gvs[allocas_from_def] >> (gvs[allocas_from_def])) >>
      metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm q` by metis_tac[ci_mono_def, loweringShapeDefsTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem code_dynamic_address_joint_frame_run:
  emit_op ADD [base_op;Lit 32w] sa = (Var data,sm) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sm = (Var offset,sn) /\
  emit_op ADD [Var data;Var offset] sn = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    (?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
         sf = (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (32 + i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, cs_extends_trans, fn_has_code_split] >>
  `eval_operand (Lit 32w) s = SOME 32w /\
   op_taint tn (Lit 32w) = {} /\ op_prov G (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (scalar_binop_joint_frame_run |>
    Q.INST [`opc` |-> `ADD`, `w` |-> `a + b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `not_fresh_at sm data` by
    (qpat_assum `emit_op ADD [base_op;Lit 32w] sa = _`
       (mp_tac o MATCH_MP emit_op_facts) >> simp[]) >>
  `(!q. Var data = Var q ==> not_fresh_at sm q) /\
   (!l. Var data <> Label l) /\ eval_operand (Var data) s1 = SOME (a + 32w)` by
    simp[eval_operand_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all scalar_mul_add_joint_frame_run >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       s2 = (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (imp_res_tac (SIMP_RULE (srw_ss()) []
       (Q.INST [`opc` |-> `ADD`] scalar_emit_landing_layout)) >>
     imp_res_tac (SIMP_RULE (srw_ss()) []
       (Q.INST [`opc` |-> `MUL`] scalar_emit_landing_layout)) >>
     `emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
       (irule emitted_insts_append >> simp[]) >>
     `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
      EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
       (simp[] >> metis_tac[APPEND_ASSOC]) >>
     drule_all scalar_address_landing_append >> simp[]) >>
  qexistsl [`G2`, `tn2`, `s2`] >>
  simp[GSYM word_add_n2w, WORD_ADD_ASSOC] >> conj_tac
  >- (rpt strip_tac >>
      `allocas_from lo s1` by (gvs[allocas_from_def] >> gvs[allocas_from_def]) >>
      metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm q` by metis_tac[ci_mono_def, loweringShapeDefsTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem scalar_mul_add_joint_frame:
  emit_op MUL [idx;Lit (n2w elem_size)] sa = (Var offset,sm) /\
  emit_op ADD [base_op;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q ==> not_fresh_at sa q) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov G base_op /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all scalar_mul_add_joint_frame_run >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED

Theorem code_dynamic_address_joint_frame:
  emit_op ADD [base_op;Lit 32w] sa = (Var data,sm) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sm = (Var offset,sn) /\
  emit_op ADD [Var data;Var offset] sn = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\ op_prov G base_op = NONE /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (32 + i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all code_dynamic_address_joint_frame_run >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED
