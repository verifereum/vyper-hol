(* EXTCODESIZE yields a clean scalar; the bounds logic is source-independent. *)
Theory bodyPtrCodeSliceExternalBounds
Ancestors
  bodyPtrCodeSliceBounds bodyPtrCodeSliceSelfPrefix exprSimSliceExtcode
  fragGasSeqPtr fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState codegenRel contextCodegenRel
  compileEnv loweringStateRelDefs words finite_map pred_set list emitHelperProps
  ghostPcTransportPtr fragExec exprLoweringProps

Theorem external_code_size_ghost:
  !PG G tn s id dst addr a.
    step_prov PG G (mk_inst id EXTCODESIZE [addr] [dst])
      (update_var dst (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s) =
      G \\ dst /\
    step_taint (mk_inst id EXTCODESIZE [addr] [dst]) s
      (update_var dst (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s) tn =
      tn with t_var := tn.t_var |+ (dst,{})
Proof
  rpt gen_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
    new_site_bytes_def, update_var_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, written_taint_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    taint_component_equality, FLOOKUP_DEF, DRESTRICT_DOMSUB,
    EXTENSION] >>
  conj_tac >- simp[fmap_domsub] >>
  Cases_on `eval_operand addr s` >> simp[] >> metis_tac[]
QED

Theorem external_code_size_checked:
  !D ctx fn PG G tn s id dst addr a.
    eval_operand addr s = SOME a /\ op_taint tn addr = {} /\
    ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id EXTCODESIZE [addr] [dst]] s
      (G \\ dst) (tn with t_var := tn.t_var |+ (dst,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id EXTCODESIZE [addr] [dst]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
     simp[exec_read1_def, update_var_def]) >>
  `step_inst_base (mk_inst id EXTCODESIZE [addr] [dst]) s =
    OK (update_var dst (n2w (LENGTH (lookup_account (w2w a) s.vs_accounts).code)) s)` by
    (irule slice_extcodesize_step >> simp[]) >>
  simp[inst_seq_ptr_def, external_code_size_ghost]
QED

Theorem external_code_size_bounds_checked:
  !D ctx fn PG G tn s addr a n limit sa sb sc av wa wn.
    emit_op EXTCODESIZE [addr] sa = (limit,sb) /\
    compile_assert_slice_bounds a n limit sb = ((),sc) /\
    eval_operand addr s = SOME av /\ op_taint tn addr = {} /\
    eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
    op_taint tn a = {} /\ op_taint tn n = {} /\
    op_prov G a = NONE /\ op_prov G n = NONE /\
    (!z. a = Var z ==> not_fresh_at sa z) /\
    (!z. n = Var z ==> not_fresh_at sa z) /\ ~ctx_has_dalloca ctx ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `a <> Var (STRING #"%" (toString sa.cs_next_var)) /\
   n <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_fresh_at sb (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `?Gf tnf. inst_seq_ptr D 0 ctx fn PG
    (G \\ STRING #"%" (toString sa.cs_next_var))
    (tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}))
    (emitted_insts sb sc)
    (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w av) s.vs_accounts).code)) s with
       vs_inst_idx := SUC s.vs_inst_idx) Gf tnf` by
    (irule slice_bounds_checked_ptr >> simp[] >>
     goal_assum (drule_at Any) >>
     simp[eval_operand_inst_idx, GSYM DRESTRICT_DOMSUB,
       slice_bounds_scalar_operand_frame] >>
     simp[eval_operand_def, lookup_var_update_var,
       op_taint_def, op_prov_def, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE] >>
     conj_tac >- (Cases_on `a` >> gvs[op_prov_def]) >>
     Cases_on `n` >> gvs[op_prov_def]) >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[Once inst_seq_ptr_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id EXTCODESIZE [addr]
      [STRING #"%" (toString sa.cs_next_var)]) s` by
    (mp_tac external_code_size_checked >> simp[inst_seq_ptr_def] >> metis_tac[]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
    SRULE [mk_inst_def] external_code_size_ghost]
QED

Theorem external_code_size_bounds_frame:
  emit_op EXTCODESIZE [addr] sa = (limit,sb) /\
  compile_assert_slice_bounds a n limit sb = ((),sc) /\
  eval_operand addr s = SOME av /\
  inst_seq_ptr D 0 ctx fn PG G tn
    (emitted_insts sa sb ++ emitted_insts sb sc) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) /\
  (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) ==>
  ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = n2w (LENGTH (lookup_account (w2w av) s.vs_accounts).code) : bytes32` >>
  qabbrev_tac `u = update_var v w s` >>
  `step_inst_base (mk_inst sa.cs_next_id EXTCODESIZE [addr] [v]) s = OK u` by
    (simp[Abbr `u`, Abbr `w`, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  `run_inst_seq (emitted_insts sb sc) u = OK t` by
    gvs[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D 0 ctx fn PG (G \\ v)
    (tn with t_var := tn.t_var |+ (v,{})) (emitted_insts sb sc)
    (u with vs_inst_idx := SUC s.vs_inst_idx) Gf tnf` by
    gvs[Once inst_seq_ptr_def, Abbr `u`, Abbr `w`, external_code_size_ghost] >>
  `~not_fresh_at sa v` by simp[Abbr `v`, not_fresh_at_def] >>
  drule_all slice_bounds_scalar_frame >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by simp[not_fresh_at_def] >>
  `local_ptrs_reserved cenv sb` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sb p) /\
   (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sb p)` by
    metis_tac[] >>
  `ghost_inv d cenv cx es (G \\ v) (tn with t_var := tn.t_var |+ (v,{})) u` by
    gvs[Abbr `u`, fmap_domsub] >>
  drule_all self_code_bounds_cursor_frame >> strip_tac >>
  conj_tac >- simp[] >> suspend "kept_runtime"
QED

Resume external_code_size_bounds_frame[kept_runtime]:
  `writes_fresh sb (emitted_insts sb sc)` by
    (irule exprSimSliceBoundsTheory.slice_bounds_writes_fresh >> metis_tac[]) >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes u name b sz <=>
    local_region cenv es.scopes s name b sz` by
    (gvs[local_region_def, local_ptrs_reserved_def, eval_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (irule wordArgsPtrTheory.ghost_kept_trans >>
      goal_assum (drule_at (Pat `ghost_kept _ _ sb _ _ _ _ _`)) >>
      gvs[Abbr `u`, fmap_domsub]) >>
  conj_tac >- (rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `t = _ with vs_vars := _` (fn th => once_rewrite_tac [th]) >>
  simp[Abbr `u`, update_var_def]
QED

Finalise external_code_size_bounds_frame
