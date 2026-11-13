(* Pointer certificate for the common SHR/SHL selector mask. *)
Theory bodyPtrEnvBuiltinsMask
Ancestors bodyPtrEnvBuiltinsEdges bodyPtrEnvBuiltinsHashStep
  fragExec fragExecPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs ptrDiscipline
  venomInst venomState venomExecSemantics instIdxIndep compileEnv loweringStateRelDefs
  exprLoweringProps context emitHelper freshWrites rich_list
  words finite_map pred_set list

Theorem method_id_mask_seq_certificate:
  code = [mk_inst ir SHR [Lit 224w; hash] [sel];
          mk_inst il SHL [Lit 224w; Var sel] [out]] /\
  op_taint tn hash = {} /\ eval_operand hash s = SOME w /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa sel /\ ~not_fresh_at sa out /\ ~ctx_has_dalloca ctx /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := k) G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result (Var out) G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  qabbrev_tac `u = update_var sel (w >>> 224) s` >>
  `step_inst_base (mk_inst ir SHR [Lit 224w; hash] [sel]) s = OK u` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, Abbr `u`, eval_operand_def, dimword_def]) >>
  `step_inst_base (mk_inst il SHL [Lit 224w; Var sel] [out]) u =
    OK (update_var out ((w >>> 224) << 224) u)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, Abbr `u`, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, dimword_def]) >>
  `t = update_var out ((w >>> 224) << 224) u` by gvs[run_inst_seq_def] >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst ir SHR [Lit 224w; hash] [sel]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst ir SHR [Lit 224w; hash] [sel]) s u tn` >>
  `op_taint tn1 (Var sel) = {}` by
    (simp[Abbr `tn1`] >> irule scalar_builtin_output_clean >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  `ghost_inv d cenv cx es G1 tn1 u /\ ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `u`] >> irule scalar_builtin_update_ghosts >> simp[]) >>
  qexistsl_tac [`step_prov PG G1 (mk_inst il SHL [Lit 224w; Var sel] [out]) t`,
    `step_taint (mk_inst il SHL [Lit 224w; Var sel] [out]) u t tn1`] >>
  conj_tac >- suspend "checks" >>
  conj_tac
  >- (simp[ptr_val_ok_def, is_word_type_def] >> conj_tac
      >- (irule scalar_builtin_output_clean >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
      irule scalar_builtin_output_no_prov >> simp[]) >>
  gvs[] >> irule scalar_builtin_update_ghosts >> simp[]
QED

Resume method_id_mask_seq_certificate[checks]:
  gvs[mk_inst_def, Abbr `G1`, Abbr `tn1`] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       is_terminator_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >> conj_tac
  >- (irule ptr_inst_ok_scalar_builtin >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  irule ptr_inst_ok_scalar_builtin >> simp[] >>
  rpt strip_tac >> gvs[] >> gvs[op_taint_def, mk_inst_def]
QED

Finalise method_id_mask_seq_certificate

Theorem method_id_mask_compile_code:
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) ==>
  ?x y. op = Var y /\ sel = Var x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SHR [Lit 224w; hash] [x];
       mk_inst (sa.cs_next_id+1) SHL [Lit 224w; Var x] [y]] /\
    ~not_fresh_at sa x /\ ~not_fresh_at sa y /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, not_fresh_at_def]
QED

Theorem method_id_mask_compile_counted:
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) /\
  op_taint tn hash = {} /\ eval_operand hash s = SOME w /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sf G0 tn0 s0 G tn /\ local_ptrs_reserved cenv sf /\
  (!x. not_fresh_at sf x ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result op G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es0 sf G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_all method_id_mask_compile_code >> strip_tac >>
  `~not_fresh_at sf x /\ ~not_fresh_at sf y` by metis_tac[] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     qexists_tac `l` >> simp[]) >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result op G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es0 sf G0 tn0 s0 G' tn'` by
    (drule_at (Pat `_ = [_;_]`) method_id_mask_seq_certificate >>
     disch_then drule_all >>
     disch_then (qspecl_then [`result`, `s.vs_inst_idx`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED
