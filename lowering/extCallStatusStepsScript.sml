Theory extCallStatusSteps
Ancestors
  bodyFullRawCallCallOrigin fragGasEmitCtrl fragGasOriginPtrLoop fragGasOrigin
  fragExec emitHelper emitHelperProps frameGasEvents venomExecSemantics
  venomExecProps venomInst venomInstProps venomState ptrDiscipline
  instMemFrontier finite_map pred_set words

(* The emitted status branch is fetched at the intermediate cursor. It takes
   only the edge selected by the status operand, without entering either block
   for an additional instruction. *)
Theorem extcall_status_jnz_edge[local]:
  emit_inst JNZ [op; Label lt; Label lf] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ eval_operand op s = SOME (if b then 1w else 0w) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted ==>
  (?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx =
          SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])) /\
  gas_origin_edge F explicit ctx func s [] (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s =
    OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] mp_tac) >>
     Cases_on `b` >> simp[]) >>
  pure_rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`0`, `bb`, `mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []`,
                `OK (jump_to (if b then lt else lf) s)`] >>
  simp[gas_events_step_plain, mk_inst_def, is_terminator_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `if b then lt else lf` >> simp[]
QED

(* The physical edges are independent of D. The pointer path reuses their
   intermediate and final states for every valid input storage taint. *)
Theorem extcall_dispatch_status_edges:
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [g;a;dp;dl;rp;rl] else [g;a;v;dp;dl;rp;rl]) /\
  inst.inst_outputs = [out] /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand rp s = SOME ro /\ eval_operand rl s = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (rn <> 0w ==> ?p. rp = Var p /\ ptr_covers G tn p s (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_mem_below_frontier inst s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u /\
  u = update_var out (if success then 1w else 0w) t /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
  u.vs_initial_fmp = s.vs_initial_fmp /\
  sj.cs_current_bb = s.vs_current_bb /\ LENGTH sj.cs_current_insts = SUC s.vs_inst_idx /\
  emit_inst JNZ [Var out; Label cont_lbl; Label fail_lbl] [] sj = ((),se) /\
  fn_has_code sj se func ==>
  gas_origin_edge F explicit ctx func s [] (OK (next_inst u)) /\
  (next_inst u).vs_current_bb = sj.cs_current_bb /\
  (next_inst u).vs_inst_idx = LENGTH sj.cs_current_insts /\
  (?jb. lookup_block (next_inst u).vs_current_bb func.fn_blocks = SOME jb /\
        get_instruction jb (next_inst u).vs_inst_idx =
          SOME (mk_inst sj.cs_next_id JNZ [Var out; Label cont_lbl; Label fail_lbl] [])) /\
  gas_origin_edge F explicit ctx func (next_inst u) []
    (OK (jump_to (if success then cont_lbl else fail_lbl) (next_inst u))) /\
  !D. stor_taint_ok_at D tn s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if success then cont_lbl else fail_lbl) (next_inst u)),
       step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u /\ ~is_terminator inst.inst_opcode` by
    (Cases_on `stat` >> simp[step_inst_non_invoke, is_terminator_def]) >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  `eval_operand (Var out) (next_inst u) = SOME (if success then 1w else 0w)` by
    simp[next_inst_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `u = update_var _ _ _` kall_tac >>
  `(next_inst u).vs_current_bb = sj.cs_current_bb /\
   (next_inst u).vs_inst_idx = LENGTH sj.cs_current_insts /\ ~(next_inst u).vs_halted` by
    simp[next_inst_def, GSYM arithmeticTheory.ADD1] >>
  conj_tac
  >- (pure_rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
      qexistsl_tac [`0`, `bb`, `inst`, `OK u`] >>
      Cases_on `stat` >> simp[gas_events_step_plain, next_inst_def, GSYM arithmeticTheory.ADD1]) >>
  drule_all extcall_status_jnz_edge >> strip_tac >>
  simp[] >> gen_tac >> strip_tac >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    (Cases_on `stat` >> simp[step_taint_def, out_taint_def,
       set_var_taint_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (next_inst u),step_prov PG G inst u,step_taint inst s u tn)` by
    (simp[next_inst_def, GSYM arithmeticTheory.ADD1] >>
     irule raw_call_step_origin_full >>
     simp[] >>
     qexistsl [`ao`,`az`,`dl`,`dp`,`g`,`rp`,`rn`,`ro`,`rl`,`a`,`v`] >>
     Cases_on `stat` >> simp[]) >>
  irule gas_origin_ptr_path_trans >> goal_assum drule >>
  irule emit_jnz_origin_ptr >> simp[] >>
  `allocas_from lo (next_inst u) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (next_inst u))` by
    (gvs[next_inst_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[] >> qexistsl [`Var out`,`sj`,`se`] >> simp[]
QED
