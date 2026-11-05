(* Counted optional GAS suffix for raw_call. *)
Theory rawCallPrefixPtr
Ancestors
  rawCallKeywordPrefixPtr gasCount compileEnv venomInst
  gasContext exprSimDefs vyperInterpreter vyperState exprSimWordArgs

(* GAS consumes one observation, even when the runtime oracle is empty. *)
Theorem raw_call_gas_observation_count:
  gas_count_step fuel ctx (mk_inst iid GAS [] [out]) s = 1
Proof
  simp[gas_count_step_def, mk_inst_def]
QED

Theorem ptr_inst_ok_raw_call_gas:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn (mk_inst iid GAS [] [out]) s
Proof
  strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
    ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
    mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  simp[mk_inst_def, venomExecSemanticsTheory.exec_gas_def, AllCaseEqs(),
    venomStateTheory.update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem raw_call_gas_step_base:
  step_inst_base (mk_inst iid GAS [] [out]) s =
    OK (update_var out (case s.vs_gas_readings of [] => 0w | r::rs => r)
      (s with vs_gas_readings := TL s.vs_gas_readings))
Proof
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  Cases_on `s.vs_gas_readings` >>
  simp[mk_inst_def, venomExecSemanticsTheory.exec_gas_def] >>
  fs[venomStateTheory.update_var_def] >>
  simp[venomStateTheory.venom_state_component_equality]
QED

Theorem raw_call_gas_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid GAS [] [out]) /\
  u = update_var out (case s.vs_gas_readings of [] => 0w | r::rs => r)
    (s with vs_gas_readings := TL s.vs_gas_readings) ==>
  gas_path_ptr D 0 ctx func PG G tn s 1
    (step_prov PG G (mk_inst iid GAS [] [out]) u)
    (step_taint (mk_inst iid GAS [] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid GAS [] [out]) s = OK u` by
    simp[raw_call_gas_step_base] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst iid GAS [] [out]) s` by
    simp[ptr_inst_ok_raw_call_gas] >>
  `(mk_inst iid GAS [] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst iid GAS [] [out]).inst_opcode` by
    simp[mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all fragGasSeqPtrTheory.straight_line_ptr_edge >>
  disch_then (qspecl_then [`PG`] mp_tac) >>
  simp[mk_inst_def, venomInstTheory.is_terminator_def] >> strip_tac >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem raw_call_emit_gas_path_ptr:
  emit_op GAS [] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  u = update_var out (case s.vs_gas_readings of [] => 0w | r::rs => r)
    (s with vs_gas_readings := TL s.vs_gas_readings) ==>
  gas_path_ptr D 0 ctx func PG G tn s 1
    (step_prov PG G (mk_inst sa.cs_next_id GAS [] [out]) u)
    (step_taint (mk_inst sa.cs_next_id GAS [] [out]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id GAS [] [out]]` by
    (gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id GAS [] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_gas_path_ptr >> simp[]
QED

Theorem raw_call_gas_ghost_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out /\
  u = update_var out w (s with vs_gas_readings := rs) /\
  H = step_prov PG G (mk_inst iid GAS [] [out]) u /\
  un = step_taint (mk_inst iid GAS [] [out]) s u tn ==>
  ghost_inv dep cenv cx es H un (u with vs_inst_idx := k) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> simp[rawCallHeaderFramePtrTheory.ghost_inv_inst_idx] >>
  irule rawCallHeaderFramePtrTheory.raw_call_header_ghost_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >> gvs[] >>
      simp[decoderGhostFramePtrTheory.step_prov_other_output,
        decoderGhostFramePtrTheory.step_taint_other_output,
        mk_inst_def, venomStateTheory.update_var_def,
        venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
    ptrDisciplineTheory.range_bytes_def, venomStateTheory.update_var_def,
    mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  rpt (CASE_TAC >> gvs[]) >> simp[SF CONJ_ss]
QED

Theorem raw_call_gas_step_taint:
  step_taint (mk_inst iid GAS [] [out]) s
    (update_var out w (s with vs_gas_readings := rs)) tn =
  tn with t_var := tn.t_var |+ (out,{})
Proof
  simp[ptrDisciplineTheory.step_taint_def, mk_inst_def,
    ptrDisciplineTheory.out_taint_def, ptrDisciplineTheory.set_var_taint_def,
    ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
    ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.range_bytes_def,
    codegenRelTheory.source_memory_write_ranges_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SF CONJ_ss, ptrDisciplineTheory.taint_component_equality]
QED

Theorem raw_call_emit_gas_stage:
  emit_op GAS [] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 1 H un (OK t) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    eval_operand (Var out) t = SOME
      (case s.vs_gas_readings of [] => 0w | r::rs => r) /\
    t.vs_gas_readings = TL s.vs_gas_readings /\ op_taint un (Var out) = {} /\
    not_fresh_at sb out /\ t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) ==>
      op_taint un op = op_taint tn op /\
      (!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var out
    (case s.vs_gas_readings of [] => 0w | r::rs => r)
    (s with vs_gas_readings := TL s.vs_gas_readings)` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 1
    (step_prov PG G (mk_inst sa.cs_next_id GAS [] [out]) u)
    (step_taint (mk_inst sa.cs_next_id GAS [] [out]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule raw_call_emit_gas_path_ptr >> simp[Abbr `u`]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H un (OK t)` >>
  `~not_fresh_at sa out /\ not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[compileEnvTheory.not_fresh_at_def]) >>
  `ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un` by
    (qunabbrev_tac `t` >> irule raw_call_gas_ghost_frame >>
     goal_assum (drule_at Any) >> simp[Abbr `H`, Abbr `un`] >>
     qexistsl_tac [`PG`, `sa.cs_next_id`] >> simp[] >>
     qexistsl_tac [`out`, `TL s.vs_gas_readings`,
       `case s.vs_gas_readings of [] => 0w | r::rs => r`] >> simp[Abbr `u`]) >>
  suspend "frame"
QED

Resume raw_call_emit_gas_stage[frame]:
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t` by
    (`stmt_state_rel ctx func cenv cx es
       ((update_var out (case s.vs_gas_readings of [] => 0w | r::rs => r) s)
          with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      wb_frame cenv es sa s
       ((update_var out (case s.vs_gas_readings of [] => 0w | r::rs => r) s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)` by
       (irule rawCallDataHeaderPtrTheory.raw_call_fresh_update_state_frame >> simp[]) >>
     fs[Abbr `t`, Abbr `u`, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       exprSimHashTheory.hash_gas_readings_state_rel,
       loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
       venomStateTheory.lookup_var_def]) >>
  qexistsl_tac [`H`, `un`, `t`] >> simp[] >>
  simp[Abbr `un`, Abbr `u`, raw_call_gas_step_taint] >>
  simp[Abbr `t`, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
    finite_mapTheory.FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rename1 `not_fresh_at sa x` >>
  `x <> out` by metis_tac[] >> simp[]
QED

Finalise raw_call_emit_gas_stage

Theorem raw_call_optional_gas_stage:
  (case gas_opt of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas_op,sb) /\
  (!g. gas_opt = SOME g ==> eval_operand g s = SOME gasw /\ op_taint tn g = {}) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s
      (case gas_opt of SOME g => 0 | NONE => 1) H un (OK t) /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es sa G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    eval_operand gas_op t = SOME (case gas_opt of SOME g => gasw
      | NONE => (case s.vs_gas_readings of [] => 0w | r::rs => r)) /\
    t.vs_gas_readings = (case gas_opt of SOME g => s.vs_gas_readings
      | NONE => TL s.vs_gas_readings) /\ op_taint un gas_op = {} /\
    t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) ==>
      op_taint un op = op_taint tn op /\
      (!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w))
Proof
  Cases_on `gas_opt`
  >- (simp[] >> strip_tac >>
      `?out. gas_op = Var out` by
        (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
         simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
           compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
           compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
           compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[]) >>
      gvs[] >> drule_all raw_call_emit_gas_stage >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qexistsl_tac [`H`, `un`, `t`] >> simp[]) >>
  simp[] >> strip_tac >> gvs[] >> qexistsl_tac [`G`, `tn`, `s`] >>
  simp[exprSimWordArgsTheory.wb_frame_refl, bodyPtrDefsTheory.ghost_kept_def,
    cj 1 fragGasPathPtrTheory.gas_path_ptr_rules]
QED

Theorem raw_call_operands_admissible:
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) args dflt))
    expr_vv_res_ok es ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  drule rawCallShapePtrTheory.eval_expr_raw_call_operand_exit >>
  disch_then (qspecl_then [`flags`, `dflt`, `ann`] assume_tac) >>
  first_x_assum drule >> simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem eval_exprs_append_action:
  !xs ys cx. eval_exprs cx (xs ++ ys) =
    do vs <- eval_exprs cx xs; ws <- eval_exprs cx ys; return (vs ++ ws) od
Proof
  Induct_on `xs`
  >- (simp[Once evaluate_def, FUN_EQ_THM, bind_def, return_def] >>
      rpt gen_tac >> Cases_on `eval_exprs cx ys x` >>
      Cases_on `q` >> simp[]) >>
  rpt gen_tac >> simp[eval_exprs_cons_action, bind_assoc] >>
  simp[FUN_EQ_THM, bind_def, return_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> simp[]) >> Cases_on `v` >> simp[]
QED

(* Machine-only suffixes record observations with F marks, rather than
   requiring the unchanged source action to consume a gas reading. *)
Theorem gas_marked_exec_ptr_implicit_suffix:
  gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0) marks
    res ee G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx func PG G1 tn1 t n G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0)
    (marks ++ REPLICATE n F) res ee G tn r
Proof
  rewrite_tac[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
  strip_tac >> conj_tac
  >- simp[gasSummaryTheory.gas_explicit_append] >>
  simp[listTheory.LENGTH_APPEND] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule fragGasPathPtrTheory.gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_operand_actions:
  eval_exprs cx (a::d::kws) =
    do vs <- eval_exprs cx [a;d];
       kvs <- eval_exprs cx kws; return (vs ++ kvs) od
Proof
  mp_tac (Q.SPECL [`[a;d]`, `kws`, `cx`] eval_exprs_append_action) >> simp[]
QED
