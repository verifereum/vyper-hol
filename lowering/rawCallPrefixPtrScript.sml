(* Counted optional GAS suffix for raw_call. *)
Theory rawCallPrefixPtr
Ancestors
  rawCallKeywordPrefixPtr gasCount compileEnv venomInst
  gasContext exprSimDefs vyperInterpreter vyperState exprSimWordArgs
  abiCanonicalHeadSize

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
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
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
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
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

(* Operand prefix, before the optional machine-only GAS instruction. *)
Theorem raw_call_operands_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  raw_call_kws_ok flags kws /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\
  emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  fn_has_code sa s5 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (a::d::kws)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?av bs kvs xs ea ed ta tb th b x base sz.
      rr = INL (av::BytesV bs::kvs) /\ value_has_type (BaseTV AddressT) av /\
      expr_post ctx func cenv cx a es sa s1 s0 ea av addr ta /\
      expr_post ctx func cenv cx d ea s1 s2 ta ed (BytesV bs) data tb /\
      typed_args_post ctx func cenv cx ed sm th ee kws xs kvs t /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ig = NONE /\
      EVERY (\op. op_taint tn op = {}) xs /\
      EVERY (\op. !l. op <> Label l) xs /\
      EVERY (\op. !v. op = Var v ==> not_fresh_at s5 v) xs /\
      stmt_state_rel ctx func cenv cx ee t /\ expr_sim_inv cenv cx env ee /\
      wb_frame cenv es sa s0 t /\ ghost_inv dep cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      t.vs_current_bb = s5.cs_current_bb /\
      t.vs_inst_idx = LENGTH s5.cs_current_insts /\ ~t.vs_halted /\
      expr_val_rel cx (BaseT AddressT) av addr t /\ op_taint tn addr = {} /\
      eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
      eval_operand data_op t = SOME (n2w (b+32)) /\
      op_taint tn len_op = {} /\ op_taint tn data_op = {} /\
      data = Var x /\ eval_operand data t = SOME (n2w b) /\
      FLOOKUP G x = SOME (base,sz) /\ op_prov G data_op = SOME (base,sz) /\ base <= b /\
      b + 32 + LENGTH bs <= base + sz /\ b < dimword (:256) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      (!v. addr = Var v \/ data = Var v \/ len_op = Var v \/ data_op = Var v ==>
        not_fresh_at s5 v) /\
      expr_val_at cenv cx (expr_type d) s1 s5 ee (BytesV bs) data t)
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by
    (fs[vyperTypeSystemTheory.raw_call_kws_ok_def] >>
     metis_tac[listTheory.LENGTH_MAP]) >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `expr_sim_inv cenv cx env es` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  `cs_extends sa sm /\ cs_extends sm s5` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa sm func /\ fn_has_code sm s5 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all rawCallOperandPrefixPtrTheory.raw_call_addr_data_header_sim_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  once_rewrite_tac[raw_call_operand_actions] >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "tail_cert"
  >- suspend "head_cert"
  >> irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "keywords"
  >> simp[exprSimWordArgsTheory.wb_args_exit_def] >> rpt strip_tac >> gvs[]
QED

Resume raw_call_operands_sim_ptr[head_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >>
  goal_assum (drule_at Any)
QED

Resume raw_call_operands_sim_ptr[tail_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Resume raw_call_operands_sim_ptr[keywords]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule rawCallShapePtrTheory.raw_call_pre_operands >> strip_tac >> gvs[] >>
  `local_ptrs_reserved cenv sm` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `expr_body_pre cenv cx env d ee` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
      SOME (BaseTV (BytesT (Dynamic n)))` by
    (qpat_assum `expr_body_pre _ _ _ d _`
       (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `expr_body_pre cenv cx env a es` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
  `(!l. addr <> Label l)` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!l. len_op <> Label l) /\ (!l. data_op <> Label l)` by
    metis_tac[exprSafeOperandTheory.emit_op_safe_operand,
      exprSafeOperandTheory.safe_operand_def] >>
  `(!op. MEM op [addr;len_op;data_op] ==>
      (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l))` by
    (simp[] >> metis_tac[]) >>
  `not_fresh_at sm x` by metis_tac[] >>
  `b + 32 + LENGTH bs <= base' + sz` by decide_tac >>
  `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` mp_tac >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  suspend "keyword_map"
QED

Resume raw_call_operands_sim_ptr[keyword_map]:
  drule_all (Q.INST [`saved` |-> `[addr;len_op;data_op]`]
    rawCallKeywordPrefixPtrTheory.raw_call_kwargs_sim_ptr) >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule (BETA_RULE (Q.ISPEC `\kvs. av::BytesV bs::kvs`
    (Q.GEN `f` (SPEC_ALL operandOutcomePtrTheory.gas_outcome_ptr_map_return)))) >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `wb_frame cenv es sa s0 t'` by
        (irule exprSimWordArgsTheory.wb_frame_trans >>
         goal_assum (drule_at Any) >> conj_tac
         >- (qexistsl_tac [`ee`,`sm`,`t`] >>
             simp[] >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
         goal_assum (drule_at Any)) >>
      `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
        (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
         >- (qexists_tac `func` >>
             fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
         qexistsl_tac [`G`, `ee`, `t`, `sm`, `tn`] >>
         fs[exprLoweringPropsTheory.ci_mono_def]) >>
      `expr_val_rel cx (BaseT AddressT) av addr t' /\ op_taint tn' addr = {}` by
        (qpat_assum `!op. _ ==> op_prov G' op = _ /\ _`
           (qspec_then `addr` assume_tac) >>
         qpat_x_assum `expr_val_rel cx (BaseT AddressT) av addr t` mp_tac >>
         simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
      `op_prov G' data_op = SOME (base',sz)` by
        (qpat_assum `!op. _ ==> op_prov G' op = _ /\ _`
          (qspec_then `data_op` mp_tac) >> simp[]) >>
      qexistsl_tac [`xs'`, `ea`, `ee`, `ta`, `tb`, `t`, `b`] >>
      simp[wordsTheory.MOD_DIMINDEX] >> conj_tac
      >- (qpat_x_assum `mem_bytes_at b (LENGTH bs + 32) _ = _` mp_tac >>
          qpat_x_assum `mem_bytes_at (b + 32) (LENGTH bs) _ = bs` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          qspecl_then [`b`, `32`, `LENGTH bs`, `LENGTH bs + 32`]
            (fn th => simp[GSYM th]) abiCanonicalHeadSizeTheory.mem_bytes_at_window) >>
      qpat_x_assum `!v. _ ==> not_fresh_at sm v` mp_tac >>
      qpat_x_assum `sm.cs_next_var <= s5.cs_next_var` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[compileEnvTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >> rpt gen_tac >> Cases_on `res` >>
     simp[exprSimWordArgsTheory.wb_args_exit_def]
QED


Finalise raw_call_operands_sim_ptr

Theorem ext_call_kwarg_member:
  !ks xs op. ext_call_kwarg kw ks xs = SOME op ==> MEM op xs
Proof
  Induct_on `ks` >> Cases_on `xs` >> simp[ext_call_kwarg_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem typed_args_post_operands_evaluate:
  typed_args_post ctx func cenv cx es sa s0 ee args xs vs t ==>
  EVERY (\op. ?w. eval_operand op t = SOME w) xs
Proof
  simp[exprSimPrecompilesTheory.typed_args_post_def,
    listTheory.EVERY_EL, listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem raw_call_prefix_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  raw_call_kws_ok flags kws /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\
  emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  fn_has_code sa s6 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (a::d::kws)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?av bs kvs xs ea ed ta tb th b x base sz t5 gasw.
      rr = INL (av::BytesV bs::kvs) /\ value_has_type (BaseTV AddressT) av /\
      expr_post ctx func cenv cx a es sa s1 s0 ea av addr ta /\
      expr_post ctx func cenv cx d ea s1 s2 ta ed (BytesV bs) data tb /\
      typed_args_post ctx func cenv cx ed sm th ee kws xs kvs t /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ig = NONE /\
      EVERY (\op. op_taint tn op = {}) xs /\
      EVERY (\op. !l. op <> Label l) xs /\
      EVERY (\op. !v. op = Var v ==> not_fresh_at s6 v) xs /\
      stmt_state_rel ctx func cenv cx ee t /\ expr_sim_inv cenv cx env ee /\
      wb_frame cenv es sa s0 t /\ ghost_inv dep cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      t.vs_current_bb = s6.cs_current_bb /\
      t.vs_inst_idx = LENGTH s6.cs_current_insts /\ ~t.vs_halted /\
      expr_val_rel cx (BaseT AddressT) av addr t /\ op_taint tn addr = {} /\
      eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
      eval_operand data_op t = SOME (n2w (b+32)) /\
      op_taint tn len_op = {} /\ op_taint tn data_op = {} /\
      data = Var x /\ eval_operand data t = SOME (n2w b) /\
      FLOOKUP G x = SOME (base,sz) /\ op_prov G data_op = SOME (base,sz) /\ base <= b /\
      b + 32 + LENGTH bs <= base + sz /\ b < dimword (:256) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      (!v. addr = Var v \/ data = Var v \/ len_op = Var v \/ data_op = Var v ==>
        not_fresh_at s6 v) /\
      (!g. go = SOME g ==> eval_operand g t5 = SOME gasw) /\
      eval_operand gas_op t = SOME (case go of SOME g => gasw
        | NONE => case t5.vs_gas_readings of [] => 0w | r::rs => r) /\
      op_taint tn gas_op = {} /\
      t.vs_gas_readings = (case go of SOME g => t5.vs_gas_readings
        | NONE => TL t5.vs_gas_readings) /\
      expr_val_at cenv cx (expr_type d) s1 s6 ee (BytesV bs) data t)
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by
    (fs[vyperTypeSystemTheory.raw_call_kws_ok_def] >>
     metis_tac[listTheory.LENGTH_MAP]) >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `expr_sim_inv cenv cx env es` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op,
       pairTheory.SND, exprLoweringPropsTheory.ci_mono_refl]) >>
  `cs_extends sa s5 /\ cs_extends s5 s6 /\ sa.cs_next_var <= s5.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa s5 func /\ fn_has_code s5 s6 func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all raw_call_operands_sim_ptr >>
  disch_then (qspec_then `PG` mp_tac) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def,
    gasSummaryComposePtrTheory.gas_summary_ptr_at_marked] >>
  strip_tac
  >- suspend "gas_normal"
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Resume raw_call_prefix_sim_ptr[gas_normal]:
  gvs[] >>
  `local_ptrs_reserved cenv s5` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `?gasw. !g. ext_call_kwarg EKGas flags.rcf_kws xs' = SOME g ==>
      eval_operand g t = SOME gasw /\ op_taint tn g = {}` by
    (Cases_on `ext_call_kwarg EKGas flags.rcf_kws xs'` >- simp[] >>
     drule ext_call_kwarg_member >> strip_tac >>
     drule typed_args_post_operands_evaluate >> strip_tac >>
     qpat_x_assum `EVERY (\op. ?w. eval_operand op t = SOME w) xs'` mp_tac >>
     qpat_x_assum `MEM _ xs'` mp_tac >>
     qpat_x_assum `EVERY (\op. op_taint tn op = {}) xs'` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  fs[stmtFragPtrTheory.ghost_inv_gas_obs] >>
  drule_all raw_call_optional_gas_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "gas_post"
QED

Resume raw_call_prefix_sim_ptr[gas_post]:
  qexists_tac `marks ++ REPLICATE
    (case ext_call_kwarg EKGas flags.rcf_kws xs' of NONE => 1 | SOME g => 0) F` >>
  disj1_tac >>
  qexistsl_tac [`INL (av::BytesV bs::kvs)`, `es_end`, `H`, `un`, `OK t'`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_implicit_suffix >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  disj1_tac >> qexists_tac `t'` >> simp[] >>
  qexistsl_tac [`xs'`, `ea`, `ed`, `ta`, `tb`, `t'`, `b`, `base'`, `sz`, `t`, `gasw`] >>
  simp[] >> suspend "transport"
QED

Resume raw_call_prefix_sim_ptr[transport]:
  `op_prov H data_op = SOME (base',sz)` by
    (Cases_on `data_op` >>
     fs[ptrDisciplineTheory.op_prov_def, bodyPtrDefsTheory.ghost_kept_def]) >>
  `expr_val_at cenv cx (expr_type d) s1 s6 es_end (BytesV bs) (Var x) t'` by
    (irule stmtSimLogArgsTheory.log_frame_placement >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[exprLoweringPropsTheory.ci_mono_def, loweringPostsTheory.expr_val_at_def] >>
     metis_tac[]) >>
  conj_tac >- suspend "typed_post" >>
  conj_tac
  >- (qpat_x_assum `!op. _ ==> op_taint un op = _ /\ _` mp_tac >>
      qpat_x_assum `EVERY (\op. op_taint tn op = {}) xs'` mp_tac >>
      qpat_x_assum `EVERY (\op. !v. op = Var v ==> not_fresh_at s5 v) xs'` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (fs[listTheory.EVERY_MEM, exprLoweringPropsTheory.ci_mono_def] >>
      metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  conj_tac
  >- (irule exprSimWordArgsTheory.wb_frame_trans >>
      goal_assum (drule_at Any) >> conj_tac
      >- (qexistsl_tac [`es_end`, `s5`, `t`] >>
          simp[] >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
      goal_assum (drule_at Any)) >>
  conj_tac
  >- (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
      >- (qexists_tac `func` >>
          fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
      qexistsl_tac [`G`, `es_end`, `t`, `s5`, `tn`] >>
      fs[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac
  >- (qpat_x_assum `expr_val_rel cx (BaseT AddressT) av addr t` mp_tac >>
      simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `ghost_kept _ _ s5 G tn t H un` mp_tac >>
      simp[bodyPtrDefsTheory.ghost_kept_def]) >>
  conj_tac
  >- (fs[exprLoweringPropsTheory.ci_mono_def] >>
      metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  fs[loweringPostsTheory.expr_val_at_def, exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
QED

Resume raw_call_prefix_sim_ptr[typed_post]:
  qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[exprSimPrecompilesTheory.typed_args_post_def,
    exprSimWordArgsTheory.wb_frame_refl] >> strip_tac >>
  qpat_x_assum `EVERY (\op. !v. op = Var v ==> not_fresh_at s5 v) xs'` mp_tac >>
  qpat_x_assum `!op. _ ==> op_taint un op = _ /\ _` mp_tac >>
  qpat_x_assum `LIST_REL _ xs' _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[listTheory.LIST_REL_EL_EQN, listTheory.EVERY_EL] >> rpt strip_tac >>
  qpat_x_assum `!op. _` (qspec_then `EL n xs'` mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.MIN_DEF]
QED

Finalise raw_call_prefix_sim_ptr
