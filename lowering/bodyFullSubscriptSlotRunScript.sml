(* Counted array selection in slot units, from the post-index cursor. *)
Theory bodyFullSubscriptSlotRun
Ancestors
  bodyFullTargetArrayLoad bodyFullTargetArraySuffix fragGasOriginPtrDead
  fragGasOriginPtr fragGasOriginPtrLoop exprPtrUnwrapCopyEdges bodyPtrDefs
  exprLowering exprLoweringProps exprSimArrayIndex freshWrites fragExec
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics ptrDiscipline memLocDefs contextCodegenRel codegenRel
  unitTransformDefs loweringStateRelDefs finite_map rich_list words
  stmtReasonLitFragMemory bodyBinopFragMemory loweringPosts

Theorem slot_bounds_layout[local]:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  sa.cs_next_var <= sb.cs_next_var
Proof
  simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  Cases_on `sgn` >> simp[comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (imp_res_tac ci_mono_emit_op >> imp_res_tac ci_mono_emit_void >>
     fs[ci_mono_def] >> decide_tac) >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC,
       mk_inst_def, is_terminator_def]
QED

Theorem slot_address_layout[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)
Proof
  Cases_on `dyn` >> simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC,
       mk_inst_def, is_terminator_def]
QED

Theorem slot_length_step[local]:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (Var out,sb) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  array_length_step_ok lo ctx fn (if tr then TLOAD else SLOAD) [bop]
    (if tr then tload slot s else sload slot s) sa out sb s G tn
Proof
  Cases_on `tr` >>
  simp[array_length_step_ok_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, access_ok_def, taint_ok_def, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def]
QED

Theorem slot_length_stage_run:
  (if dyn then compile_ptr_load ctor imm (slot_loc tr) bop
   else comp_return (Lit (n2w cnt))) sa = (len,sl) /\
  fn_has_code sa sl fn /\ eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  (dyn ==> key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand len t = SOME (if dyn then (if tr then tload slot s else sload slot s)
                                else n2w cnt) /\
    ~t.vs_halted /\ t.vs_current_bb = sl.cs_current_bb /\
    t.vs_inst_idx = LENGTH sl.cs_current_insts /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    (!x. len = Var x ==> not_fresh_at sl x) /\
    array_length_frame sa s G tn t G' tn' /\
    (?raw. run_inst_seq (emitted_insts sa sl) s = OK raw /\
           t = (raw with vs_inst_idx := LENGTH sl.cs_current_insts))
Proof
  reverse (Cases_on `dyn`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[eval_operand_def, op_prov_def, op_taint_def, array_length_frame_def,
           emitted_insts_def, run_inst_seq_def] >>
      (reverse conj_tac >-
        (qpat_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[])) >>
      gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  simp[] >> strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [bop] sa = (len,sl)` by
    (Cases_on `tr` >> fs[slot_loc_def, compile_ptr_load_def]) >>
  drule_then strip_assume_tac loweringShapeRulesTheory.emit_op_facts >>
  gvs[] >> drule_all_then assume_tac slot_length_step >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `?t G' tn'. array_length_loader_ok ctor imm (slot_loc tr) bop
      (if tr then tload slot s else sload slot s) sa (Var out) sl lo ctx fn PG
      s G tn t G' tn'`
  >- (Cases_on `tr` >> gvs[array_length_loader_ok_def, slot_loc_def, compile_ptr_load_def] >>
      metis_tac[]) >>
  drule_all (array_length_joint |> Q.INST [`dyn` |-> `T`] |> SRULE []) >>
  disch_then (qspecl_then [`explicit`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  qexistsl [`t`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_from_no_dead] >>
  qpat_x_assum `array_length_loader_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t G' tn'` mp_tac >>
  Cases_on `tr` >>
  simp[array_length_loader_ok_def, slot_loc_def, compile_ptr_load_def, FUN_EQ_THM] >>
  disch_then strip_assume_tac >>
  `emit_op opc [bop] sa = (Var out,sl)` by
    (qpat_assum `!x. emit_op _ _ x = emit_op opc _ x` (qspec_then `sa` mp_tac) >>
     fs[]) >>
  qpat_assum `emit_op opc _ sa = _`
    (mp_tac o cj 5 o MATCH_MP emitted_insts_emit_op) >>
  simp[mk_inst_def] >> disch_tac >>
  gvs[GSYM mk_inst_def] >>
  (conj_tac
   >- simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
           mk_inst_def, FLOOKUP_UPDATE, pred_setTheory.EXTENSION]) >>
  (conj_tac
   >- (irule step_prov_out_none >> simp[mk_inst_def] >>
       irule out_prov_other_none >> simp[mk_inst_def])) >>
  gvs[array_length_step_ok_def] >>
  qpat_assum `!f G. step_inst_base _ _ = _ /\ _`
    (qspecl_then [`fn`,`G`] strip_assume_tac) >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def]
QED

(* The optional load and the two scalar stages are in one basic block. *)
Theorem slot_emission_cut[local]:
  compile_array_subscript bop iop dyn cnt 1 esz sgn
    (compile_ptr_load ctor imm (slot_loc tr)) sn = (dst,sb) /\
  fn_has_code sn sb fn ==>
  ?len sl sc.
    (if dyn then compile_ptr_load ctor imm (slot_loc tr) bop
      else comp_return (Lit (n2w cnt))) sn = (len,sl) /\
    array_bounds_check iop len sgn sl = ((),sc) /\
    array_elem_ptr bop iop dyn 1 esz sc = (dst,sb) /\
    sn.cs_next_var <= sl.cs_next_var /\
    same_blocks sl sc /\ same_blocks sc sb /\ same_blocks sn sb /\
    sc.cs_current_insts = sl.cs_current_insts ++ emitted_insts sl sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
    fn_has_code sn sl fn /\ fn_has_code sl sc fn /\ fn_has_code sc sb fn /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                ~is_terminator i.inst_opcode) (emitted_insts sl sc) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                ~is_terminator i.inst_opcode) (emitted_insts sc sb) /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sb)
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sl = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >>
  drule_then strip_assume_tac slot_bounds_layout >>
  drule_then strip_assume_tac slot_address_layout >>
  `same_blocks sn sl /\
   sl.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sl /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sl) /\
   sn.cs_next_var <= sl.cs_next_var` by
    (Cases_on `dyn` >> Cases_on `tr` >>
     gvs[slot_loc_def, compile_ptr_load_def, comp_return_def] >>
     imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
     simp[same_blocks_def, emitted_insts_def, mk_inst_def,
          DROP_LENGTH_APPEND]) >>
  `cs_extends sn sl /\ cs_extends sl sc /\ cs_extends sc sb` by
    fs[cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  `cs_extends sl sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sn sl fn /\ fn_has_code sl sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code sl sc fn /\ fn_has_code sc sb fn` by metis_tac[fn_has_code_split] >>
  `emitted_insts sn sc = emitted_insts sn sl ++ emitted_insts sl sc` by
    metis_tac[emitted_insts_append] >>
  `sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc` by simp[APPEND_ASSOC] >>
  `emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
    metis_tac[emitted_insts_append] >>
  simp[listTheory.EVERY_APPEND, APPEND_ASSOC] >>
  metis_tac[same_blocks_trans]
QED

(* Keep the load and scalar itineraries on the same witnesses as the post. *)
Theorem subscript_slot_array_execution_run:
  compile_array_subscript bop iop dyn cnt 1 (type_slot_size etv) sgn
    (compile_ptr_load ctor imm (slot_loc tr)) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME slot /\ eval_operand iop u = SOME iw /\
  nw = (if dyn then (if tr then tload slot u else sload slot u) else n2w cnt) /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (dyn ==> key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}) /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q,H,tm)) /\
    (idx_in_range sgn iw nw ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
      eval_operand dst q = SOME
        ((if dyn then slot + 1w else slot) + iw * n2w (type_slot_size etv)) /\
      op_prov H dst = op_prov G bop /\ op_taint tm dst = {} /\
      array_length_frame sn u G tn q H tm) /\
    (?len sl sc ul Gl tl raw.
      (if dyn then compile_ptr_load ctor imm (slot_loc tr) bop
       else comp_return (Lit (n2w cnt))) sn = (len,sl) /\
      array_bounds_check iop len sgn sl = ((),sc) /\
      array_elem_ptr bop iop dyn 1 (type_slot_size etv) sc = (dst,sb) /\
      run_inst_seq (emitted_insts sn sl) u = OK raw /\
      ul = (raw with vs_inst_idx := LENGTH sl.cs_current_insts) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) [] (OK ul,Gl,tl)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (ul,Gl,tl) []
        (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q,H,tm)) /\
      (if idx_in_range sgn iw nw then
         ?checked addr. run_inst_seq (emitted_insts sl sc) ul = OK checked /\
           run_inst_seq (emitted_insts sc sb)
             (checked with vs_inst_idx := LENGTH sc.cs_current_insts) = OK addr /\
           q = (addr with vs_inst_idx := LENGTH sb.cs_current_insts)
       else ?aborted. array_abort_itinerary (emitted_insts sl sc) fn ul
                       Revert_abort aborted q))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac slot_emission_cut >>
  drule_all slot_length_stage_run >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename [ `array_length_frame sn u G tn ul Gl tl` ] >>
  `(!x. bop = Var x ==> not_fresh_at sl x) /\
   (!x. iop = Var x ==> not_fresh_at sl x)` by metis_tac[not_fresh_at_mono] >>
  `eval_operand bop ul = SOME slot /\ eval_operand iop ul = SOME iw /\
   op_prov Gl bop = op_prov G bop /\ op_prov Gl iop = NONE /\
   op_taint tl bop = {} /\ op_taint tl iop = {} /\ allocas_from lo ul` by
    (Cases_on `bop` >> Cases_on `iop` >>
     gvs[array_length_frame_def, eval_operand_def, op_prov_def, op_taint_def] >>
     qpat_x_assum `ul with <|vs_vars := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality, allocas_from_def] >>
     metis_tac[allocas_from_def]) >>
  `eval_operand len ul = SOME nw` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ul` by
    (qpat_assum `array_length_frame _ u _ _ ul _ _`
       (strip_assume_tac o SRULE [] o Q.AP_TERM `\st. (st.vs_allocas, st.vs_initial_fmp, st.vs_fmp)` o
        cj 1 o REWRITE_RULE [array_length_frame_def]) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all array_tail_scalar_uniform_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`H`,`tm`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  reverse conj_tac
  >- (qexistsl [`len`,`sl`,`sc`,`ul`,`Gl`,`tl`,`raw`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> strip_tac >>
  `array_length_frame sn u G tn t H tm` by
    (fs[array_length_frame_def, lookup_var_def] >>
     conj_tac >- gvs[venom_state_component_equality] >>
     rpt strip_tac >>
     `not_fresh_at sl x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!y. not_fresh_at sl y ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!y. not_fresh_at sn y ==> _` (qspec_then `x` mp_tac) >>
     simp[] >> metis_tac[]) >>
  simp[] >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_current_bb = u.vs_current_bb` by
    (qpat_assum `array_length_frame sn u G tn t H tm`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [array_length_frame_def]) >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  fs[IS_PREFIX_APPEND] >>
  `t.vs_inst_idx = u.vs_inst_idx + LENGTH (emitted_insts sn sb)` by
    (qpat_assum `sb.cs_current_insts = sn.cs_current_insts ++ _`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `alloca_history fn (t with vs_inst_idx := t.vs_inst_idx)` suffices_by simp[] >>
  qpat_assum `t.vs_inst_idx = u.vs_inst_idx + _` SUBST1_TAC >>
  irule alloca_history_no_alloca_slice >> simp[] >> qexistsl [`bb`,`l`] >> simp[]
QED

Theorem subscript_slot_array_execution:
  compile_array_subscript bop iop dyn cnt 1 (type_slot_size etv) sgn
    (compile_ptr_load ctor imm (slot_loc tr)) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME slot /\ eval_operand iop u = SOME iw /\
  nw = (if dyn then (if tr then tload slot u else sload slot u) else n2w cnt) /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (dyn ==> key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}) /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q,H,tm)) /\
    (idx_in_range sgn iw nw ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
      eval_operand dst q = SOME
        ((if dyn then slot + 1w else slot) + iw * n2w (type_slot_size etv)) /\
      op_prov H dst = op_prov G bop /\ op_taint tm dst = {} /\
      array_length_frame sn u G tn q H tm)
Proof
  strip_tac >> drule_all subscript_slot_array_execution_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`q`,`H`,`tm`] >> simp[]
QED
