Theory bodyPtrPopTargetSimArraySlot
Ancestors
  bodyPtrPopTargetSimArrayCase bodyPtrPopTargetSimStorageHeader
  augAssignPtrStorageFieldLoad emitHelperProps exprLoweringProps
  emitHelper compileEnv venomState ptrDiscipline finite_map arithmetic
  exprSimWordBuiltins fragGasPathPtr exprSimCopy list fragExec stmtReasonLitFragMemory
  bodyPtrPopTargetSimArrayGuard

Theorem target_slot_header_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [addr] sa = (Var out,sl) /\
  fn_has_code sa sl fn /\ fresh_vars_wrt sa s /\
  eval_operand addr s = SOME slot /\ op_prov G addr = NONE /\ op_taint tn addr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK r) /\
    fresh_vars_wrt sl r /\
    eval_operand (Var out) r = SOME (if tr then tload slot s else sload slot s) /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op r = SOME w) /\
    op_prov H (Var out) = NONE /\ op_taint un (Var out) = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
    r.vs_current_bb = sl.cs_current_bb /\ r.vs_inst_idx = LENGTH sl.cs_current_insts /\
    ~r.vs_halted /\
    r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH sl.cs_current_insts|>
Proof
  strip_tac >> drule_all emit_storage_address_load_clean_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[eval_operand_def] >>
  `out = STRING #"%" (toString sa.cs_next_var) /\
   sa.cs_next_var < sl.cs_next_var` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def]) >>
  conj_tac
  >- (qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
      irule fresh_vars_wrt_advance >> simp[fresh_vars_wrt_def] >>
      qexists_tac `sa` >> fs[fresh_vars_wrt_def]) >>
  conj_tac
  >- (Cases_on `op` >> simp[eval_operand_def] >> rpt strip_tac >>
      rename1 `lookup_var x s = SOME w` >>
      `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
      `not_fresh_at sa x` by metis_tac[fresh_vars_wrt_not_fresh_at] >>
      metis_tac[]) >>
  qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >> simp[update_var_def]
QED

Theorem target_dynamic_slot_array_path_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (Var out,sl) /\
  array_bounds_check idx (Var out) sgn sl = ((),sm) /\
  array_elem_ptr bop idx T 1 esz sm = (dst,sb) /\
  fn_has_code sa sl fn /\ fn_has_code sl sb fn /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i (if tr then tload b s else sload b s) /\
  op_prov G bop = NONE /\ op_taint tn bop = {} /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) b = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    eval_operand dst t = SOME ((b+1w)+i*n2w esz) /\
    op_prov H dst = NONE /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
    fresh_vars_wrt sb t /\ copy_old_operand sb dst /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>
Proof
  strip_tac >> drule_all target_slot_header_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand bop r = SOME b /\ eval_operand idx r = SOME i` by metis_tac[] >>
  `op_prov H idx = NONE /\ op_taint un idx = {} /\
   op_taint un bop = {} /\ op_prov H bop = NONE` by
    (`copy_old_operand sa idx /\ copy_old_operand sa bop` by
       (simp[copy_old_operand_def] >> metis_tac[fresh_vars_wrt_not_fresh_at]) >>
     Cases_on `idx` >> Cases_on `bop` >>
     fs[copy_old_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `sb.cs_current_insts = sl.cs_current_insts ++
       (emitted_insts sl sm ++ emitted_insts sm sb) /\
   sb.cs_current_bb = sl.cs_current_bb` by fs[same_blocks_def, APPEND_ASSOC] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sl sm ++ emitted_insts sm sb)
     (DROP r.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all target_array_guarded_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> suspend "finish"
QED

Resume target_dynamic_slot_array_path_ptr[finish]:
  `emitted_insts sl sb = emitted_insts sl sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `r.vs_inst_idx + LENGTH (emitted_insts sl sb) = LENGTH sb.cs_current_insts` by
    (gs[] >> decide_tac) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_x_assum `t = r with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms] >> asm_rewrite_tac[] >> simp[NoAsms]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sl x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def]) >>
  qexistsl_tac [`t`, `H'`, `un'`] >> simp[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s (0+0) H' un' (OK t)` by
    (irule gas_path_ptr_then >> qexistsl_tac [`H`, `r`, `un`] >> simp[]) >> fs[]
QED

Finalise target_dynamic_slot_array_path_ptr

Theorem target_dynamic_slot_array_abort_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (Var out,sl) /\
  array_bounds_check idx (Var out) sgn sl = ((),sm) /\
  fn_has_code sa sl fn /\ fn_has_code sl sm fn /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i (if tr then tload b s else sload b s) /\
  op_prov G bop = NONE /\ op_taint tn bop = {} /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) b = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
      (Abort Revert_abort (t with vs_inst_idx := pc)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all target_slot_header_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand idx r = SOME i` by metis_tac[] >>
  `op_prov H idx = NONE /\ op_taint un idx = {}` by
    (`copy_old_operand sa idx` by
       (simp[copy_old_operand_def] >> metis_tac[fresh_vars_wrt_not_fresh_at]) >>
     Cases_on `idx` >> fs[copy_old_operand_def, op_prov_def, op_taint_def]) >>
  drule target_array_guard_layout >> strip_tac >>
  `sm.cs_current_bb = sl.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sl sm) (DROP r.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all target_bounds_check_abort_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H'`, `un'`, `fuel`, `pc`] >> simp[] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+fuel) H' un'
        (Abort Revert_abort (t with vs_inst_idx := pc))` by
        (irule gas_path_ptr_then >> qexistsl_tac [`H`, `r`, `un`] >> simp[]) >> fs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sl x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def]) >>
  fs[op_taint_def] >> metis_tac[]
QED
