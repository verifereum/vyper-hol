Theory bodyPtrPopTargetSimArrayCase
Ancestors
  bodyPtrPopTargetSimArrayRun bodyPtrPopTargetSimArrayGuard exprSimArrayIndex
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopInLiteralSuffix
  exprSimWordBuiltins bodyPtrHashBuiltinsShaAlloc entrySinkExtraction
  emitHelperProps exprLoweringProps compileEnv emitHelper venomState venomInst
  fragGasPathPtr fragGasSeqPtr fragExec exprSimCopy ptrDiscipline finite_map list arithmetic

Theorem target_array_guard_layout:
  array_bounds_check idx len sgn sa = ((),sm) ==>
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  same_blocks sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sm)
Proof
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  Cases_on `sgn` >> simp[comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _`
    kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
       mk_inst_def, is_terminator_def]
QED

Theorem target_array_guarded_path_ptr:
  array_bounds_check idx len sgn sa = ((),sm) /\
  array_elem_ptr bop idx dyn ws esz sm = (dst,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  eval_operand len s = SOME n /\ fresh_vars_wrt sa s /\ idx_in_range sgn i n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\ op_taint tn bop = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
           (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    eval_operand dst t = SOME ((if dyn then b+n2w ws else b)+i*n2w esz) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule hash_code_prefix_split >> strip_tac >>
  drule_all target_bounds_check_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all array_bounds_check_ok >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  drule target_array_guard_layout >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm)` by gvs[EVERY_CONJ] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand bop u = SOME b /\ eval_operand idx u = SOME i /\
   copy_old_operand sm bop /\ copy_old_operand sm idx` by
    (simp[Abbr `u`, copy_old_operand_def] >>
     metis_tac[fresh_vars_wrt_not_fresh_at]) >>
  `op_prov H bop = op_prov G bop /\ op_taint un bop = {} /\
   op_prov H idx = NONE /\ op_taint un idx = {}` by
    (`copy_old_operand sa bop /\ copy_old_operand sa idx` by
       (simp[copy_old_operand_def] >> metis_tac[fresh_vars_wrt_not_fresh_at]) >>
     Cases_on `bop` >> Cases_on `idx` >>
     gvs[copy_old_operand_def, op_prov_def, op_taint_def]) >>
  `~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `u`] >>
  drule_all target_array_elem_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "finish"
QED

Resume target_array_guarded_path_ptr[finish]:
  qexistsl_tac [`t' with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sm sb)`,
                `H'`, `un'`] >>
  simp[] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) H' un'
        (OK (t' with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sm sb)))` by
       (irule gas_path_ptr_then >> qexistsl_tac [`H`, `u`, `un`] >>
        simp[Abbr `u`]) >> fs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  gvs[op_taint_def] >> metis_tac[]
QED

Finalise target_array_guarded_path_ptr

Theorem target_array_elem_layout:
  array_elem_ptr bop idx dyn ws esz sa = (dst,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  simp[array_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `dyn` >> gvs[comp_return_def] >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_op >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _`
    kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC]
QED

Theorem target_fixed_array_path_ptr:
  compile_array_subscript bop idx F cnt ws esz sgn loader sa = (dst,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i (n2w cnt) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\ op_taint tn bop = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    eval_operand dst t = SOME (b+i*n2w esz) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sa = (u,sm)` >> Cases_on `u` >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt) /\
   op_prov G (Lit (n2w cnt)) = NONE /\ op_taint tn (Lit (n2w cnt)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  `isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all target_array_guarded_path_ptr >> simp[]
QED

Theorem target_fixed_array_abort_ptr:
  compile_array_subscript bop idx F cnt ws esz sgn loader sa = (dst,sb) /\
  eval_operand idx s = SOME i /\ fresh_vars_wrt sa s /\
  ~idx_in_range sgn i (n2w cnt) /\ op_prov G idx = NONE /\ op_taint tn idx = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
      (Abort Revert_abort (t with vs_inst_idx := pc)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sa = (u,sm)` >> Cases_on `u` >>
  drule target_array_guard_layout >> strip_tac >>
  drule target_array_elem_layout >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule hash_code_prefix_split >> strip_tac >>
  `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt) /\
   op_prov G (Lit (n2w cnt)) = NONE /\ op_taint tn (Lit (n2w cnt)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all target_bounds_check_abort_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `un`, `fuel`, `pc`] >> gvs[op_taint_def]
QED
