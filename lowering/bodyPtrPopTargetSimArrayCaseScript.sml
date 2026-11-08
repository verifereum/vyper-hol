Theory bodyPtrPopTargetSimArrayCase
Ancestors
  bodyPtrPopTargetSimArrayRun bodyPtrPopTargetSimArrayGuard exprSimArrayIndex
  bodyPtrPopMemoryHeader stmtReasonLitFragMemory
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

Theorem target_memory_header_runtime:
  emit_op MLOAD [Var src] sa = (Var out,sl) /\
  lookup_var src s = SOME b /\ fresh_vars_wrt sa s ==>
  fresh_vars_wrt sl (update_var out (mload (w2n b) s) s) /\
  (!op w. eval_operand op s = SOME w ==>
     eval_operand op (update_var out (mload (w2n b) s) s) = SOME w)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME b` by simp[eval_operand_def] >>
  drule_all emit_op_MLOAD_correct >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `out = STRING #"%" (toString sa.cs_next_var)` by gvs[] >>
  qpat_x_assum `Var out = _` kall_tac >>
  `run_inst_seq (emitted_insts sa sl) s =
     OK (update_var out (mload (w2n b) s) s)` by
    (qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
     simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          mk_inst_def, venomExecSemanticsTheory.exec_read1_def, eval_operand_def]) >>
  gvs[]
QED

Theorem target_memory_header_path_ptr:
  emit_op MLOAD [Var src] sa = (len,sl) /\ fn_has_code sa sl fn /\
  lookup_var src s = SOME b /\ fresh_vars_wrt sa s /\
  ptr_covers G tn src s bytes /\ 32 <= bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK r) /\
    fresh_vars_wrt sl r /\ eval_operand len r = SOME (mload (w2n b) s) /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op r = SOME w) /\
    op_prov H len = NONE /\ op_taint un len = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x)) /\
    r.vs_current_bb = sl.cs_current_bb /\ r.vs_inst_idx = LENGTH sl.cs_current_insts /\
    ~r.vs_halted
Proof
  strip_tac >> drule_all pop_memory_header_load >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  drule_all target_memory_header_runtime >> strip_tac >>
  qexistsl_tac [`update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n b) s) s
                  with vs_inst_idx := SUC s.vs_inst_idx`, `G'`, `tn'`] >> simp[] >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       fresh_vars_wrt_def, same_blocks_def] >>
  fs[op_taint_def, fresh_vars_wrt_def, same_blocks_def] >> metis_tac[]
QED

Theorem target_dynamic_memory_array_path_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sl) /\
  array_bounds_check idx (Var out) sgn sl = ((),sm) /\
  array_elem_ptr (Var src) idx T 32 esz sm = (dst,sb) /\
  fn_has_code sa sl fn /\ fn_has_code sl sb fn /\
  lookup_var src s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i (mload (w2n b) s) /\
  ptr_covers G tn src s bytes /\ 32 <= bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) mem) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\ op_taint tn (Var src) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H un. gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    eval_operand dst t = SOME ((b+32w)+i*n2w esz) /\
    op_prov H dst = op_prov G (Var src) /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all target_memory_header_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var src) r = SOME b /\ eval_operand idx r = SOME i` by
    metis_tac[eval_operand_def] >>
  `op_prov H idx = NONE /\ op_taint un idx = {} /\
   op_taint un (Var src) = {} /\ op_prov H (Var src) = op_prov G (Var src)` by
    (`copy_old_operand sa idx /\ not_fresh_at sa src` by
       (simp[copy_old_operand_def] >> metis_tac[fresh_vars_wrt_not_fresh_at,
         eval_operand_def]) >>
     Cases_on `idx` >> fs[copy_old_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[]) >>
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
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "finish"
QED

Resume target_dynamic_memory_array_path_ptr[finish]:
  qexistsl_tac [`t`, `H'`, `un'`] >> simp[] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) H' un' (OK t)` by
        (irule gas_path_ptr_then >> qexistsl_tac [`H`, `r`, `un`] >> simp[]) >> fs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sl x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def]) >>
  metis_tac[]
QED

Finalise target_dynamic_memory_array_path_ptr

Theorem target_dynamic_memory_array_abort_ptr:
  emit_op MLOAD [Var src] sa = (len,sl) /\
  array_bounds_check idx len sgn sl = ((),sm) /\
  fn_has_code sa sl fn /\ fn_has_code sl sm fn /\
  lookup_var src s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i (mload (w2n b) s) /\
  ptr_covers G tn src s bytes /\ 32 <= bytes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) mem) /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H un fuel pc. gas_path_ptr D 0 ctx fn PG G tn s fuel H un
      (Abort Revert_abort (t with vs_inst_idx := pc)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all target_memory_header_path_ptr >>
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
