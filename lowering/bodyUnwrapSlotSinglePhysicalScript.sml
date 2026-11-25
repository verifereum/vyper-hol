(* Physical installation and execution of the allocating one-word unwrap. *)
Theory bodyUnwrapSlotSinglePhysical
Ancestors
  bodyFullUnwrapSlotOrigin exprPtrUnwrapAllocEntry exprPtrUnwrapEnsureShape
  exprSimStorageCopy abiBufferAllocationCode exprLoweringProps emitHelperProps
  stmtReasonLitFragMemory bufferAllocationExecution slotCopyExecution
  fragExec fragGasOriginPtr ptrDiscipline logInstSeqPtr words
  venomExecSemantics venomState venomInst finite_map rich_list list

Theorem single_slot_raw_run[local]:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  lookup_var root s = SOME addr /\ root <> out ==>
  run_inst_seq
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []] s =
  OK (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s))
Proof
  strip_tac >> gvs[] >>
  fs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
     exec_read1_def, exec_write2_def, slot_copy_word_def,
     eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem single_slot_installed_list[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sm.cs_next_var = sa.cs_next_var + 1 /\ root = STRING #"%" (toString sa.cs_next_var) /\
  emitted_insts sa sb =
    mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root] ::
    [mk_inst sm.cs_next_id (if loc = LocStorage then SLOAD else TLOAD) [src]
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst (sm.cs_next_id+1) MSTORE
       [Var root; Var (STRING #"%" (toString sm.cs_next_var))] []]
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (pure_rewrite_tac[emitted_insts_def, GSYM prefix_drop_equiv] >>
     first_assum ACCEPT_TAC) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  fs[same_blocks_def, APPEND_ASSOC]
QED

Theorem unwrap_ensure_slot_single_physical:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32 <= nb /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u raw bb.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
      (update_var (STRING #"%" (toString sm.cs_next_var))
        (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
          with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
      {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
    MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
      [ALLOCA; (if loc = LocStorage then SLOAD else TLOAD); MSTORE] /\
    run_inst_seq (emitted_insts sa sb) s = OK raw /\
    t = raw with vs_inst_idx := LENGTH sb.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all unwrap_ensure_slot_origin_single >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,`D`]
    (qx_choosel_then [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`]
       strip_assume_tac)) >>
  drule_all single_slot_installed_list >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  `!x. src = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand src a = SOME p` by metis_tac[unwrap_alloc_old_operand_ghost] >>
  `lookup_var root a = SOME d` by simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `root <> STRING #"%" (toString sm.cs_next_var)` by simp[fresh_var_distinct] >>
  qabbrev_tac `load = if loc = LocStorage then SLOAD else TLOAD` >>
  (Q.SUBGOAL_THEN `load = SLOAD \/ load = TLOAD` assume_tac
   >- (Cases_on `loc = LocStorage` >> simp[Abbr `load`])) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `tail = [mk_inst sm.cs_next_id load [src] [out];
      mk_inst (sm.cs_next_id+1) MSTORE [Var root;Var out] []]` >>
  qabbrev_tac `mid = update_var out (slot_copy_word load a p) a` >>
  `run_inst_seq tail a = OK (mstore (w2n d) (slot_copy_word load a p) mid)` by
    (simp_tac bool_ss [Abbr `tail`, Abbr `mid`] >>
     irule single_slot_raw_run >> asm_rewrite_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) tail` by
    (Cases_on `loc = LocStorage` >> simp[Abbr `tail`, Abbr `load`, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `r = mstore (w2n d) (slot_copy_word load a p) mid` >>
  qabbrev_tac `alloc = mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >>
  `run_inst_seq [alloc] s = OK u` by
    (asm_rewrite_tac[run_inst_seq_def] >> simp[]) >>
  `run_inst_seq ([alloc] ++ tail) s = OK (r with vs_inst_idx := u.vs_inst_idx)` by
    (irule run_inst_seq_append_advanced >>
     simp_tac bool_ss [LENGTH, arithmeticTheory.ADD_CLAUSES, GSYM arithmeticTheory.ADD1] >>
     qpat_assum `a = u with vs_inst_idx := _` (SUBST1_TAC o SYM) >>
     asm_rewrite_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (r with vs_inst_idx := u.vs_inst_idx)` by
    (qpat_assum `run_inst_seq ([alloc] ++ tail) s = _`
       (assume_tac o REWRITE_RULE [APPEND]) >> asm_rewrite_tac[]) >>
  `isPREFIX (alloc::tail) (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (qpat_assum `emitted_insts sa sb = alloc::tail` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `sm.cs_next_var = _` kall_tac >>
  qexistsl_tac [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`,
    `r with vs_inst_idx := u.vs_inst_idx`,`bb`] >>
  unabbrev_all_tac >>
  asm_rewrite_tac[venom_state_fupdfupds] >>
  simp[LENGTH_APPEND, mk_inst_def]
QED
