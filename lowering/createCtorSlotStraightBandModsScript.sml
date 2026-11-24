(* The two straight fragments of a slot unwrap: ALLOCA and the single-slot copy. *)
Theory createCtorSlotStraightBandMods
Ancestors
  createCtorStraightBand createCtorSlotLoopOriginBand
  bodyFullUnwrapSlotOrigin exprPtrUnwrapSingleSegment abiBufferAllocationCode
  stmtReasonLitFragMemory exprSimStorageCopy copyExecution allocaHistory
  compileEnv emitHelper venomExecSemantics venomInst venomMemProofs
  fragExec exprLoweringProps loweringStateRelDefs venomState bodyBinopFragMemory
  finite_map words
  relation rich_list arithmetic list

Theorem ctor_slot_alloc_band_mods:
  compile_alloc_buffer nb sa = (buf,mid) /\ fn_has_code sa mid func /\
  buf.buf_operand = Var root /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sa.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  qpat_assum `buf.buf_operand = Var root` mp_tac >> simp[] >> strip_tac >>
  `LENGTH (emitted_insts sa mid) = 1` by simp[] >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sa.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa mid))` by
    (irule ctor_straight_band_run >>
     reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> gvs[]) >>
     fs[run_inst_seq_def,mk_inst_def,is_terminator_def]) >>
  gvs[ADD1,ADD_COMM]
QED

Theorem ctor_single_slot_band_mods:
  (load = SLOAD \/ load = TLOAD) /\
  (do v <- emit_op load [src]; emit_void MSTORE [Var root; v] od) mid = ((),sc) /\
  fn_has_code mid sc func /\
  eval_operand src a = SOME key /\ op_taint tn src = {} /\
  not_fresh_at mid root /\ ptr_covers G tn root a 32 /\
  lookup_var root a = SOME dst /\ allocas_from lo a /\ w2n dst + 32 <= a.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\ alloca_history func a /\
  ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?Gf tnf z.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G,tn) [] (OK z,Gf,tnf) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
    mid.cs_next_id <= sc.cs_next_id /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ ~z.vs_halted /\ z.vs_alloca_next = a.vs_alloca_next /\
    z = (mstore (w2n dst) (slot_copy_word load a key)
      (update_var (STRING #"%" (toString mid.cs_next_var)) (slot_copy_word load a key) a)
      with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    tnf.t_mem = (tn.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
      {w2n dst+b | b IN key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule storage_copy_word_layout >> strip_tac >>
  `sc.cs_next_id = mid.cs_next_id + 2` by
    (qpat_x_assum `(do v <- _; _ od) _ = _` mp_tac >>
     simp[emit_op_def,emit_void_def,emit_def,fresh_var_def,fresh_id_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[]) >>
  `root <> STRING #"%" (toString mid.cs_next_var)` by simp[] >>
  drule_all unwrap_single_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (a,G,tn) [] (OK z,Gf,tnf)` >>
  suspend "single_band"
QED

Resume ctor_single_slot_band_mods[single_band]:
  `sc.cs_current_bb = mid.cs_current_bb /\
   sc.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid sc` by
    gvs[same_blocks_def,emitted_insts_def,IS_PREFIX_APPEND,DROP_LENGTH_APPEND] >>
  drule_all fn_has_code_code >> strip_tac >>
  `LENGTH sc.cs_current_insts = a.vs_inst_idx + LENGTH (emitted_insts mid sc)` by simp[] >>
  `?t. run_inst_seq (emitted_insts mid sc) a = OK t /\
       z = t with vs_inst_idx := LENGTH sc.cs_current_insts` by
    (drule_all copy_single_slot_segment >>
     disch_then (qspecl_then [`mid.cs_next_id`,`func`,`PG`,`D`] strip_assume_tac) >>
     rename1 `run_inst_seq [_; _] a = OK t` >> qexists_tac `t` >> simp[]) >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z` by
    (qpat_assum `z = t with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `LENGTH sc.cs_current_insts = _` SUBST1_TAC >>
     irule ctor_straight_band_run >>
     reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> gvs[]) >>
     Cases_on `load = SLOAD` >> fs[mk_inst_def,is_terminator_def]) >>
  suspend "single_history"
QED

Resume ctor_single_slot_band_mods[single_history]:
  `z.vs_allocas = a.vs_allocas /\ z.vs_current_bb = a.vs_current_bb /\
   ~z.vs_halted /\ z.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `z = (mstore _ _ _) with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms,mstore_def,write_memory_with_expansion_def,update_var_def] >> simp[]) >>
  `alloca_history func z` by
    (qpat_assum `isPREFIX (emitted_insts mid sc) _`
       (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts mid sc)` by
       (Cases_on `load = SLOAD` >> fs[mk_inst_def]) >>
     `lookup_block a.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     `DROP a.vs_inst_idx bb.bb_instructions = emitted_insts mid sc ++ l` by simp[] >>
     drule_all alloca_history_no_alloca_slice >>
     qpat_assum `LENGTH sc.cs_current_insts = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`z`] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Finalise ctor_single_slot_band_mods
