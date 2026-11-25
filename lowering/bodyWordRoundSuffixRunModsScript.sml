(* Physical Ceil/Floor suffix, independent of the source and immutable frame. *)
Theory bodyWordRoundSuffixRunMods
Ancestors
  bodyFullBuiltinWordRounding augAssignPtrScalarRun fragGasCopySeqLiftProps
  allocaHistoryFragment builtinMisc builtinSimple emitHelper emitHelperProps
  fragGasSeqPtr fragExec freshWrites instIdxIndep instMemFrontier
  exprLoweringProps augAssignPtrScalarCertificate exprSimWordBuiltins
  ptrDiscipline loweringStateRelDefs compileEnv venomInst venomState
  vyperAST list rich_list finite_map pred_set

Theorem rounding_static_scalar[local]:
  (bt = Ceil \/ bt = Floor) /\
  (if bt = Ceil then compile_ceil x n else compile_floor x n) sa = (op,sb) /\
  (!l. x <> Label l) ==>
  scalar_code {v | x = Var v} (emitted_insts sa sb) /\
  ?p. op = Var p /\ MEM p (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))
Proof
  Cases_on `bt = Ceil` >> simp[] >>
  simp[compile_ceil_def, compile_floor_def, compile_select_def, comp_bind_def,
       emit_op_def, fresh_var_def, fresh_id_def, comp_ignore_bind_def,
       comp_return_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  Cases_on `x` >>
  gvs[scalar_code_def, scalar_shape_def, scalar_binary_def,
      scalar_available_def, mk_inst_def]
QED

Theorem rounding_straight_fresh[local]:
  (bt = Ceil \/ bt = Floor) /\
  (if bt = Ceil then compile_ceil x n else compile_floor x n) sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  writes_fresh sa (emitted_insts sa sb)
Proof
  Cases_on `bt = Ceil` >> simp[] >>
  metis_tac[straight_fresh_def, straight_fresh_ceil, straight_fresh_floor]
QED

Theorem rounding_sequence_opcodes[local]:
  (bt = Ceil \/ bt = Floor) /\
  (if bt = Ceil then compile_ceil x n else compile_floor x n) sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac rounding_suffix_opcodes >>
  simp[FILTER_EQ_NIL, GSYM EVERY_MEM] >>
  `!P. EVERY P (MAP (\i. i.inst_opcode) (emitted_insts sa sb)) =
       EVERY P [SLT; if bt = Ceil then ADD else SUB; XOR; MUL; XOR; SDIV]` by simp[] >>
  qpat_x_assum `!P. _` (assume_tac o BETA_RULE o REWRITE_RULE [EVERY_MAP]) >>
  Cases_on `bt = Ceil` >> simp[is_terminator_def]
QED

Theorem word_rounding_suffix_run:
  (bt = Ceil \/ bt = Floor) /\
  (if bt = Ceil then compile_ceil x 10000000000 else compile_floor x 10000000000)
    s1 = (op,sb) /\
  eval_operand x t = SOME w /\ (!l. x <> Label l) /\
  (!v. x = Var v ==> not_fresh_at s1 v) /\
  op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  ~t.vs_halted /\ fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  alloca_history func t /\ alloca_inv t ==>
  ?u z G' tn'.
    run_inst_seq (emitted_insts s1 sb) t = OK u /\
    u = (t with vs_vars := u.vs_vars) /\
    z = (u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts s1 sb)) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\
    eval_operand op z = SOME (safe_sdiv
      (if bt = Ceil then (if word_lt w 0w then w else w + n2w (10000000000 - 1))
       else (if word_lt w 0w then w - n2w (10000000000 - 1) else w))
      (n2w 10000000000)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    (!v. not_fresh_at s1 v ==>
      lookup_var v z = lookup_var v t /\ FLOOKUP G' v = FLOOKUP G1 v /\
      op_taint tn' (Var v) = op_taint tn1 (Var v)) /\
    tn'.t_mem = tn1.t_mem /\ tn'.t_stor = tn1.t_stor /\
    tn'.t_trans = tn1.t_trans /\ tn'.t_imm = tn1.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G1,tn1) [] (OK z,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac rounding_static_scalar >>
  drule_all_then strip_assume_tac rounding_straight_fresh >>
  drule_all_then strip_assume_tac rounding_sequence_opcodes >>
  drule_all_then (qx_choose_then `u` strip_assume_tac) word_rounding_run_nonfresh >>
  drule_all_then strip_assume_tac run_inst_seq_writes_fresh >>
  qabbrev_tac `code = emitted_insts s1 sb` >>
  qabbrev_tac `avail = {v | x = Var v}` >>
  `scalar_code avail code` by simp[Abbr `avail`] >>
  `!v. v IN avail ==> op_prov G1 (Var v) = NONE /\ op_taint tn1 (Var v) = {}` by
    (simp[Abbr `avail`] >> rpt strip_tac >> gvs[]) >>
  `?G' tn'. inst_seq_ptr (ARB:dead) 0 ctx func PG G1 tn1 code t G' tn'` by
    (irule scalar_code_inst_seq_ptr >> simp[] >> qexists_tac `avail` >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G1 tn1 code t G' tn'` by
    (gen_tac >>
     `?H tm. inst_seq_ptr D lo ctx func PG G1 tn1 code t H tm` by
       (irule scalar_code_inst_seq_ptr_lo >> simp[] >> qexists_tac `avail` >> simp[]) >>
     `inst_seq_ptr (ARB:dead) lo ctx func PG G1 tn1 code t G' tn'` by
       (irule inst_seq_ptr_lower_bound_transport >> simp[] >> qexists_tac `0` >> simp[]) >>
     `H = G' /\ tm = tn'` by
       (irule inst_seq_ptr_ghost_unique >>
        qpat_assum `inst_seq_ptr D lo _ _ _ _ _ _ _ H tm` (irule_at Any) >>
        qpat_assum `inst_seq_ptr (ARB:dead) lo _ _ _ _ _ _ _ G' tn'` (irule_at Any)) >>
     gvs[]) >>
  `op_prov G' (Var p) = NONE /\ op_taint tn' (Var p) = {}` by
    (irule scalar_seq_success_clean >>
     qpat_assum `inst_seq_ptr (ARB:dead) 0 _ _ _ _ _ _ _ G' tn'` (irule_at Any) >>
     qpat_assum `run_inst_seq code t = OK u` (irule_at Any) >>
     qpat_assum `scalar_code avail code` (irule_at Any) >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     fs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `!v. not_fresh_at s1 v ==> ~MEM v (FLAT (MAP (\i. i.inst_outputs) code))` by
    (rpt strip_tac >> fs[writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  drule_all_then strip_assume_tac scalar_seq_metadata_frame_lo >>
  `?bb rest. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    DROP t.vs_inst_idx bb.bb_instructions = code ++ rest` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     metis_tac[DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  qabbrev_tac `z = u with vs_inst_idx := t.vs_inst_idx + LENGTH code` >>
  `alloca_history func z` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
     drule_all alloca_history_run_inst_seq >> simp[Abbr `z`]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (t,G1,tn1) [] (OK z,G',tn')` by
    (rpt gen_tac >>
     `run_inst_seq_mem_ok code t` by
       (drule_all rounding_suffix_mem_ok >> simp[Abbr `code`]) >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         code = pre ++ i::post /\ run_inst_seq pre t = OK u ==>
         unitTransformDefs$dalloca_no_wrap i u)` by
       (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
        `MEM i code` by (qpat_x_assum `code = pre ++ i::post` SUBST1_TAC >> simp[MEM_APPEND]) >>
        fs[EVERY_MEM]) >>
     `inst_seq_ptr D lo ctx func PG G1 tn1 code t G' tn'` by simp[] >>
     `isPREFIX code (DROP t.vs_inst_idx bb.bb_instructions)` by simp[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `z`]) >>
  qexistsl_tac [`u`,`z`,`G'`,`tn'`] >>
  simp[Abbr `z`, eval_operand_inst_idx, lookup_var_def] >>
  qpat_assum `u = (t with vs_vars := _)` (fn th => once_rewrite_tac[th]) >> simp[]
QED
