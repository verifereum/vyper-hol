(* Linked normal LOG step after a prepared fixed-data window. *)
Theory bodyRawLogFixedEmitMods
Ancestors
  bodyFullRawLogFixedTailPath bodyForRangeScalarFrameMods bodyFullLogSuffix
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit rawLogCoreFrame
  fragGasSeqPtr fragGasOriginPtr rawLogPtrInst emitHelper emitHelperProps fragExec
  ptrDiscipline venomState venomInst venomExecSemantics
  bodyPtrDefs compileEnv exprLoweringProps loweringStateRelDefs
  vyperEvent valueEncoding valueEncodingDefs valueEncodingProps words list rich_list
  finite_map pred_set arithmetic

Theorem raw_log_fixed_emit_mods:
  !D lo explicit ctx func PG cenv cx ee z G tf s1 sb p buf ops vals bs off ev.
    ~cx.txn.is_static /\
    ~z.vs_call_ctx.cc_static /\
    z.vs_call_ctx.cc_address = cx.txn.target /\
    buf = Var p /\
    emit_inst LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf]) [] s1 = ((),sb) /\
    fn_has_code s1 sb func /\
    LENGTH ops < dimword (:256) /\
    eval_operands ops z = SOME (MAP event_value_to_word vals) /\
    eval_operand buf z = SOME off /\
    ptr_covers G tf p z 32 /\
    EVERY (\op. op_taint tf op = {}) ops /\
    op_taint tf buf = {} /\
    (!i. w2n off <= i /\ i < w2n off + 32 ==> i NOTIN tf.t_mem) /\
    w2n off + 32 <= z.vs_alloca_next /\
    allocas_from lo z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    stor_taint_ok_at D tf z /\
    lo <= z.vs_alloca_next /\
    ~z.vs_halted /\
    z.vs_current_bb = s1.cs_current_bb /\
    z.vs_inst_idx = LENGTH s1.cs_current_insts /\
    mem_bytes_at (w2n off) 32 z.vs_memory = bs /\
    ev = encode_raw_event_values cx.txn.target vals bs /\
    immutable_frame_mods func cenv cx ee z /\
    ghost_inv_at_mods D lo d cenv cx ee G tf z ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tf) []
      (OK (z with <|vs_logs := z.vs_logs ++ [ev];
                         vs_inst_idx := LENGTH sb.cs_current_insts|>),G,tf) /\
    (z with <|vs_logs := z.vs_logs ++ [ev];
               vs_inst_idx := LENGTH sb.cs_current_insts|>).vs_current_bb = sb.cs_current_bb /\
    immutable_frame_mods func cenv cx
      (ee with logs := ee.logs ++ [ev])
      (z with <|vs_logs := z.vs_logs ++ [ev];
                vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    ghost_inv_at_mods D lo d cenv cx
      (ee with logs := ee.logs ++ [ev]) G tf
      (z with <|vs_logs := z.vs_logs ++ [ev];
                vs_inst_idx := LENGTH sb.cs_current_insts|>)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst s1.cs_next_id LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf]) []` >>
  qabbrev_tac `u = z with <|vs_logs := z.vs_logs ++ [ev];
    vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
  `i.inst_opcode = LOG /\
   i.inst_operands = Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf] /\
   i.inst_outputs = []` by simp[Abbr `i`, mk_inst_def] >>
  `inst_extends s1 sb` by
    (qpat_assum `emit_inst LOG _ _ _ = _`
      (ACCEPT_TAC o MATCH_MP emitHelperPropsTheory.inst_extends_emit_inst)) >>
  `lookup_var p z = SOME off` by
    gvs[eval_operand_def] >>
  `step_inst_base i z = OK (z with vs_logs := z.vs_logs ++
      [<|logger := z.vs_call_ctx.cc_address;
        topics := MAP event_value_to_word vals; data := bs|>])` by
    (`eval_operand (Lit 32w) z = SOME 32w` by simp[eval_operand_def] >>
     drule_all stmtSimLogEmitTheory.log_emit_step >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, dimword_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tf i z` by
    (simp[Abbr `i`] >> irule (SRULE [] raw_log_fixed_log_inst_ok) >>
     simp[mk_inst_def] >>
     gvs[ptr_covers_def, eval_operand_def, op_taint_def,
         allocas_from_def, stor_taint_ok_at_def] >>
     qexists `z with vs_logs := z.vs_logs ++
       [<|logger := z.vs_call_ctx.cc_address;
          topics := MAP event_value_to_word vals;
          data := mem_bytes_at (w2n off) 32 z.vs_memory|>]` >>
     qpat_assum `step_inst_base _ z = OK _`
       (fn th => simp[REWRITE_RULE [mk_inst_def] th])) >>
  `inst_mem_below_frontier i z /\ inst_dload_in_section i z` by
    (simp[Abbr `i`, unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.memory_range_of_operands_def, mk_inst_def,
          rich_listTheory.REVERSE_APPEND, eval_operand_def,
          lookup_var_def, dimword_def,
          memSafeRunTheory.inst_dload_in_section_other] >>
     gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> dalloca_no_wrap i z` by
    simp[Abbr `i`, mk_inst_def,
      memSafeRunTheory.dalloca_no_wrap_non_dalloca] >>
  `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb z.vs_inst_idx = SOME i` by
    (qpat_assum `fn_has_code s1 sb func` mp_tac >>
     gvs[fragExecTheory.fn_has_code_def] >>
     `sb.cs_current_insts = s1.cs_current_insts ++ [i]` by
       (qpat_assum `emit_inst LOG _ _ s1 = ((),sb)` mp_tac >>
        drule emitHelperPropsTheory.emit_inst_extends >>
        simp[Abbr `i`]) >>
     `sb.cs_current_bb = s1.cs_current_bb` by
       (qpat_assum `emit_inst LOG _ _ s1 = ((),sb)` mp_tac >>
        drule emitHelperPropsTheory.emit_inst_extends >>
        metis_tac[]) >>
     qexists `bb` >>
     conj_tac
     >- (qpat_assum `z.vs_current_bb = s1.cs_current_bb` mp_tac >>
         qpat_assum `lookup_block sb.cs_current_bb func.fn_blocks = SOME bb` mp_tac >>
         metis_tac[]) >>
     qpat_assum `z.vs_inst_idx = LENGTH s1.cs_current_insts` mp_tac >>
     qpat_assum `sb.cs_current_insts ≼ bb.bb_instructions`
       (fn h => mp_tac (REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND] h)) >>
     disch_then (qx_choose_then `tail` strip_assume_tac) >>
     simp[get_instruction_def, listTheory.EL_APPEND_EQN]) >>
  `step_prov PG G i
      (z with vs_logs := z.vs_logs ++
       [<|logger := w2w z.vs_call_ctx.cc_address;
         topics := MAP event_value_to_word vals; data := bs|>]) = G /\
   step_taint i z
      (z with vs_logs := z.vs_logs ++
       [<|logger := w2w z.vs_call_ctx.cc_address;
         topics := MAP event_value_to_word vals; data := bs|>]) tf = tf` by
    simp[Abbr `i`, rawLogPtrInstTheory.log_ghost] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (z,G,tf) []
      (OK ((z with vs_logs := z.vs_logs ++
          [<|logger := w2w z.vs_call_ctx.cc_address;
            topics := MAP event_value_to_word vals; data := bs|>]) with
          vs_inst_idx := SUC z.vs_inst_idx), G, tf)` by
    (qpat_assum `step_inst_base _ _ = OK _`
       (mp_then Any mp_tac straight_line_origin_ptr_edge) >>
     simp[Abbr `i`, rawLogPtrInstTheory.log_ghost,
          venomInstTheory.is_terminator_def] >>
     disch_then irule >> simp[] >>
     conj_tac
     >- (qexists `bb` >>
         qpat_assum `buf = Var p` mp_tac >>
         disch_then assume_tac >> gvs[])
     >> qpat_assum `buf = Var p` mp_tac >>
        disch_then assume_tac >> gvs[]) >>
  `LENGTH sb.cs_current_insts = SUC z.vs_inst_idx` by
    (qpat_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     drule emitHelperPropsTheory.emit_inst_extends >>
     simp[emitHelperTheory.emit_inst_def, compileEnvTheory.emit_def,
          compileEnvTheory.fresh_id_def, Abbr `i`, mk_inst_def] >>
     metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tf) [] (OK u,G,tf)` by
    (`gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (z,G,tf) []
        (OK u,G,tf)` by
       gvs[Abbr `u`, encode_raw_event_values_def,
           vyperEventTheory.encode_raw_event_def] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tf) []
        (OK u,G,tf)` by
       (irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`]) >>
     drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  `u.vs_current_bb = sb.cs_current_bb` by
    (drule emitHelperPropsTheory.emit_inst_extends >> simp[Abbr `u`]) >>
  qabbrev_tac `ef = ee with logs := ee.logs ++ [ev]` >>
  `immutable_frame_mods func cenv cx ef u <=>
   immutable_frame_mods func cenv cx ee z` by
    (qpat_x_assum `immutable_frame_mods _ _ _ ee z` kall_tac >>
     simp[Abbr `u`, Abbr `ef`, immutable_frame_mods_def, immutables_rel_mods_def,
          immutables_rel_def, immutable_alloca_sep_mods_def,
          immutable_alloca_sep_def, local_region_def, lookup_var_def]) >>
  `ghost_inv_at_mods D lo d cenv cx ef G tf u <=>
   ghost_inv_at_mods D lo d cenv cx ee G tf z` by
    (qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ ee _ _ z` kall_tac >>
     qpat_x_assum `allocas_from lo z` kall_tac >>
     qpat_x_assum `stor_taint_ok_at D tf z` kall_tac >>
     qpat_x_assum `lo <= z.vs_alloca_next` kall_tac >>
     Cases_on `d`
     >- simp[Abbr `u`, Abbr `ef`, ghost_inv_at_mods_def, ptr_covers_def,
             stor_taint_ok_at_def, lookup_var_def, allocas_from_def, return_buf_ptr_def] >>
     PairCases_on `x` >>
     simp[Abbr `u`, Abbr `ef`, ghost_inv_at_mods_def, ptr_covers_def,
          stor_taint_ok_at_def, lookup_var_def, allocas_from_def, return_buf_ptr_def]) >>
  simp[]
QED
