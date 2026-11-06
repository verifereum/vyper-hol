Theory whitelistS2Shape
Ancestors
  list loweringShapeProps loweringShapeRules loweringShapeDefs
  builtinSystem context compileEnv emitHelper unitShapeDefs venomInst
  exprLowering supportedExprTraverse vyperAST

(* Output capacity is static, including the zero-capacity revert buffer. *)
Theorem compile_raw_call_outbuf_shape:
  !n internal.
    shape_step internal compiler_label (\st. T)
      (compile_raw_call_outbuf n)
      (\buf st. plain_operand st (FST buf) /\ plain_operand st (SND buf))
Proof
  rpt gen_tac >>
  `!(x:operand) (f:operand -> (operand # operand) compiler).
     compileEnv$comp_bind (comp_return x) f = f x` by
    simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  Cases_on `0 < n` >>
  simp[compile_raw_call_outbuf_def] >>
  irule shape_step_bind >> irule_at Any compile_alloc_buffer_shape >>
  qx_gen_tac `buf` >> simp[]
  >- (
    match_mp_tac shape_step_bind >>
    qexists_tac `\op st. plain_operand st buf.buf_operand /\ plain_operand st op` >>
    conj_tac
    >- (
      `shape_stable (\st. plain_operand st buf.buf_operand)` by
        (mp_tac (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands) >> simp[]) >>
      `shape_step internal compiler_label
         (\st. plain_operand st buf.buf_operand /\ plain_operand st buf.buf_operand)
         (emit_op ADD [buf.buf_operand; Lit 32w])
         (\op st. plain_operand st buf.buf_operand /\ plain_operand st op)`
        suffices_by simp[] >>
      ho_match_mp_tac shape_step_frame >> simp[] >>
      irule shape_step_emit_op_pre >>
      simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
           inst_shape_ok_def, label_positions_ok_def, operand_case_not_label,
           inst_jump_labels_ok_def, is_read0_opcode_def, is_terminator_def,
           is_param_opcode_def, plain_operand_def, label_or_plain_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
    gen_tac >> simp[] >> irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[]
QED

Theorem compile_raw_call_finish_base_shape[local]:
  shape_base_step internal compiler_label
    (\st. EVERY (plain_operand st)
      [to_op; data_ptr; data_len; gas_op; value_op; out_val; out_ptr])
    (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
      call_ty max_outsize T out_val out_ptr)
    (\v st. plain_operand st v)
Proof
  simp[compile_raw_call_finish_def] >>
  qmatch_goalsub_abbrev_tac `shape_base_step _ _ P _ _` >>
  `shape_stable P` by
    (simp[Abbr `P`, shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule shape_base_step_bind >>
  qexists_tac `\v st. P st /\ plain_operand st v` >>
  reverse conj_tac
  >- (Cases_on `call_ty` >> simp[] >>
      irule shape_base_step_emit_op_guarded >>
      simp[Abbr `P`, label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
           raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
           inst_jump_labels_ok_def, is_read0_opcode_def,
           is_terminator_def, is_param_opcode_def,
           stackPlanTypesTheory.is_label_operand_def] >>
      rpt strip_tac >> gvs[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `success` >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `shape_base_step _ _ B _ _` >>
  `shape_stable B` by
    (simp[Abbr `B`, shape_stable_def] >>
     metis_tac[shape_stable_def, plain_operand_mono]) >>
  irule shape_base_step_bind >>
  qexists_tac `\l st. B st /\ compiler_label l /\ label_sfx "call_failed" l` >>
  reverse conj_tac
  >- (irule shape_base_step_fresh_label_sfx >> simp[]) >>
  qx_gen_tac `fail_lbl` >> BETA_TAC >>
  irule shape_base_step_bind >>
  qexists_tac `\l st. (B st /\ compiler_label fail_lbl /\
    label_sfx "call_failed" fail_lbl) /\ compiler_label l /\ label_sfx "call_ok" l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_fresh_label_sfx >>
      simp[shape_stable_def] >> metis_tac[shape_stable_def]) >>
  qx_gen_tac `ok_lbl` >> BETA_TAC >>
  suspend "guard"
QED

Resume compile_raw_call_finish_base_shape[guard]:
  qmatch_goalsub_abbrev_tac `shape_base_step _ _ C m Q` >>
  pure_rewrite_tac[shape_base_step_def] >> rpt gen_tac >> strip_tac >>
  fs[Abbr `C`] >>
  `shape_base_step internal compiler_label B m Q` suffices_by
    (simp[shape_base_step_def] >> metis_tac[]) >>
  simp[Abbr `m`, Abbr `Q`] >>
  `ok_lbl <> fail_lbl` by
    (`"call_ok" <> "call_failed"` by EVAL_TAC >>
     metis_tac[label_sfx_distinct]) >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. B st` >> reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_emit_inst_guarded >>
      simp[Abbr `B`, label_or_plain_def, lowered_inst_ok_def,
        mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        label_positions_ok_def, inst_jump_labels_ok_def,
        is_read0_opcode_def, is_terminator_def, is_param_opcode_def,
        stackPlanTypesTheory.is_label_operand_def] >>
      rpt strip_tac >> gvs[plain_operand_def, jump_label_ok_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. B st` >> reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind (new_block ok_lbl) tail` >>
  qabbrev_tac `reverter = do
    rds <- emit_op RETURNDATASIZE [];
    buf <- compile_alloc_buffer 0;
    emit_void RETURNDATACOPY [buf.buf_operand; Lit 0w; rds];
    emit_inst REVERT [buf.buf_operand; rds] [] od` >>
  `shape_base_step internal compiler_label (\st. B st)
    (comp_ignore_bind reverter (comp_ignore_bind (new_block ok_lbl) tail))
    (\v st. plain_operand st v)` suffices_by
    simp[Abbr `reverter`, comp_ignore_bind_def, comp_bind_assoc] >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. B st` >> reverse conj_tac
  >- (simp[Abbr `reverter`] >>
      ho_match_mp_tac shape_base_step_extcall_revert >> simp[SF ETA_ss]) >>
  gen_tac >> BETA_TAC >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. B st` >> reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_new_block >> simp[SF ETA_ss]) >>
  gen_tac >> simp[Abbr `tail`] >> suspend "success"
QED

Resume compile_raw_call_finish_base_shape[success]:
  Cases_on `0 < max_outsize` >> simp[]
  >- (irule shape_base_step_bind >>
      qexists_tac `\rds st. B st /\ plain_operand st rds` >>
      reverse conj_tac
      >- (simp[SF ETA_ss] >>
          ho_match_mp_tac shape_base_step_emit_op_guarded >>
          simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
               inst_shape_ok_def, label_positions_ok_def,
               inst_jump_labels_ok_def, is_read0_opcode_def,
               is_terminator_def, is_param_opcode_def]) >>
      qx_gen_tac `rds` >> BETA_TAC >> suspend "cap") >>
  irule shape_base_step_return >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_raw_call_finish_base_shape[cap]:
  irule shape_base_step_bind >>
  qexists_tac `\cmp st. (B st /\ plain_operand st rds) /\ plain_operand st cmp` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_emit_op_guarded >>
      conj_tac
      >- (simp[shape_stable_def] >>
          metis_tac[shape_stable_def, plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
        inst_jump_labels_ok_def, is_read0_opcode_def,
        is_terminator_def, is_param_opcode_def] >>
      rpt strip_tac >> gvs[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `cmp` >> BETA_TAC >>
  simp[builtinSimpleTheory.compile_select_def, comp_bind_assoc] >>
  let
    val emit_plain =
      ho_match_mp_tac shape_base_step_emit_op_guarded >>
      conj_tac
      >- (simp[shape_stable_def] >>
          metis_tac[shape_stable_def, plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
        inst_jump_labels_ok_def, is_read0_opcode_def,
        is_terminator_def, is_param_opcode_def] >>
      rpt strip_tac >> gvs[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]
  in
    irule shape_base_step_bind >>
    qexists_tac `\diff st. ((B st /\ plain_operand st rds) /\ plain_operand st cmp) /\ plain_operand st diff` >>
    reverse conj_tac >- emit_plain >>
    qx_gen_tac `diff` >> BETA_TAC >>
    irule shape_base_step_bind >>
    qexists_tac `\scaled st. (((B st /\ plain_operand st rds) /\ plain_operand st cmp) /\ plain_operand st diff) /\ plain_operand st scaled` >>
    reverse conj_tac >- emit_plain >>
    qx_gen_tac `scaled` >> BETA_TAC >>
    irule shape_base_step_bind >>
    qexists_tac `\capped st. ((((B st /\ plain_operand st rds) /\ plain_operand st cmp) /\ plain_operand st diff) /\ plain_operand st scaled) /\ plain_operand st capped` >>
    reverse conj_tac >- emit_plain >>
    qx_gen_tac `capped` >> BETA_TAC >> suspend "store"
  end
QED

Resume compile_raw_call_finish_base_shape[store]:
  `emit_void MSTORE [out_val; capped] = emit_inst MSTORE [out_val; capped] []` by
    simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `shape_base_step _ _ StorePre _ _` >>
  irule shape_base_step_ignore_bind >>
  qexists_tac `\u st. StorePre st` >> reverse conj_tac
  >- (ho_match_mp_tac shape_base_step_emit_inst_guarded >>
      conj_tac
      >- (simp[Abbr `StorePre`, shape_stable_def] >>
          metis_tac[shape_stable_def, plain_operand_mono]) >>
      simp[Abbr `StorePre`, Abbr `B`, Abbr `P`, label_or_plain_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
        inst_shape_ok_def, label_positions_ok_def, inst_jump_labels_ok_def,
        is_read0_opcode_def, is_terminator_def, is_param_opcode_def] >>
      rpt strip_tac >> gvs[plain_operand_def]) >>
  gen_tac >> irule shape_base_step_return >>
  simp[Abbr `StorePre`, Abbr `B`, Abbr `P`]
QED

Finalise compile_raw_call_finish_base_shape

Theorem compile_raw_call_finish_shape[local]:
  shape_step internal compiler_label
    (\st. EVERY (plain_operand st)
      [to_op; data_ptr; data_len; gas_op; value_op; out_val; out_ptr])
    (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
      call_ty max_outsize T out_val out_ptr)
    (\v st. plain_operand st v)
Proof
  qmatch_goalsub_abbrev_tac `shape_step _ _ Pre m Post` >>
  `shape_base_step internal compiler_label Pre m Post` by
    (simp[Abbr `Pre`, Abbr `m`, Abbr `Post`] >>
     irule (SRULE [] compile_raw_call_finish_base_shape)) >>
  fs[shape_base_step_def, shape_step_def, shape_state_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  qpat_x_assum `shape_extends _ _ _ _` kall_tac >>
  qpat_x_assum `shape_base_state st'` kall_tac >>
  qpat_x_assum `Post _ _` kall_tac >>
  qpat_x_assum `Pre _` kall_tac >>
  fs[Abbr `m`] >>
  qpat_x_assum `shape_base_state _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  qpat_x_assum `Abbrev (Post = _)` kall_tac >>
  Cases_on `call_ty` >> Cases_on `0 < max_outsize` >>
  gvs[compile_raw_call_finish_def, compile_alloc_buffer_def,
      builtinSimpleTheory.compile_select_def, emit_op_def,
      emit_void_def, emit_inst_def, emit_def, new_block_def,
      fresh_var_def, fresh_id_def, fresh_label_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  fs[raw_checked_state_def, all_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  drule raw_checked_blocks_splice_branch >>
  simp[Excl "APPEND_ASSOC"] >> disch_then irule >>
  simp[mk_inst_def, compiler_label_def,
       emitHelperPropsTheory.fresh_label_output_in_future]
QED

(* Non-reverting raw calls require the separate call-check invariant widening.
   Output capacity here is unrestricted: the buffer uses fixed ALLOCA. *)
Theorem compile_call_raw_shape_widen:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args /\
  rcf.rcf_revert_on_failure ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty (RawCallTarget rcf) args default_ret)
    (\v st. value_shape_ok st v)
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e rest"]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_uncurry >> qexists_tac `\u st. T` >> reverse conj_tac
      >- (irule shape_step_conseq >>
          irule_at Any shape_step_emit_inst_guarded_framed >>
          qexists_tac `\st. T` >>
          simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
            raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
            inst_jump_labels_ok_def, is_read0_opcode_def,
            is_terminator_def, is_param_opcode_def]) >>
      gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
        plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  namedCases_on `rest` ["", "data_e kw_es"]
  >- (CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
      simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule shape_step_uncurry >> qexists_tac `\u st. T` >> reverse conj_tac
      >- (irule shape_step_conseq >>
          irule_at Any shape_step_emit_inst_guarded_framed >>
          qexists_tac `\st. T` >>
          simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
            raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
            inst_jump_labels_ok_def, is_read0_opcode_def,
            is_terminator_def, is_param_opcode_def]) >>
      gen_tac >> simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
        plain_operand_def, stackPlanTypesTheory.is_label_operand_def]) >>
  gvs[supported_exprs_exists_every] >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_uncurry >>
  qexists_tac `\v st. cenv_shape_ok st cenv /\ plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `addr_op` >> simp[] >>
  irule shape_step_uncurry >>
  qexists_tac `\data st. (cenv_shape_ok st cenv /\ plain_operand st addr_op) /\ plain_operand st data` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
      qexists_tac `\st. cenv_shape_ok st cenv /\ plain_operand st addr_op` >>
      simp[] >> ho_match_mp_tac shape_stable_conj >>
      simp[cenv_shape_ok_stable] >>
      mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `data` >> simp[] >> suspend "memory"
QED

Resume compile_call_raw_shape_widen[memory]:
  qmatch_goalsub_abbrev_tac `shape_step _ _ MemPre _ _` >>
  `shape_stable MemPre` by
    (simp[Abbr `MemPre`] >> ho_match_mp_tac shape_stable_conj >>
     conj_tac
     >- (ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
         mp_tac (Q.SPEC `[addr_op]` shape_stable_plain_operands) >> simp[]) >>
     mp_tac (Q.SPEC `[data]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\len st. MemPre st /\ plain_operand st len` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
      qexists_tac `MemPre` >>
      simp[Abbr `MemPre`, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
        inst_jump_labels_ok_def, is_read0_opcode_def,
        is_terminator_def, is_param_opcode_def] >>
      rpt strip_tac >> gvs[plain_operand_def]) >>
  qx_gen_tac `data_len` >> simp[] >>
  qmatch_goalsub_abbrev_tac `shape_step _ _ LenPre _ _` >>
  `shape_stable LenPre` by
    (simp[Abbr `LenPre`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_len]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\ptr st. LenPre st /\ plain_operand st ptr` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
      qexists_tac `LenPre` >>
      simp[Abbr `LenPre`, Abbr `MemPre`, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, label_positions_ok_def,
        inst_jump_labels_ok_def, is_read0_opcode_def,
        is_terminator_def, is_param_opcode_def, plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `data_ptr` >> simp[] >> suspend "kwargs"
QED

Resume compile_call_raw_shape_widen[kwargs]:
  qmatch_goalsub_abbrev_tac `shape_step _ _ PtrPre _ _` >>
  `shape_stable PtrPre` by
    (simp[Abbr `PtrPre`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
     mp_tac (Q.SPEC `[data_ptr]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_uncurry >>
  qexists_tac `\vs st. PtrPre st /\
    EVERY (plain_operand st)
      ((case FST vs of NONE => [] | SOME v => [v]) ++
       (case FST (SND vs) of NONE => [] | SOME v => [v]) ++
       (case SND (SND vs) of NONE => [] | SOME v => [FST v]))` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any compile_ext_call_kwargs_shape >>
      qexists_tac `PtrPre` >>
      simp[supported_exprs_exists_every, Abbr `PtrPre`, Abbr `LenPre`, Abbr `MemPre`]) >>
  qx_gen_tac `options` >> PairCases_on `options` >> simp[] >>
  suspend "gas"
QED

Resume compile_call_raw_shape_widen[gas]:
  qmatch_goalsub_abbrev_tac `shape_step _ _ KwPre _ _` >>
  `shape_stable KwPre` by
    (simp[Abbr `KwPre`] >>
     Cases_on `options0` >> Cases_on `options1` >> Cases_on `options2` >>
     simp[shape_stable_def] >>
     metis_tac[shape_stable_def, plain_operand_mono]) >>
  Cases_on `options1` >> simp[]
  >- (irule shape_step_uncurry >>
      qexists_tac `\gas st. KwPre st /\ plain_operand st gas` >> reverse conj_tac
      >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op_gas_plain >>
          qexists_tac `KwPre` >> qexists_tac `compiler_label` >> simp[]) >>
      qx_gen_tac `gas_op` >> simp[] >> suspend "buffer") >>
  rename1 `SOME gas_op` >>
  suspend "buffer_given"
QED

val raw_buffer_tac =
  qmatch_goalsub_abbrev_tac `shape_step _ _ GasPre _ _` >>
  `shape_stable GasPre` by
    (simp[Abbr `GasPre`, shape_stable_def] >>
     metis_tac[shape_stable_def, plain_operand_mono]) >>
  irule shape_step_uncurry >>
  qexists_tac `\buf st. GasPre st /\ plain_operand st (FST buf) /\ plain_operand st (SND buf)` >>
  reverse conj_tac
  >- (irule shape_step_frame_from >> irule_at Any compile_raw_call_outbuf_shape >>
      qexists_tac `GasPre` >> simp[]) >>
  qx_gen_tac `buf` >> PairCases_on `buf` >> simp[] >>
  irule shape_step_uncurry >>
  qexists_tac `\op st. plain_operand st op` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any compile_raw_call_finish_shape >>
      simp[Abbr `GasPre`, Abbr `KwPre`, Abbr `PtrPre`, Abbr `LenPre`, Abbr `MemPre`] >>
      Cases_on `options0` >> simp[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> Cases_on `rcf.rcf_max_outsize = 0` >>
  simp[shape_step_def, shape_extends_refl, value_shape_ok_def,
       mk_ptr_def, loc_shape_ok_def];

Resume compile_call_raw_shape_widen[buffer]:
  raw_buffer_tac
QED

Resume compile_call_raw_shape_widen[buffer_given]:
  raw_buffer_tac
QED

Finalise compile_call_raw_shape_widen
