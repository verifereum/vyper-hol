Theory whitelistS2RawBaseShape
Ancestors
  list loweringShapeRules loweringShapeDefs builtinSystem context
  compileEnv emitHelper unitShapeDefs venomInst

Theorem shape_base_step_emit_op_call_widen:
  !internal LP R opc g rest.
    shape_stable R /\ MEM opc [CALL; STATICCALL; DELEGATECALL] /\
    (!id outs. lowered_inst_ok internal (mk_inst id opc (g :: rest) outs)) ==>
    shape_base_step internal LP
      (\st. R st /\ (gas_operand st g \/ plain_operand st g) /\
            EVERY (plain_operand st) rest)
      (emit_op opc (g :: rest)) (\x st'. R st' /\ plain_operand st' x)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_base_step_conseq >>
  irule_at Any shape_base_step_emit_op >>
  qexistsl [`R`, `LP`] >> simp[] >>
  rpt strip_tac >> simp[] >>
  gvs[label_or_plain_def, gas_operand_def, plain_operand_def,
      EVERY_MEM] >> metis_tac[]
QED
Theorem shape_base_step_alloc_buffer_widen:
  !internal LP R size.
    shape_stable R ==>
    shape_base_step internal LP R (compile_alloc_buffer size)
      (\buf st. R st /\ plain_operand st buf.buf_operand)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_alloc_buffer_def] >>
  irule shape_base_step_bind >>
  qexists_tac `\op st. R st /\ plain_operand st op` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_base_step_return >> simp[]) >>
  irule shape_base_step_conseq >>
  irule_at Any shape_base_step_emit_op >>
  qexistsl [`R`, `LP`] >>
  simp[label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def,
       lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, mk_inst_def, label_positions_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED

fun base_emit_with stable_tac g =
  (qmatch_goalsub_abbrev_tac `shape_base_step _ lab pre _ _` >>
   irule shape_base_step_conseq >>
   qexistsl_tac [`lab`, `pre`, `\x st. pre st /\ plain_operand st x`] >>
   conj_tac >- simp[Abbr `pre`] >>
   conj_tac >- simp[Abbr `pre`] >>
   conj_tac >- simp[] >>
   irule shape_base_step_emit_op_guarded >>
   reverse conj_tac
   >- (conj_tac
       >- (simp_tac bool_ss [Abbr `pre`] >> stable_tac) >> simp[]) >>
   rpt strip_tac >>
   simp[label_or_plain_def, lowered_inst_ok_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
        label_positions_ok_def, is_terminator_def, is_param_opcode_def,
        is_read0_opcode_def] >>
   gvs[Abbr `pre`, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]) g;

val base_emit_tac = base_emit_with
  (ho_match_mp_tac shape_stable_conj >> simp[shape_stable_plain_operands]);
val base_plain_emit_tac = base_emit_with
  (irule shape_stable_plain_operands);

fun base_plain_void_tac g =
  (pure_rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
   qmatch_goalsub_abbrev_tac `shape_base_step _ lab pre _ _` >>
   irule shape_base_step_conseq >>
   qexistsl_tac [`lab`, `pre`, `\x st. pre st`] >>
   conj_tac >- simp[Abbr `pre`] >>
   conj_tac >- simp[Abbr `pre`] >>
   conj_tac >- simp[] >>
   irule shape_base_step_emit_inst_guarded >>
   reverse conj_tac
   >- (conj_tac
       >- (simp_tac bool_ss [Abbr `pre`] >> irule shape_stable_plain_operands) >>
       simp[]) >>
   rpt strip_tac >>
   simp[label_or_plain_def, lowered_inst_ok_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, mk_inst_def,
        label_positions_ok_def, is_terminator_def, is_param_opcode_def,
        is_read0_opcode_def] >>
   gvs[Abbr `pre`, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]) g;

Theorem compile_select_base_shape_widen:
  !internal LP R c t e. shape_stable R ==>
    shape_base_step internal LP
      (\st. R st /\ plain_operand st c /\ plain_operand st t /\ plain_operand st e)
      (builtinSimple$compile_select c t e)
      (\z st. R st /\ plain_operand st z)
Proof
  rpt gen_tac >> strip_tac >> simp[builtinSimpleTheory.compile_select_def] >>
  irule shape_base_step_conseq >>
  qexistsl_tac [`LP`, `\st. R st /\ EVERY (plain_operand st) [c;t;e]`,
               `\z st. R st /\ plain_operand st z`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  irule shape_base_step_bind >>
  qexists_tac `\diff st. R st /\ EVERY (plain_operand st) [diff;c;e]` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_base_step_bind >>
      qexists_tac `\scaled st. R st /\ EVERY (plain_operand st) [scaled;e]` >>
      conj_tac >- (gen_tac >> BETA_TAC >> base_emit_tac) >>
      base_emit_tac) >>
  base_emit_tac
QED


(* Non-reverting calls return their success bit, optionally paired with bytes. *)
Theorem compile_raw_call_finish_base_shape_widen:
  !to_op data_ptr data_len gas_op value_op call_ty max_outsize out_val out_ptr internal.
    shape_base_step internal compiler_label
      (\st. EVERY (plain_operand st)
        [to_op; data_ptr; data_len; gas_op; value_op; out_val; out_ptr])
      (compile_raw_call_finish to_op data_ptr data_len gas_op value_op
        call_ty max_outsize F out_val out_ptr)
      (\v st. plain_operand st v)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_raw_call_finish_def] >>
  irule shape_base_step_bind >>
  qexists_tac `\success st. EVERY (plain_operand st) [success;out_val]` >>
  conj_tac
  >- (qx_gen_tac `success` >> BETA_TAC >> Cases_on `max_outsize > 0` >>
      asm_simp_tac std_ss [LET_THM]
      >- (irule shape_base_step_bind >>
          qexists_tac `\rds st. EVERY (plain_operand st) [success;out_val;rds]` >>
          reverse conj_tac >- base_plain_emit_tac >>
          qx_gen_tac `rds` >> BETA_TAC >>
          irule shape_base_step_bind >>
          qexists_tac `\cmp st. EVERY (plain_operand st) [success;out_val;rds;cmp]` >>
          reverse conj_tac >- base_plain_emit_tac >>
          qx_gen_tac `cmp` >> BETA_TAC >>
          irule shape_base_step_bind >>
          qexists_tac `\capped st. EVERY (plain_operand st) [success;out_val;capped]` >>
          reverse conj_tac
          >- (irule shape_base_step_conseq >>
              irule_at Any compile_select_base_shape_widen >>
              qexistsl_tac [`\st. EVERY (plain_operand st) [success;out_val]`,
                           `compiler_label`] >>
              simp[shape_stable_plain_operands, plain_operand_def,
                   stackPlanTypesTheory.is_label_operand_def]) >>
          qx_gen_tac `capped` >> BETA_TAC >>
          irule shape_base_step_ignore_bind >>
          qexists_tac `\u st. EVERY (plain_operand st) [success;out_val]` >>
          reverse conj_tac >- base_plain_void_tac >>
          gen_tac >> BETA_TAC >>
          irule shape_base_step_bind >>
          qexists_tac `\buf st. EVERY (plain_operand st) [success;out_val;buf.buf_operand]` >>
          reverse conj_tac
          >- (irule shape_base_step_conseq >>
              irule_at Any shape_base_step_alloc_buffer_widen >>
              qexistsl_tac [`\st. EVERY (plain_operand st) [success;out_val]`,
                           `compiler_label`] >> simp[shape_stable_plain_operands]) >>
          qx_gen_tac `buf` >> BETA_TAC >>
          irule shape_base_step_ignore_bind >>
          qexists_tac `\u st. EVERY (plain_operand st) [out_val;buf.buf_operand]` >>
          reverse conj_tac >- base_plain_void_tac >>
          gen_tac >> BETA_TAC >>
          irule shape_base_step_bind >>
          qexists_tac `\dst st. EVERY (plain_operand st) [out_val;buf.buf_operand;dst]` >>
          reverse conj_tac >- base_plain_emit_tac >>
          qx_gen_tac `dst` >> BETA_TAC >>
          irule shape_base_step_ignore_bind >>
          qexists_tac `\u st. EVERY (plain_operand st) [buf.buf_operand]` >>
          reverse conj_tac >- base_plain_void_tac >>
          gen_tac >> BETA_TAC >> irule shape_base_step_return >> simp[]) >>
      irule shape_base_step_return >> simp[]) >>
  Cases_on `call_ty` >> simp_tac bool_ss [call_type_case_def] >> base_plain_emit_tac
QED
