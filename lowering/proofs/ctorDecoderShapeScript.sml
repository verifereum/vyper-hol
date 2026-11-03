Theory ctorDecoderShape
Ancestors
  list loweringShapeDefs loweringShapeRules loweringShapeProps
  abiEncoder unitShapeDefs venomInst

val ctor_opcode_tac =
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, jump_label_ok_def, is_terminator_def,
       is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
       operand_case_not_label, plain_operand_def, label_or_plain_def,
       stackPlanTypesTheory.is_label_operand_def];

fun ctor_emit_bind post name cont =
  irule shape_step_bind >> qexists_tac post >> conj_tac
  >- (qx_gen_tac name >> BETA_TAC >> cont) >>
  ho_match_mp_tac extbodies_emit_plain >> ctor_opcode_tac;

fun ctor_void_bind post cont =
  irule shape_step_ignore_bind >> qexists_tac post >> conj_tac
  >- (gen_tac >> BETA_TAC >> cont) >>
  ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac;

Theorem compile_getelemptr_abi_dload_shape[local]:
  !src dynamic off hi.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [src; hi])
      (compile_getelemptr_abi src dynamic off DLOAD hi)
      (\ptr st. plain_operand st ptr)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_getelemptr_abi_def] >>
  ctor_emit_bind `\head st. EVERY (plain_operand st) [head; src; hi]` `head`
    (Cases_on `dynamic` >> pure_rewrite_tac[COND_CLAUSES, NOT_CLAUSES]
     >- (ctor_emit_bind `\offv st. EVERY (plain_operand st) [offv; head; src; hi]` `offv`
       (ctor_emit_bind `\ptrv st. EVERY (plain_operand st) [ptrv; offv; head; src; hi]` `ptrv`
         (irule shape_step_ignore_bind >>
          qexists_tac `\u st. EVERY (plain_operand st) [ptrv; offv; head; src; hi]` >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
          Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
          >- (irule shape_step_return >> simp[]) >>
          ctor_emit_bind `\bad st. EVERY (plain_operand st) [bad; ptrv; offv; head; src; hi]` `bad`
           (ctor_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; ptrv; offv; head; src; hi]` `ok`
             (irule shape_step_conseq >>
              qexistsl_tac [`compiler_label`,
                `\st. EVERY (plain_operand st) [ok; bad; ptrv; offv; head; src; hi]`,
                `\u st. EVERY (plain_operand st) [ok; bad; ptrv; offv; head; src; hi]`] >>
              simp_tac bool_ss [] >> conj_tac >- simp[] >>
              ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac))))) >>
     irule shape_step_return >> simp[])
QED

Theorem compile_abi_decode_dyn_elem_ptr_dload_shape[local]:
  !elem src hi sz.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [elem; src; hi])
      (compile_abi_decode_dyn_elem_ptr DLOAD elem src hi sz)
      (\ptr st. plain_operand st ptr)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  ctor_emit_bind `\offv st. EVERY (plain_operand st) [offv; elem; src; hi]` `offv`
   (ctor_emit_bind `\ptrv st. EVERY (plain_operand st) [ptrv; offv; elem; src; hi]` `ptrv`
    (irule shape_step_ignore_bind >>
     qexists_tac `\u st. EVERY (plain_operand st) [ptrv; offv; elem; src; hi]` >> conj_tac
     >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
     Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
     >- (irule shape_step_return >> simp[]) >>
     ctor_emit_bind `\bad st. EVERY (plain_operand st) [bad; ptrv; offv; elem; src; hi]` `bad`
      (ctor_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; ptrv; offv; elem; src; hi]` `ok`
       (ctor_void_bind `\u st. EVERY (plain_operand st) [ok; bad; ptrv; offv; elem; src; hi]`
        (ctor_emit_bind `\eend st. EVERY (plain_operand st) [eend; ok; bad; ptrv; offv; elem; src; hi]` `eend`
         (ctor_emit_bind `\oob st. EVERY (plain_operand st) [oob; eend; ok; bad; ptrv; offv; elem; src; hi]` `oob`
          (ctor_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; eend; ok; bad; ptrv; offv; elem; src; hi]` `ok2`
           (irule shape_step_conseq >>
            qexistsl_tac [`compiler_label`,
              `\st. EVERY (plain_operand st) [ok2; oob; eend; ok; bad; ptrv; offv; elem; src; hi]`,
              `\u st. EVERY (plain_operand st) [ok2; oob; eend; ok; bad; ptrv; offv; elem; src; hi]`] >>
            simp_tac bool_ss [] >> conj_tac >- simp[] >>
            ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac))))))))
QED

Theorem compile_abi_decode_static_dload_shape[local]:
  !src dst clamp.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [src; dst])
      (compile_abi_decode_static src dst DLOAD
        (\v. compile_abi_clamp_basetype v clamp)) (\x st. T)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_abi_decode_static_def] >>
  irule shape_step_bind >>
  qexists_tac `\v st. EVERY (plain_operand st) [v; src; dst]` >> conj_tac
  >- (qx_gen_tac `v` >> BETA_TAC >> irule shape_step_ignore_bind >>
      qexists_tac `\u st. EVERY (plain_operand st) [v; src; dst] /\ T` >>
      conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`,
            `\st. EVERY (plain_operand st) [v; src; dst]`,
            `\u st. EVERY (plain_operand st) [v; src; dst]`] >>
          simp_tac bool_ss [] >> ho_match_mp_tac extbodies_emit_void_plain >>
          ctor_opcode_tac) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [v; src; dst] /\
               EVERY (plain_operand st) [v]`,
        `\u st. EVERY (plain_operand st) [v; src; dst] /\ T`] >>
      simp_tac bool_ss [] >> conj_tac >- simp[] >>
      mp_tac (Q.SPECL [`v`, `clamp`] compile_abi_clamp_basetype_shape) >>
      strip_tac >> drule shape_step_frame >>
      disch_then (qspec_then `\st. EVERY (plain_operand st) [v; src; dst]` mp_tac) >>
      simp[shape_stable_plain_operands]) >>
  ho_match_mp_tac extbodies_emit_plain >> ctor_opcode_tac
QED

fun ctor_block_bind post cont =
  irule shape_step_ignore_bind >> qexists_tac post >> conj_tac
  >- (gen_tac >> BETA_TAC >> cont) >>
  ho_match_mp_tac shape_step_new_block >> simp[shape_stable_plain_operands];

fun ctor_label_bind pre name cont =
  irule shape_step_bind >> qexists_tac pre >> conj_tac
  >- (qx_gen_tac name >> BETA_TAC >> ho_match_mp_tac extbodies_assume >> strip_tac >> cont) >>
  ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_plain_operands];

Theorem ctor_decode_mutual[local]:
  (!dst src opc hi info. opc = DLOAD ==>
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_to_buf dst src opc hi info) (\x st. T)) /\
  (!dst src opc hi elems ao vo. opc = DLOAD ==>
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_complex_elems dst src opc hi elems ao vo) (\x st. T)) /\
  (!dst src opc hi ei asz msz ip cnt. opc = DLOAD ==>
    shape_step F compiler_label
      (\st. EVERY (plain_operand st) [dst; src; hi; ip; cnt])
      (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt) (\x st. T))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume ctor_decode_mutual[prim]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [src; dst]`, `\x st. T`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  irule compile_abi_decode_static_dload_shape
QED

Resume ctor_decode_mutual[nil]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  irule shape_step_return >> simp[]
QED

Resume ctor_decode_mutual[bytes]:
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM, opcode_case_def] >> BETA_TAC >>
  ctor_emit_bind `\len st. EVERY (plain_operand st) [len; dst; src; hi]` `len`
   (ctor_emit_bind `\bad st. EVERY (plain_operand st) [bad; len; dst; src; hi]` `bad`
    (ctor_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]` `ok`
     (ctor_void_bind `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`
      (suspend "bytes_tail"))))
QED
Resume ctor_decode_mutual[bytes_tail]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`,
        `\u st. EVERY (plain_operand st) [ok; bad; len; dst; src; hi]`] >>
      simp_tac bool_ss [] >>
      ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac) >>
  suspend "bytes_guard"
QED
Resume ctor_decode_mutual[bytes_guard]:
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (irule shape_step_return >> simp[]) >>
  ctor_emit_bind `\start st. EVERY (plain_operand st) [start; ok; bad; len; dst; src; hi]` `start`
   (ctor_emit_bind `\last st. EVERY (plain_operand st) [last; start; ok; bad; len; dst; src; hi]` `last`
    (ctor_emit_bind `\oob st. EVERY (plain_operand st) [oob; last; start; ok; bad; len; dst; src; hi]` `oob`
     (ctor_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]` `ok2`
      (suspend "bytes_assert"))))
QED
Resume ctor_decode_mutual[bytes_assert]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ok2; oob; last; start; ok; bad; len; dst; src; hi]`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac
QED
Resume ctor_decode_mutual[complex]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `!static_sz. _` (qspec_then
    `FOLDR (\(_, a:num, _:num) acc. a + acc) 0 elems` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `!static_sz. _` (qspec_then
    `FOLDR (\(_, a:num, _:num) acc. a + acc) 0 elems` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (first_assum irule >> simp[]) >>
  ctor_emit_bind `\last st. EVERY (plain_operand st) [last; dst; src; hi]` `last`
   (ctor_emit_bind `\bad st. EVERY (plain_operand st) [bad; last; dst; src; hi]` `bad`
    (ctor_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; last; dst; src; hi]` `ok`
     (ctor_void_bind `\u st. EVERY (plain_operand st) [ok; bad; last; dst; src; hi]`
      (irule shape_step_conseq >>
       qexistsl_tac [`compiler_label`,
         `\st. EVERY (plain_operand st) [dst; src; hi]`, `\x st. T`] >>
       simp_tac bool_ss [] >> conj_tac >- simp[] >>
       first_assum irule >> simp[]))))
QED
Resume ctor_decode_mutual[cons]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `compile_getelemptr_abi src dyn ao DLOAD hi` >>
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dyn` mp_tac) >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dyn` mp_tac) >>
  simp_tac bool_ss [Abbr `dyn`] >> ntac 2 disch_tac >>
  irule shape_step_bind >>
  qexists_tac `\elem st. EVERY (plain_operand st) [elem; dst; src; hi]` >>
  conj_tac
  >- (qx_gen_tac `elem` >> BETA_TAC >>
      ctor_emit_bind `\edst st. EVERY (plain_operand st) [edst; elem; dst; src; hi]` `edst`
       (irule shape_step_ignore_bind >>
        qexists_tac `\u st. EVERY (plain_operand st) [edst; elem; dst; src; hi] /\ T` >>
        conj_tac
        >- (gen_tac >> BETA_TAC >>
            irule shape_step_conseq >>
            qexistsl_tac [`compiler_label`,
              `\st. EVERY (plain_operand st) [dst; src; hi]`, `\x st. T`] >>
            simp_tac bool_ss [] >> conj_tac >- simp[] >>
            first_assum irule) >>
        ho_match_mp_tac extbodies_frame >>
        simp_tac bool_ss [shape_stable_plain_operands] >>
        qexists_tac `\st. EVERY (plain_operand st) [edst; elem; hi]` >>
        conj_tac >- (first_assum irule) >> simp[])) >>
  suspend "cons_ptr"
QED
Resume ctor_decode_mutual[cons_ptr]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [dst; src; hi]`,
    `\elem st. EVERY (plain_operand st) [dst; src; hi] /\ plain_operand st elem`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  qexists_tac `\st. EVERY (plain_operand st) [src; hi]` >>
  conj_tac >- (irule compile_getelemptr_abi_dload_shape) >> simp[]
QED

Resume ctor_decode_mutual[array]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM, opcode_case_def] >> BETA_TAC >>
  ctor_emit_bind `\cnt0 st. EVERY (plain_operand st) [cnt0; dst; src; hi]` `cnt0`
   (suspend "array_clamp")
QED
Resume ctor_decode_mutual[array_clamp]:
  ctor_emit_bind `\bad st. EVERY (plain_operand st) [bad; cnt0; dst; src; hi]` `bad`
    (ctor_emit_bind `\ok st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]` `ok`
     (suspend "array_check"))
QED
Resume ctor_decode_mutual[array_check]:
  ctor_void_bind `\u st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]`
      (irule shape_step_ignore_bind >>
       qexists_tac `\u st. EVERY (plain_operand st) [ok; bad; cnt0; dst; src; hi]` >>
       conj_tac >- suspend "array_reload" >> suspend "array_guard")
QED
Resume ctor_decode_mutual[array_guard]:
  Cases_on `hi = Lit 0w` >> pure_asm_rewrite_tac[COND_CLAUSES, REFL_CLAUSE]
  >- (irule shape_step_return >> simp[]) >>
  ctor_emit_bind `\sz st. EVERY (plain_operand st) [sz; ok; bad; cnt0; dst; src; hi]` `sz`
   (ctor_emit_bind `\sz1 st. EVERY (plain_operand st) [sz1; sz; ok; bad; cnt0; dst; src; hi]` `sz1`
    (ctor_emit_bind `\last st. EVERY (plain_operand st) [last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `last`
     (ctor_emit_bind `\oob st. EVERY (plain_operand st) [oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `oob`
      (ctor_emit_bind `\ok2 st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]` `ok2`
       (suspend "array_assert")))))
QED
Resume ctor_decode_mutual[array_assert]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ok2; oob; last; sz1; sz; ok; bad; cnt0; dst; src; hi]`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac
QED
Resume ctor_decode_mutual[array_reload]:
  gen_tac >> BETA_TAC >>
  ctor_emit_bind `\cnt st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi]` `cnt`
   (ctor_void_bind `\u st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi]`
     (suspend "array_choose"))
QED
Resume ctor_decode_mutual[array_choose]:
  qmatch_goalsub_abbrev_tac `if bulk then _ else _` >>
  Cases_on `bulk` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (ctor_emit_bind `\sz st. EVERY (plain_operand st) [sz; cnt; ok; bad; cnt0; dst; src; hi]` `sz`
       (ctor_emit_bind `\sdata st. EVERY (plain_operand st) [sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]` `sdata`
        (ctor_emit_bind `\ddata st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]` `ddata`
         (suspend "array_copy")))) >>
  irule shape_step_bind >>
  qexists_tac `\buf st. EVERY (plain_operand st) [cnt; ok; bad; cnt0; dst; src; hi] /\
                        plain_operand st buf.buf_operand` >>
  conj_tac >- suspend "array_loop" >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >> qexists_tac `\st. T` >>
  simp_tac bool_ss [] >> irule compile_alloc_buffer_shape
QED
Resume ctor_decode_mutual[array_copy]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]`,
    `\u st. EVERY (plain_operand st) [ddata; sdata; sz; cnt; ok; bad; cnt0; dst; src; hi]`] >>
  simp_tac bool_ss [] >> ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac
QED
Resume ctor_decode_mutual[array_loop]:
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. EVERY (plain_operand st) [buf.buf_operand; dst; src; hi; cnt]`, `\x st. T`] >>
  simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ctor_void_bind `\u st. EVERY (plain_operand st) [buf.buf_operand; dst; src; hi; cnt]`
    (irule shape_step_conseq >>
     qexistsl_tac [`compiler_label`,
       `\st. EVERY (plain_operand st) [dst; src; hi; buf.buf_operand; cnt]`, `\x st. T`] >>
     simp_tac bool_ss [] >> conj_tac >- simp[] >>
     first_x_assum (qspecl_then [`F`, `buf.buf_operand`, `buf`, `cnt`] mp_tac) >>
     simp_tac bool_ss [])
QED
Resume ctor_decode_mutual[loop]:
  rpt gen_tac >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pure_rewrite_tac[Once compile_abi_decode_to_buf_def, LET_THM,
    extbodies_emit_inst_void] >> BETA_TAC >>
  ctor_label_bind
    `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `hdr`
   (ctor_label_bind
     `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `bodylbl`
    (ctor_label_bind
      `\l st. EVERY (plain_operand st) [dst; src; hi; ip; cnt] /\ compiler_label l` `exit`
     (suspend "loop_jump")))
QED
Resume ctor_decode_mutual[loop_jump]:
  ctor_void_bind `\u st. EVERY (plain_operand st) [dst; src; hi; ip; cnt]`
   (ctor_block_bind `\u st. EVERY (plain_operand st) [dst; src; hi; ip; cnt]`
     (suspend "loop_header"))
QED
Resume ctor_decode_mutual[loop_header]:
  ctor_emit_bind `\idx st. EVERY (plain_operand st) [idx; dst; src; hi; ip; cnt]` `idx`
   (ctor_emit_bind `\n st. EVERY (plain_operand st) [n; idx; dst; src; hi; ip; cnt]` `n`
    (ctor_emit_bind `\cmp st. EVERY (plain_operand st) [cmp; n; idx; dst; src; hi; ip; cnt]` `cmp`
     (ctor_emit_bind `\done st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]` `done`
      (suspend "loop_jnz"))))
QED
Resume ctor_decode_mutual[loop_jnz]:
  ctor_void_bind `\u st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]`
    (ctor_block_bind `\u st. EVERY (plain_operand st) [done; cmp; n; idx; dst; src; hi; ip; cnt]`
      (suspend "loop_body")) >>
  rpt strip_tac >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED
Resume ctor_decode_mutual[loop_body]:
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) [dst; src; hi; ip]`,
    `\x st. T`] >> simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ctor_emit_bind `\idx2 st. EVERY (plain_operand st) [idx2; dst; src; hi; ip]` `idx2`
   (ctor_emit_bind `\sdata st. EVERY (plain_operand st) [sdata; idx2; dst; src; hi; ip]` `sdata`
    (suspend "loop_source"))
QED
Resume ctor_decode_mutual[loop_source]:
  ctor_emit_bind `\soff st. EVERY (plain_operand st) [soff; sdata; idx2; dst; src; hi; ip]` `soff`
   (ctor_emit_bind `\esrc st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip]` `esrc`
    (irule shape_step_bind >>
     qexists_tac `\actual st. EVERY (plain_operand st) [actual; idx2; dst; hi; ip]` >>
     conj_tac >- suspend "loop_dest" >> suspend "loop_actual"))
QED
Resume ctor_decode_mutual[loop_actual]:
  qmatch_goalsub_abbrev_tac `if dyn then _ else _` >>
  Cases_on `dyn` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`,
        `\st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip]`,
        `\actual st. EVERY (plain_operand st) [esrc; soff; sdata; idx2; dst; src; hi; ip] /\ plain_operand st actual`] >>
      simp_tac bool_ss [] >> conj_tac >- simp[] >>
      ho_match_mp_tac extbodies_frame >>
      simp_tac bool_ss [shape_stable_plain_operands] >>
      qexists_tac `\st. EVERY (plain_operand st) [esrc; sdata; hi]` >>
      conj_tac >- (irule compile_abi_decode_dyn_elem_ptr_dload_shape) >> simp[]) >>
  irule shape_step_return >> simp[]
QED
Resume ctor_decode_mutual[loop_dest]:
  qx_gen_tac `actual` >> BETA_TAC >>
  ctor_emit_bind `\ddata st. EVERY (plain_operand st) [ddata; actual; idx2; dst; hi; ip]` `ddata`
   (ctor_emit_bind `\doff st. EVERY (plain_operand st) [doff; ddata; actual; idx2; dst; hi; ip]` `doff`
    (ctor_emit_bind `\edst st. EVERY (plain_operand st) [edst; doff; ddata; actual; idx2; dst; hi; ip]` `edst`
     (irule shape_step_ignore_bind >>
      qexists_tac `\u st. EVERY (plain_operand st) [edst; doff; ddata; actual; idx2; dst; hi; ip] /\ T` >>
      conj_tac >- suspend "loop_end" >> suspend "loop_recurse")))
QED
Resume ctor_decode_mutual[loop_recurse]:
  qpat_x_assum `!dyn dst src. _` (qspec_then
    `dec_info_needs_offset ei` mp_tac) >>
  disch_then assume_tac >>
  ho_match_mp_tac extbodies_frame >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  qexists_tac `\st. EVERY (plain_operand st) [edst; actual; hi]` >>
  conj_tac >- (first_assum irule >> simp_tac bool_ss []) >> simp[]
QED
Resume ctor_decode_mutual[loop_end]:
  gen_tac >> BETA_TAC >> simp_tac bool_ss [] >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. EVERY (plain_operand st) [idx2; ip]`,
    `\x st. T`] >> simp_tac bool_ss [] >> conj_tac >- simp[] >>
  ctor_emit_bind `\next st. EVERY (plain_operand st) [next; idx2; ip]` `next`
   (ctor_void_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
    (ctor_void_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
     (ctor_block_bind `\u st. EVERY (plain_operand st) [next; idx2; ip]`
      (irule shape_step_return >> simp[]))))
QED
Finalise ctor_decode_mutual

Theorem compile_abi_decode_dload_shape:
  (!dst src hi info.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_to_buf dst src DLOAD hi info) (\x st. T)) /\
  (!dst src hi elems ao vo.
    shape_step F compiler_label (\st. EVERY (plain_operand st) [dst; src; hi])
      (compile_abi_decode_complex_elems dst src DLOAD hi elems ao vo) (\x st. T)) /\
  (!dst src hi ei asz msz ip cnt.
    shape_step F compiler_label
      (\st. EVERY (plain_operand st) [dst; src; hi; ip; cnt])
      (compile_abi_decode_dyn_loop dst src DLOAD hi ei asz msz ip cnt) (\x st. T))
Proof
  metis_tac[ctor_decode_mutual]
QED
