Theory typedCopyFieldsPathMem
Ancestors
  typedNormalizeFields externalReturnNormalizeMem bodyDeclMemoryCounted
  typedNormalizeFrame typedBytesArrayMem context compileEnv emitHelper
  venomInst exprLoweringProps venomState venomExecSemantics fragGasPathMem
  fragGasSeqMem fragGasMode instMemFrontier memSafeRun

Theorem normalize_byte_offset_path_mem:
  compile_with_byte_offset op off sa = (out,sb) /\
  eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      eval_operand out t = SOME (a + n2w off) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all normalize_byte_offset_run >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >> simp[] >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (drule_all normalize_byte_offset_straight >> strip_tac >>
      irule body_decl_zero_gas_path >> simp[] >>
      qexists_tac `sa` >> simp[same_blocks_def] >>
      conj_tac >- (
        qpat_x_assum `isPREFIX _ _` mp_tac >>
        simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
        simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
      conj_tac
      >- (Cases_on `off = 0`
          >- (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
              simp[compile_with_byte_offset_def, comp_return_def] >>
              strip_tac >> simp[emitted_insts_def]) >>
          qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
          simp[compile_with_byte_offset_def] >> strip_tac >>
          drule emitted_insts_emit_op_local >> strip_tac >>
          simp[mk_inst_def, is_terminator_def]) >>
      drule normalize_byte_offset_mem_ok >> simp[]) >>
  drule_all normalize_byte_offset_straight >> strip_tac >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

Theorem normalize_fields_sequence_path_mem:
  (!dt st dts sts doff soff sa dp sc sp sd se s.
    Inv (dt::dts) (st::sts) doff soff sa s /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?t. gas_path_mem ctx fn s 0 (OK t) /\
        Inv dts sts (doff + type_memory_bytes ce dt)
          (soff + type_memory_bytes ce st) se t) /\
  (!dts sts doff soff sa s.
    Inv dts sts doff soff sa s ==> ~s.vs_halted) ==>
  !dts sts doff soff sa sb s.
    LENGTH dts = LENGTH sts /\ Inv dts sts doff soff sa s /\
    compile_typed_copy_fields ce dst src dts sts doff soff sa = ((),sb) ==>
    ?t. gas_path_mem ctx fn s 0 (OK t) /\
        Inv [] [] (doff + SUM (MAP (type_memory_bytes ce) dts))
          (soff + SUM (MAP (type_memory_bytes ce) sts)) sb t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "field_step")
    (mk_asm "inv_nonhalted")) >> Induct_on `dts`
  >- (rpt gen_tac >> simp[Once compile_store_memory_typed_def,
        comp_return_def] >> strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >> asm "inv_nonhalted" drule_all >> simp[]) >>
  pop_assum (mk_asm "fields_ih") >>
  rpt gen_tac >> Cases_on `sts` >- simp[] >>
  strip_tac >> drule normalize_fields_cons_states >> strip_tac >>
  asm "field_step" drule_all >> strip_tac >>
  fs[listTheory.LENGTH] >>
  asm_x "fields_ih" drule_all >> strip_tac >>
  rename1 `Inv [] [] _ _ sb u` >> qexists_tac `u` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  qpat_x_assum `Inv [] [] _ _ sb u` mp_tac >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED
