(* A bounded bytestring read followed by memory-free scalar instructions. *)
Theory bodyMemTbConvertReadSuffix
Ancestors
  bodyMemTbConvertLoadMemory bodyUnopFragMemory freshWrites
  exprSimConvertFromBytes exprLowering exprLoweringProps emitHelperProps
  list rich_list compileEnv emitHelper fragExecMem vyperTypeSystem
  fragGasPathMem fragGasMode fragGasSeqMem fragExec venomInst venomState

Theorem convert_load_straight_suffix_mem_ok[local]:
  load_bytestring_as_word x opc sa = ((r,k),sm) /\
  (opc = SHR \/ opc = SAR) /\ straight_fresh f /\ f sm = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule convert_load_bytestring_mem_ok >> metis_tac[]) >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (gvs[load_bytestring_as_word_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     simp[emitted_insts_def, DROP_APPEND]) >>
  fs[straight_fresh_def] >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> irule writes_fresh_mem_ok >> metis_tac[]
QED

Theorem convert_bytestring_scalar_ops_mem_ok:
  (cop = ConvBytestringToBool \/
   (?sg b n. cop = ConvBytestringToInt sg b n) \/
   (?d lo hi n. cop = ConvBytestringToDecimal d lo hi n) \/
   (?m. cop = ConvBytestringToBytesM m)) /\
  compile_type_convert x cop sa = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[Once compile_type_convert_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``]
    convert_load_straight_suffix_mem_ok) >> simp[] >>
  goal_assum (drule_at (Pat `load_bytestring_as_word _ _ _ = _`)) >>
  qmatch_asmsub_abbrev_tac `suffix cs' = (op,sb)` >>
  qexists_tac `suffix` >> simp[] >>
  simp[Abbr `suffix`] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
    gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_return,
    IF_CASES_TAC,
    CHANGED_TAC (simp[compile_int_clamp_def, comp_ignore_bind_def])])
QED

Theorem convert_dynamic_scalar_mem_ok:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  compile_type_convert x (mk_convert_op src dst) sa = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `is_bytestring_type src` mp_tac >>
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
  >- (drule_all dynamic_string_scalar_partition >> strip_tac >> gvs[] >>
      irule convert_bytestring_scalar_ops_mem_ok >>
      simp[] >> metis_tac[dynamic_scalar_convert_ops]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def] >>
  drule_all dynamic_bytes_scalar_partition >> strip_tac >> gvs[] >>
  irule convert_bytestring_scalar_ops_mem_ok >> simp[] >>
  metis_tac[dynamic_scalar_convert_ops, dynamic_decimal_convert_op]
QED

Theorem convert_dynamic_scalar_paths_mem:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  compile_type_convert x (mk_convert_op src dst) sa = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
  (!a t. run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
    ?j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_dynamic_scalar_mem_ok >> metis_tac[]) >>
  drule_all dynamic_scalar_straight_read_fresh >>
  disch_then (qspec_then `x` mp_tac) >>
  rewrite_tac[dynamic_straight_fresh_def] >>
  disch_then drule >> strip_tac >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[dynamic_writes_fresh_def, EVERY_MEM, FILTER_EQ_NIL] >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_x_assum `!i. MEM i _ ==> _` drule >>
         metis_tac[dynamic_read_fresh_safe]) >>
     gen_tac >> disch_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >>
     simp[fresh_write_op_def] >> rpt strip_tac >> gvs[]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (qpat_assum `fn_has_code _ _ _` mp_tac >>
     pure_rewrite_tac[fn_has_code_def] >> strip_tac >>
     qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     pure_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
       by decide_tac >>
     qexistsl_tac [`bb`,`l`] >> simp[DROP_APPEND, APPEND_ASSOC] >> metis_tac[]) >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts` by simp[] >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  conj_tac >> rpt strip_tac
  >- (drule run_inst_seq_gas_path_mem >>
      disch_then (qspecl_then [`emitted_insts sa sb`, `t`, `ctx`, `func`, `bb`] mp_tac) >>
      simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule run_inst_seq_abort_zero_path_mem >>
  goal_assum (drule_at Any) >> simp[IS_PREFIX_APPEND] >>
  qexists_tac `emitted_insts sa sb` >>
  gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]
QED
