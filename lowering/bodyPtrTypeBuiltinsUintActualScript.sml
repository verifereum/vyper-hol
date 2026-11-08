(* Replay fresh-state semantics at loop-reentry states with stale temporaries. *)
Theory bodyPtrTypeBuiltinsUintActual
Ancestors bodyPtrTypeBuiltinsBytesUintSemantics bodyPtrSignedConvertUnsignedLoad
  bodyPtrSignedConvertClamp freshWrites varsExt exprSimProps
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  venomExecSemantics venomInst venomState finite_map rich_list list

Theorem readonly_step_frame[local]:
  (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = MLOAD) /\
  step_inst_base inst ss = OK tt ==>
  tt = ss with vs_vars := tt.vs_vars /\
  (!x. ~MEM x inst.inst_outputs ==>
       FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x)
Proof
  strip_tac >- metis_tac[step_fresh_write_op] >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  gvs[update_var_def, FLOOKUP_UPDATE, venom_state_component_equality]
QED

Theorem readonly_run_frame:
  !code st ss tt.
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at st x) i.inst_outputs) code /\
  run_inst_seq code ss = OK tt ==>
  tt = ss with vs_vars := tt.vs_vars /\
  !x. not_fresh_at st x ==> FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x
Proof
  Induct >- simp[run_inst_seq_def, venom_state_component_equality] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp[run_inst_seq_def] >> strip_tac >>
  (Cases_on `step_inst_base inst ss` >> gvs[] >>
  rename1 `step_inst_base inst ss = OK s1` >>
  `s1 = ss with vs_vars := s1.vs_vars /\
   (!x. ~MEM x inst.inst_outputs ==>
        FLOOKUP s1.vs_vars x = FLOOKUP ss.vs_vars x)` by
    metis_tac[readonly_step_frame] >>
  first_x_assum (qspecl_then [`st`,`s1`,`tt`] mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST_ALL_TAC >> fs[venom_state_component_equality]) >>
  rpt strip_tac >>
  `~MEM x inst.inst_outputs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[])
QED

Theorem uint_convert_code_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at sa x) i.inst_outputs)
        (emitted_insts sa sb)
Proof
  Cases_on `8*n > b` >>
  simp[mk_convert_op_def, is_bytestring_type_def, compile_type_convert_def,
       load_bytestring_as_word_def, compile_int_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, fresh_write_op_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> decide_tac
QED

Theorem uint_convert_run_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf ==>
  sf = ss with vs_vars := sf.vs_vars /\
  (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  strip_tac >> drule uint_convert_code_frame >> strip_tac >>
  drule_all readonly_run_frame >> simp[]
QED

Theorem uint_convert_replay:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> drule uint_convert_code_frame >> disch_tac >>
  irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[fresh_write_op_def, venomInstTheory.is_terminator_def,
      venomInstTheory.is_ext_call_op_def]
QED

Theorem bytes_uint_semantic_run_actual:
  valid_conversion (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) /\
  well_formed_type tenv (BaseT (UintT b)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME stv /\
  value_has_type stv v /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) v = res /\
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  case res of
  | INL vout => ?dtv sf. evaluate_type (get_tenv cx) (BaseT (UintT b)) = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 dtv vout) /\
      sf = ss with vs_vars := sf.vs_vars /\
      (!z w. not_fresh_at sa z /\ lookup_var z ss = SOME w ==>
             lookup_var z sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand op (drop_fresh sa ss) = SOME a` by simp[eval_operand_drop_fresh] >>
  `val_in_memory stv v (w2n a) (drop_fresh sa ss).vs_memory` by
    simp[drop_fresh_def] >>
  drule_all bytes_uint_semantic_run >>
  Cases_on `res` >> simp[] >> strip_tac
  >- (drule uint_convert_replay >> disch_then (qspec_then `ss` mp_tac) >>
      simp[vars_ext_result_def] >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
      `actual = ss with vs_vars := actual.vs_vars /\
       (!z. not_fresh_at sa z ==> FLOOKUP actual.vs_vars z = FLOOKUP ss.vs_vars z)` by
        (irule uint_convert_run_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
      qexists_tac `actual` >> simp[] >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = sf with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      rpt strip_tac >> fs[lookup_var_def]) >>
  drule uint_convert_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> metis_tac[]
QED

Theorem uint_convert_stmt_frame:
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es ss ==>
  stmt_state_rel ctx func cenv cx es sf
Proof
  strip_tac >> drule_all uint_convert_run_frame >> strip_tac >>
  qpat_x_assum `sf = _` SUBST1_TAC >>
  irule stmt_state_rel_vars_frame >> simp[] >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED
