(* The assertion in a conversion suffix is an ordinary ASSERT. *)
Theory bodyConvertScalarOpcode
Ancestors
  exprLowering exprLoweringProps emitHelperProps compileEnv venomInst rich_list

Definition convert_append_safe_def[local]:
  convert_append_safe (m : 'a compiler) <=>
    !sa. ?tail. (SND (m sa)).cs_current_insts = sa.cs_current_insts ++ tail /\
                EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) tail
End

Theorem convert_append_return[local]:
  convert_append_safe (comp_return v)
Proof
  simp[convert_append_safe_def, comp_return_def] >>
  gen_tac >> qexists_tac `[]` >> simp[]
QED

Theorem convert_append_emit_op[local]:
  opc <> ASSERT_UNREACHABLE ==> convert_append_safe (emit_op opc ops)
Proof
  simp[convert_append_safe_def] >> strip_tac >> gen_tac >>
  Cases_on `emit_op opc ops sa` >> drule emitted_insts_emit_op >>
  strip_tac >> qexists_tac `[mk_inst sa.cs_next_id opc ops [STRING #"%" (toString sa.cs_next_var)]]` >>
  simp[mk_inst_def]
QED

Theorem convert_append_emit_void[local]:
  opc <> ASSERT_UNREACHABLE ==> convert_append_safe (emit_void opc ops)
Proof
  simp[convert_append_safe_def] >> strip_tac >> gen_tac >>
  Cases_on `emit_void opc ops sa` >>
  rename1 `emit_void opc ops sa = (u,sb)` >> Cases_on `u` >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexists_tac `[mk_inst sa.cs_next_id opc ops []]` >> simp[mk_inst_def]
QED

Theorem convert_append_bind[local]:
  convert_append_safe m /\ (!a. convert_append_safe (f a)) ==>
  convert_append_safe (comp_bind m f)
Proof
  simp[convert_append_safe_def] >> strip_tac >> qx_gen_tac `sa` >>
  Cases_on `m sa` >> rename1 `m sa = (a,sm)` >> simp[comp_bind_def] >>
  qpat_x_assum `!s. ?t. (SND (m s)).cs_current_insts = _ /\ _`
    (qspec_then `sa` strip_assume_tac) >>
  qpat_x_assum `!a s. _` (qspecl_then [`a`,`sm`] strip_assume_tac) >>
  gvs[] >> qexists_tac `tail ++ tail'` >> simp[]
QED

Theorem convert_append_ignore_bind[local]:
  convert_append_safe m /\ convert_append_safe f ==>
  convert_append_safe (comp_ignore_bind m f)
Proof
  simp[comp_ignore_bind_def, convert_append_bind]
QED

Theorem convert_append_if[local]:
  convert_append_safe (if p then m else f) <=>
    ((p ==> convert_append_safe m) /\ (~p ==> convert_append_safe f))
Proof
  Cases_on `p` >> simp[]
QED

fun convert_append_steps ths =
  rpt (FIRST [irule convert_append_bind, irule convert_append_ignore_bind,
    CHANGED_TAC (simp ([convert_append_if, convert_append_return,
      convert_append_emit_op, convert_append_emit_void, pairTheory.FORALL_PROD] @ ths)),
    conj_tac, gen_tac, disch_tac]);

Theorem convert_append_int_clamp[local]:
  convert_append_safe (compile_int_clamp sg bits x)
Proof
  simp[compile_int_clamp_def] >> convert_append_steps []
QED

Theorem convert_append_load_bytestring[local]:
  shift <> ASSERT_UNREACHABLE ==>
  convert_append_safe (load_bytestring_as_word x shift)
Proof
  strip_tac >> simp[load_bytestring_as_word_def] >> convert_append_steps []
QED

Theorem convert_append_type_convert[local]:
  !x cv. convert_append_safe (compile_type_convert x cv)
Proof
  rpt gen_tac >> Cases_on `cv` >> simp[compile_type_convert_def] >>
  convert_append_steps [convert_append_int_clamp, convert_append_load_bytestring] >>
  irule convert_append_load_bytestring >> IF_CASES_TAC >> simp[]
QED

Theorem scalar_convert_emitted_no_unreachable:
  compile_type_convert x cv sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)
Proof
  strip_tac >>
  qspecl_then [`x`,`cv`] mp_tac convert_append_type_convert >>
  simp[convert_append_safe_def] >> disch_then (qspec_then `sa` strip_assume_tac) >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND]
QED
