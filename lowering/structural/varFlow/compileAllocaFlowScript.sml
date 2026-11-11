(* TOP-LEVEL: compiler actions preserve predicates on all ALLOCA instructions
   when the predicate accepts fresh output names. The condition composes
   through the actual compiler monad and survives block transitions.
   Helpers expose emitted instructions without executing generated code. *)
Theory compileAllocaFlow
Ancestors
  compileVarFlow compileEnv emitHelper venomInst list pair arithmetic

Definition compiler_alloca_code_def:
  compiler_alloca_code P cs <=>
    EVERY (\inst. inst.inst_opcode = ALLOCA ==> P inst) cs.cs_current_insts /\
    EVERY (\bb. EVERY (\inst. inst.inst_opcode = ALLOCA ==> P inst) bb.bb_instructions) cs.cs_blocks
End

Definition compiler_alloca_pred_def:
  compiler_alloca_pred P m <=>
    compiler_vars_mono m /\
    !cs. (!id ops n. cs.cs_next_var <= n ==>
      P (mk_inst id ALLOCA ops ["%" ++ toString n])) /\ compiler_alloca_code P cs ==>
      compiler_alloca_code P (SND (m cs))
End

Theorem compiler_alloca_pred_return:
  !P x. compiler_alloca_pred P (comp_return x)
Proof
  simp[compiler_alloca_pred_def, compiler_vars_mono_return, comp_return_def]
QED

Theorem compiler_alloca_pred_bind:
  !P m f. compiler_alloca_pred P m /\ (!value. compiler_alloca_pred P (f value)) ==>
    compiler_alloca_pred P (comp_bind m f)
Proof
  rpt gen_tac >> strip_tac >>
  `compiler_vars_mono m /\ (!value. compiler_vars_mono (f value))` by fs[compiler_alloca_pred_def] >>
  simp_tac bool_ss [compiler_alloca_pred_def] >> conj_tac
  >- (drule_all compiler_vars_mono_bind >> simp[]) >>
  qx_gen_tac `cs` >> strip_tac >> Cases_on `m cs` >> rename1 `m cs = (step_ret,mid)` >>
  `cs.cs_next_var <= mid.cs_next_var` by (drule_all compiler_vars_mono_result >> simp[]) >>
  `compiler_alloca_code P mid` by
    (qpat_x_assum `compiler_alloca_pred P m` (mp_tac o REWRITE_RULE [compiler_alloca_pred_def]) >>
     strip_tac >> qpat_x_assum `!cs. _` (qspec_then `cs` mp_tac) >> simp[]) >>
  `!id ops n. mid.cs_next_var <= n ==> P (mk_inst id ALLOCA ops ["%" ++ toString n])` by
    (rpt gen_tac >> DISCH_TAC >>
     qpat_x_assum `!id ops n. _` irule >> decide_tac) >>
  qpat_x_assum `!value. compiler_alloca_pred P (f value)` (qspec_then `step_ret` mp_tac) >>
  simp_tac bool_ss [compiler_alloca_pred_def] >> strip_tac >>
  qpat_x_assum `!cs. _` (qspec_then `mid` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[comp_bind_def]
QED

Theorem compiler_alloca_pred_ignore_bind:
  !P m f. compiler_alloca_pred P m /\ compiler_alloca_pred P f ==>
    compiler_alloca_pred P (comp_ignore_bind m f)
Proof
  rpt gen_tac >> rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_alloca_pred_bind >> simp[]
QED

Theorem compiler_alloca_pred_prims:
  (!P label. compiler_alloca_pred P (new_block label)) /\
  (!P. compiler_alloca_pred P fresh_var) /\
  (!P suffix. compiler_alloca_pred P (fresh_label suffix)) /\
  (!P. compiler_alloca_pred P fresh_id) /\ (!P. compiler_alloca_pred P comp_get)
Proof
  simp[compiler_alloca_pred_def, compiler_vars_mono_prims, compiler_alloca_code_def,
    new_block_def, fresh_var_def, fresh_label_def, fresh_id_def, comp_get_def, LET_THM]
QED

Theorem compiler_alloca_pred_emit_op:
  !P opc ops. compiler_alloca_pred P (emit_op opc ops)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_alloca_pred_def, compiler_vars_mono_emit_helpers] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `opc = ALLOCA` >>
  asm_simp_tac (srw_ss()) [emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, compiler_alloca_code_def, mk_inst_def, LET_THM] >>
  fs[compiler_alloca_code_def, mk_inst_def]
QED

Theorem compiler_alloca_pred_emit_void:
  !P opc ops. opc <> ALLOCA ==> compiler_alloca_pred P (emit_void opc ops)
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compiler_alloca_pred_def, compiler_vars_mono_emit_helpers, emit_void_def,
    comp_bind_def, fresh_id_def, emit_def, compiler_alloca_code_def, mk_inst_def, LET_THM]
QED

Theorem compiler_alloca_pred_emit_inst:
  !P opc ops outs. opc <> ALLOCA ==> compiler_alloca_pred P (emit_inst opc ops outs)
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compiler_alloca_pred_def, compiler_vars_mono_emit_helpers, emit_inst_def,
    comp_bind_def, fresh_id_def, emit_def, compiler_alloca_code_def, mk_inst_def, LET_THM]
QED

Theorem compiler_alloca_pred_result:
  !P m cs ret cs'.
    compiler_alloca_pred P m /\ m cs = (ret,cs') /\
    (!id ops n. cs.cs_next_var <= n ==> P (mk_inst id ALLOCA ops ["%" ++ toString n])) /\
    compiler_alloca_code P cs ==>
    cs.cs_next_var <= cs'.cs_next_var /\ compiler_alloca_code P cs'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compiler_alloca_pred _ _` (strip_assume_tac o REWRITE_RULE [compiler_alloca_pred_def]) >>
  conj_tac >- (drule_all compiler_vars_mono_result >> simp[]) >>
  qpat_x_assum `!cs. _` (qspec_then `cs` mp_tac) >> simp[]
QED
