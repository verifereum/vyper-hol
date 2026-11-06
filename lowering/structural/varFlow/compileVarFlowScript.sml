(* TOP-LEVEL: compiler actions monotonically allocate generated variable
   names. Helpers compose the property through the real compiler monad. *)
Theory compileVarFlow
Ancestors
  compileEnv emitHelper venomInst list pair arithmetic

Definition compiler_vars_mono_def:
  compiler_vars_mono m <=> !cs. cs.cs_next_var <= (SND (m cs)).cs_next_var
End

Theorem compiler_vars_mono_return:
  !x. compiler_vars_mono (comp_return x)
Proof
  simp[compiler_vars_mono_def, comp_return_def]
QED

Theorem compiler_vars_mono_bind:
  !m f. compiler_vars_mono m /\ (!value. compiler_vars_mono (f value)) ==>
    compiler_vars_mono (comp_bind m f)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_vars_mono_def] >> strip_tac >> qx_gen_tac `cs` >>
  Cases_on `m cs` >> rename1 `m cs = (step_ret,mid)` >> simp[comp_bind_def] >>
  irule LESS_EQ_TRANS >> qexists_tac `mid.cs_next_var` >> conj_tac
  >- (qpat_x_assum `!cs. cs.cs_next_var <= (SND (m cs)).cs_next_var`
        (qspec_then `cs` mp_tac) >> simp[]) >>
  qpat_x_assum `!value cs. _` (qspecl_then [`step_ret`, `mid`] mp_tac) >> simp[]
QED

Theorem compiler_vars_mono_ignore_bind:
  !m f. compiler_vars_mono m /\ compiler_vars_mono f ==>
    compiler_vars_mono (comp_ignore_bind m f)
Proof
  rpt gen_tac >> rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_vars_mono_bind >> simp[]
QED

Theorem compiler_vars_mono_prims:
  (!inst. compiler_vars_mono (emit inst)) /\
  (!label. compiler_vars_mono (new_block label)) /\
  compiler_vars_mono fresh_var /\ (!suffix. compiler_vars_mono (fresh_label suffix)) /\
  compiler_vars_mono fresh_id /\ compiler_vars_mono comp_get
Proof
  simp[compiler_vars_mono_def, emit_def, new_block_def, fresh_var_def,
    fresh_label_def, fresh_id_def, comp_get_def, LET_THM]
QED

Theorem compiler_vars_mono_emit_helpers:
  (!opc ops outs. compiler_vars_mono (emit_inst opc ops outs)) /\
  (!opc ops. compiler_vars_mono (emit_op opc ops)) /\
  (!opc ops. compiler_vars_mono (emit_void opc ops))
Proof
  rw[emit_inst_def, emit_op_def, emit_void_def] >>
  rpt (FIRST [irule compiler_vars_mono_bind, irule compiler_vars_mono_ignore_bind] >>
    rw[compiler_vars_mono_prims, compiler_vars_mono_return]) >>
  rw[compiler_vars_mono_prims, compiler_vars_mono_return]
QED

Theorem compiler_vars_mono_result:
  !m cs ret cs'. compiler_vars_mono m /\ m cs = (ret,cs') ==> cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compiler_vars_mono m` (mp_tac o REWRITE_RULE [compiler_vars_mono_def]) >>
  disch_then (qspec_then `cs` mp_tac) >> simp[]
QED
