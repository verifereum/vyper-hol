(* TOP-LEVEL: preservation of compiler-state predicates through the compiler
   monad. Helpers preserve predicates on ALLOCA instructions while checking
   their actual operands, independently of generated output-name bounds. *)
Theory compileCodePreservation
Ancestors
  compileAllocaFlow compileEnv context emitHelper venomInst list pair arithmetic

Definition compiler_preserves_def:
  compiler_preserves (P:compile_state -> bool) action <=>
    !cs. P cs ==> P (SND (action cs))
End

Theorem compiler_preserves_return:
  !P value. compiler_preserves P (comp_return value)
Proof
  simp[compiler_preserves_def, comp_return_def]
QED

Theorem compiler_preserves_bind:
  !P action cont.
    compiler_preserves P action /\ (!value. compiler_preserves P (cont value)) ==>
    compiler_preserves P (comp_bind action cont)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_preserves_def] >> strip_tac >>
  qx_gen_tac `cs` >> DISCH_TAC >> Cases_on `action cs` >>
  rename1 `action cs = (value,mid)` >> simp[comp_bind_def] >>
  `P mid` by (qpat_x_assum `!cs. _` (qspec_then `cs` mp_tac) >> simp[]) >>
  qpat_x_assum `!value cs. _` (qspecl_then [`value`, `mid`] mp_tac) >> simp[]
QED

Theorem compiler_preserves_ignore_bind:
  !P action next.
    compiler_preserves P action /\ compiler_preserves P next ==>
    compiler_preserves P (comp_ignore_bind action next)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_preserves_bind >> simp[]
QED

Theorem compiler_preserves_result:
  !P action cs ret cs'.
    compiler_preserves P action /\ action cs = (ret,cs') /\ P cs ==> P cs'
Proof
  simp_tac bool_ss [compiler_preserves_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `cs` mp_tac) >> simp[]
QED

Theorem compiler_preserves_alloca_prims:
  (!P label. compiler_preserves (compiler_alloca_code P) (new_block label)) /\
  (!P. compiler_preserves (compiler_alloca_code P) fresh_var) /\
  (!P suffix. compiler_preserves (compiler_alloca_code P) (fresh_label suffix)) /\
  (!P. compiler_preserves (compiler_alloca_code P) fresh_id) /\
  (!P. compiler_preserves (compiler_alloca_code P) comp_get)
Proof
  simp[compiler_preserves_def, compiler_alloca_code_def, new_block_def,
    fresh_var_def, fresh_label_def, fresh_id_def, comp_get_def, LET_THM]
QED

Theorem compiler_preserves_alloca_emit_op:
  !P opc ops.
    (opc = ALLOCA ==> !id (n:num). P (mk_inst id ALLOCA ops ["%" ++ toString n])) ==>
    compiler_preserves (compiler_alloca_code P) (emit_op opc ops)
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `opc = ALLOCA` >>
  simp_tac bool_ss [compiler_preserves_def] >> rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, compiler_alloca_code_def, mk_inst_def, LET_THM] >>
  fs[compiler_alloca_code_def, mk_inst_def] >>
  first_x_assum (qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`] mp_tac) >> simp[]
QED

Theorem compiler_preserves_alloca_emit_void:
  !P opc ops. opc <> ALLOCA ==>
    compiler_preserves (compiler_alloca_code P) (emit_void opc ops)
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compiler_preserves_def, compiler_alloca_code_def, emit_void_def,
    comp_bind_def, fresh_id_def, emit_def, comp_return_def, mk_inst_def, LET_THM]
QED

Theorem compiler_preserves_alloca_emit_inst:
  !P opc ops outs. opc <> ALLOCA ==>
    compiler_preserves (compiler_alloca_code P) (emit_inst opc ops outs)
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compiler_preserves_def, compiler_alloca_code_def, emit_inst_def,
    comp_bind_def, fresh_id_def, emit_def, comp_return_def, mk_inst_def, LET_THM]
QED
