Theory bodyIntCallCompilerEmit
Ancestors
  bodyIntCallCompilerInterval loweringHalt emitHelper compileEnv
  exprLoweringProps venomInst fragExec bodyIntCallEmitBoundary exprLowering

Theorem intcall_interval_fresh_var:
  intcall_compiler_interval k a (SND (fresh_var a))
Proof
  simp[intcall_compiler_interval_def, ci_mono_fresh_var, fresh_var_def]
QED

Theorem intcall_interval_fresh_label:
  intcall_compiler_interval k a (SND (fresh_label suffix a))
Proof
  simp[intcall_compiler_interval_def, ci_mono_fresh_label, fresh_label_def]
QED

Theorem intcall_interval_new_block:
  intcall_compiler_interval k a (SND (new_block label a))
Proof
  simp[intcall_compiler_interval_def, ci_mono_new_block, new_block_def]
QED

Theorem intcall_interval_emit_inst:
  (opc = ALLOCA ==> !out. MEM out outs ==>
     ?j. k <= j /\ out = STRING #"%" (toString j)) ==>
  intcall_compiler_interval k a (SND (emit_inst opc ops outs a))
Proof
  strip_tac >> rewrite_tac[intcall_compiler_interval_def] >> conj_tac
  >- simp[ci_mono_emit_inst] >>
  rpt gen_tac >> strip_tac >>
  `n = a.cs_next_id` by
    gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, pairTheory.UNCURRY] >>
  qexists `mk_inst a.cs_next_id opc ops outs` >>
  conj_tac
  >- (irule emit_inst_fn_member >>
      qexists `SND (emit_inst opc ops outs a)` >>
      simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
           fresh_id_def, emit_def, pairTheory.UNCURRY]) >>
  simp[mk_inst_def]
QED

Theorem intcall_interval_emit_void:
  intcall_compiler_interval k a (SND (emit_void opc ops a))
Proof
  `emit_void opc ops = emit_inst opc ops []` by
    simp[emit_void_def, emit_inst_def] >>
  simp[intcall_interval_emit_inst]
QED

Theorem intcall_interval_emit_op:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (emit_op opc ops a))
Proof
  strip_tac >> rewrite_tac[intcall_compiler_interval_def] >> conj_tac
  >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> strip_tac >>
  `n = a.cs_next_id` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def,
        pairTheory.UNCURRY] >>
  qexists `mk_inst a.cs_next_id opc ops
    [STRING #"%" (toString a.cs_next_var)]` >>
  conj_tac
  >- (irule emit_inst_fn_member >>
      qexists `SND (emit_inst opc ops
        [STRING #"%" (toString a.cs_next_var)] a)` >>
      conj_tac
      >- simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
              pairTheory.UNCURRY] >>
      qpat_x_assum `fn_has_code _ _ _` mp_tac >>
      simp[fn_has_code_def, emitted_blocks_def,
           emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def,
           pairTheory.UNCURRY]) >>
  simp[mk_inst_def] >> strip_tac >> qexists `a.cs_next_var` >> simp[]
QED

Theorem intcall_interval_return:
  intcall_compiler_interval k a (SND (comp_return v a))
Proof
  simp[comp_return_def, intcall_compiler_interval_refl]
QED

Theorem intcall_interval_fresh_vars:
  !n a. intcall_compiler_interval k a (SND (fresh_vars n a))
Proof
  Induct >> simp[fresh_vars_def, intcall_interval_return] >> gen_tac >>
  irule intcall_compiler_interval_bind >>
  simp[intcall_interval_fresh_var] >> rpt gen_tac >>
  irule intcall_compiler_interval_bind >> simp[intcall_interval_return]
QED

Theorem intcall_interval_block_sequence:
  !a. intcall_compiler_interval k a
    (SND (comp_ignore_bind (emit_void opc ops)
      (comp_ignore_bind (new_block label) (emit_void opc' ops')) a))
Proof
  gen_tac >> irule intcall_compiler_interval_ignore_bind >>
  simp[intcall_interval_emit_void] >> gen_tac >>
  irule intcall_compiler_interval_ignore_bind >>
  simp[intcall_interval_new_block, intcall_interval_emit_void]
QED

Theorem intcall_interval_multi_vvs:
  (!e a. intcall_compiler_interval k a
    (SND (cfn cenv (expr_type e) e a))) ==>
  !es a. intcall_compiler_interval k a
    (SND (compile_multi_vvs cfn cenv es a))
Proof
  strip_tac >> Induct >>
  simp[compile_multi_vvs_def, intcall_interval_return] >> gen_tac >>
  irule intcall_compiler_interval_bind >> simp[] >> rpt gen_tac >>
  irule intcall_compiler_interval_bind >> simp[intcall_interval_return]
QED

Theorem intcall_interval_fresh_outputs:
  k <= a.cs_next_var /\ fresh_vars n a = (outs,b) ==>
  intcall_compiler_interval k a
    (SND (emit_inst opc ops outs b))
Proof
  strip_tac >> irule intcall_compiler_interval_trans >> qexists `b` >>
  conj_tac
  >- (qspec_then `n` (qspec_then `a` mp_tac)
        intcall_interval_fresh_vars >> simp[]) >>
  irule intcall_interval_emit_inst >> strip_tac >> rpt strip_tac >>
  drule fresh_vars_result >> strip_tac >> gvs[listTheory.MEM_GENLIST] >>
  qexists `a.cs_next_var + i` >> simp[]
QED
