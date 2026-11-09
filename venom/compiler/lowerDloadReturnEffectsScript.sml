(* RET effects preserve ordinary values, not the opaque final token. *)
Theory lowerDloadReturnEffects
Ancestors
  lowerDloadSafetyAssemblyPremises lowerDloadOracleCallAssembly
  lowerDloadSafetyValues lowerDloadSafetyAmbient lowerDloadSafetyKernel
  lowerDloadSafetyRelation pointerConfinedDefs memLocDefs
  o1LowerDloadOpaque o1LowerDloadGhost ptrDiscipline unitShapeDefs
  venomExecSemantics venomExecProofs venomState venomInst finite_map list rich_list

Theorem ld_sync_ret_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ inst.inst_opcode = RET /\
  step_inst_base inst t = IntRet rt u ==>
  ?rs e. step_inst 0 C inst s = IntRet rs e /\
    step_inst 0 C' inst t = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo A tn e u /\ ld_nonghost tn e u
Proof
  strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  drule ld_sync_active >> strip_tac >>
  qabbrev_tac `f = HD frames` >>
  `!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op t) <=> IS_SOME (eval_operand op s))` by
    (rpt strip_tac >>
     `!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn)` by
       metis_tac[ld_inst_input_ir] >>
     drule ld_vars_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_prov f.lf_H op = NONE` by
    (rpt strip_tac >> irule ld_vars_nonpointer_provenance >>
     qexistsl_tac [`A`,`P`] >> asm_rewrite_tac[] >>
     qx_gen_tac `v` >> disch_tac >>
     irule ld_ptr_use_scalar >> conj_tac
     >- (qexists_tac `inst` >> asm_rewrite_tac[] >>
         gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
     asm_rewrite_tac[] >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `opaque_use_ok fn` by fs[fn_shape_ok_def] >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `inst.inst_operands <> []` by (Cases_on `inst.inst_operands` >> fs[]) >>
     `MEM op inst.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
     `op_taint tn op = {}` by metis_tac[ret_operand_untainted] >>
     `eval_operand op f.lf_src = eval_operand op f.lf_tgt` suffices_by
       asm_rewrite_tac[] >>
     irule ld_vars_operand_equal >>
     (reverse conj_tac >- metis_tac[]) >>
     qx_gen_tac `v` >> disch_tac >>
     conj_tac >- metis_tac[ld_inst_input_ir] >>
     conj_tac >- metis_tac[ret_front_non_retpc] >>
     gvs[op_taint_def]) >>
  `?rs. step_inst_base inst s = IntRet rs s /\
     rs.iret_values = rt.iret_values /\ rt.iret_adopt_fmp = NONE /\
     rs.iret_adopt_fmp = NONE /\ u = t` by
    (irule ret_front_transfer >> asm_rewrite_tac[] >> metis_tac[]) >>
  gvs[] >> qexistsl_tac [`rs`,`f.lf_src`] >>
  simp[step_inst_non_invoke] >> metis_tac[ld_sync_memory]
QED

val _ = if null (hyp ld_sync_ret_effect) then ()
        else raise Fail "ld_sync_ret_effect has hypotheses";
