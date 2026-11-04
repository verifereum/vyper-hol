(* Successful branch dispatch uses pointwise selector agreement, not
   whole-list evaluation: branch label operands need not evaluate. *)
Theory lowerDloadSafetyControl
Ancestors
  lowerDloadSafetyValues lowerDloadSafetyRelation ptrDiscipline unitShapeDefs
  venomState venomInst venomExecSemantics pointerConfinedDefs memLocDefs
  finite_map list pred_set

Theorem ld_control_destination:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuelT CT inst f.lf_tgt = OK t1 ==>
  ?lbl. t1 = jump_to lbl f.lf_tgt /\
        step_inst fuelS CS inst f.lf_src = OK (jump_to lbl f.lf_src)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op f.lf_src = eval_operand op f.lf_tgt` by
    (gen_tac >> strip_tac >> irule ld_vars_operand_equal >>
     simp[] >> reverse conj_tac
     >- (conj_tac
         >- (irule ld_vars_nonpointer_provenance >>
         qexistsl_tac [`A`, `P`] >> simp[] >>
         gen_tac >> disch_tac >> irule ld_ptr_use_scalar >> simp[] >>
         qexists_tac `inst` >> gvs[] >>
         simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
         metis_tac[]) >>
     gen_tac >> disch_then SUBST_ALL_TAC >> conj_tac
     >- metis_tac[ld_inst_input_ir] >> conj_tac
     >- (irule ld_numeric_operand_nonopaque >> simp[] >>
         qexists_tac `inst` >> gvs[]) >>
     `op_taint tn (Var v) = {}` by
       (irule ld_numeric_operand_untainted >> simp[] >>
        qexistsl_tac [`f.lf_fn`, `inst`, `f.lf_src`] >> gvs[]) >>
     gvs[op_taint_def]) >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst _ = _` mp_tac >>
  gvs[] >> simp[Once step_inst_base_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> simp[] >>
  metis_tac[]
QED
