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

(* Jump dispatch leaves the data and allocation effect interface intact. *)
Theorem ld_jump_effect:
  f.lf_src = s /\ f.lf_tgt = t /\ f.lf_tv = tn.t_var /\
  ld_vars P A f /\ ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_current_bb = t.vs_current_bb ==>
  ld_vars P A (f with <|lf_src := jump_to lbl s; lf_tgt := jump_to lbl t|>) /\
  ld_memory lo A tn (jump_to lbl s) (jump_to lbl t) /\
  ld_nonghost tn (jump_to lbl s) (jump_to lbl t) /\
  (jump_to lbl s).vs_prev_bb = (jump_to lbl t).vs_prev_bb /\
  (jump_to lbl s).vs_current_bb = (jump_to lbl t).vs_current_bb
Proof
  strip_tac >> gvs[] >>
  gvs[jump_to_def, ld_vars_def, lowerDloadSafetyKernelTheory.ld_memory_def,
     lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
  first_assum MATCH_ACCEPT_TAC
QED
