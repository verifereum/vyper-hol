Theory algebraicOptDemandProofs
Ancestors
  algebraicOptRelationProofs algebraicOptDefs dfgAnalysisProps
  dfgDefs passSharedDefs venomInst venomState venomWf list
  algebraicOptCmpLayoutProofs allocaRemapSSA

Theorem ao_nontruthy_use_exact:
  !fn use x.
    MEM use (fn_insts fn) /\ MEM (Var x) use.inst_operands /\
    ~is_truthy_inst use.inst_opcode ==> ao_main_exact fn x
Proof
  rpt strip_tac >>
  `MEM x (operand_vars use.inst_operands)` by
    metis_tac[MEM_operand_vars_eq_Var] >>
  drule_all dfg_build_function_uses_complete >> strip_tac >>
  simp[ao_main_exact_def] >>
  Cases_on `?i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs`
  >- (gvs[] >> disj2_tac >> qexists `i` >> simp[] >> disj2_tac >>
      strip_tac >>
      Cases_on `i.inst_outputs` >> gvs[ao_all_truthy_def] >>
      rename1 `i.inst_outputs = out::rest` >>
      Cases_on `rest` >> gvs[ao_all_truthy_def, EVERY_MEM] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem ao_nontruthy_operand_exact_read:
  !fn V s r use a.
    ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
    MEM use (fn_insts fn) /\
    ~is_truthy_inst use.inst_opcode /\ MEM a use.inst_operands /\
    (!x. a = Var x ==> x IN V) ==>
    eval_operand a s = eval_operand a r
Proof
  rpt strip_tac >> Cases_on `a` >> simp[eval_operand_def] >>
  gvs[ao_main_observations_def, ao_main_lookup_def] >>
  metis_tac[ao_nontruthy_use_exact]
QED

Theorem ao_all_truthy_output_inexact:
  !fn inst out.
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    MEM out inst.inst_outputs /\ inst.inst_opcode <> ISZERO /\
    ao_all_truthy (dfg_build_function fn) inst ==>
    ~ao_main_exact fn out
Proof
  rpt strip_tac >>
  gvs[ao_main_exact_def] >>
  metis_tac[ssa_unique_output]
QED
