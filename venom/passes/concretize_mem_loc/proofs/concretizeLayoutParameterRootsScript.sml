Theory concretizeLayoutParameterRoots
Ancestors frameRelocationOpaque venomExecSemantics venomState list words

(* Indexed roots deliberately allow relocated pointers and opaque tokens. *)
Definition parameter_roots_def:
  parameter_roots R xs ys <=>
    LENGTH xs = LENGTH ys /\
    (!i. i < LENGTH xs ==> R i (EL i xs) (EL i ys))
End

Theorem parameter_roots_update_var:
  parameter_roots R (update_var v x s).vs_params
                    (update_var w y t).vs_params <=>
  parameter_roots R s.vs_params t.vs_params
Proof
  simp[update_var_def]
QED

Theorem parameter_roots_setup_callee:
  parameter_roots R args args' /\
  setup_callee fn args s = SOME sc /\ ~NULL gn.fn_blocks ==>
  ?tc. setup_callee gn args' t = SOME tc /\
       parameter_roots R sc.vs_params tc.vs_params
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED

Theorem parameter_roots_read:
  (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM) /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  parameter_roots R s.vs_params t.vs_params /\
  step_inst_base inst s = OK post ==>
  ?x y. post = update_var out x s /\
        step_inst_base inst t = OK (update_var out y t) /\
        R (w2n idx) x y /\
        parameter_roots R post.vs_params (update_var out y t).vs_params
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[parameter_roots_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl [`EL (w2n idx) s.vs_params`, `EL (w2n idx) t.vs_params`] >>
  simp[step_inst_base_def, parameter_roots_def, update_var_def]
QED

Theorem parameter_roots_retpc_read:
  inst.inst_opcode = RETPC_PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] ==>
  step_inst_base inst s = OK (update_var out s.vs_return_pc_token s) /\
  step_inst_base inst t = OK (update_var out t.vs_return_pc_token t)
Proof
  simp[step_inst_base_def]
QED
