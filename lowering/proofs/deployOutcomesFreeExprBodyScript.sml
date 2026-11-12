Theory deployOutcomesFreeExprBody
Ancestors
  deployOutcomesFreeLowering exprLowering exprCallBounds e2eDeployDefs
  supportedExprTraverse pairToolsContext compileEnv emitHelper

Theorem outcomes_free_invalid_expr_call:
  P INVALID /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (invalid_expr_call ty s)))
Proof
  strip_tac >> simp[invalid_expr_call_def] >> pairarg_tac >> simp[] >>
  drule_all (cj 3 outcomes_free_emit_ops) >>
  disch_then (qspecl_then [`[]`, `[]`] mp_tac) >> simp[]
QED

Theorem outcomes_free_expr_child_callback:
  (!ce ty e s. expr_size e < bound /\
     ~supported_expr_exists constructor_call_root e /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e s)))) /\
  P INVALID ==>
  !ce ty e s. ~supported_expr_exists constructor_call_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (expr_child_callback bound f ce ty e s)))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

Theorem outcomes_free_builtin_child_callback:
  (!ce rt ty bi args s. list_size expr_size args < bound /\
     ~precompile_builtin bi /\ ~supported_exprs_exists constructor_call_root args /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce rt ty bi args s)))) /\
  P INVALID ==>
  !ce rt ty bi args s.
    ~precompile_builtin bi /\ ~supported_exprs_exists constructor_call_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (builtin_child_callback bound f ce rt ty bi args s)))
Proof
  rpt strip_tac >> simp[builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

Theorem outcomes_free_type_child_callback:
  (!ce vt ty tb rt args s. list_size expr_size args < bound /\
     ~supported_exprs_exists constructor_call_root args /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce vt ty tb rt args s)))) /\
  P INVALID ==>
  !ce vt ty tb rt args s. ~supported_exprs_exists constructor_call_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (type_child_callback bound f ce vt ty tb rt args s)))
Proof
  rpt strip_tac >> simp[type_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call]
QED

(* These wrappers are parametric in the state invariant.  The join supplies
   opcode exclusion and the generator contracts proved independently. *)
Theorem outcomes_free_lower_value:
  (!s. Q s ==> Q (SND (f ce ty e s))) /\
  (!v s. Q s ==> Q (SND (unwrap_value ce v s))) /\ Q s ==>
  Q (SND (lower_value f ce ty e s))
Proof
  strip_tac >> simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_attribute:
  (!s. Q s ==> Q (SND (f ce ty e s))) /\
  (!ops s. Q s ==> Q (SND (emit_op ADD ops s))) /\ Q s ==>
  Q (SND (compile_attribute f ce rt ty e fld s))
Proof
  strip_tac >> simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_subscript:
  (!ty e s. (e = base_e \/ e = idx_e) /\ Q s ==> Q (SND (f ce ty e s))) /\
  (!v s. Q s ==> Q (SND (unwrap_value ce v s))) /\
  (!v s. Q s ==> Q (SND (compile_keccak256_key v F s))) /\
  (!b k s. Q s ==> Q (SND (compile_mapping_subscript b k s))) /\
  (!b n s. Q s ==> Q (SND (compile_tuple_subscript b n s))) /\
  (!b i d n ws sz sg loc s. Q s ==>
    Q (SND (compile_array_subscript b i d n ws sz sg
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s))) /\ Q s ==>
  Q (SND (compile_subscript f ce rt ty base_e idx_e s))
Proof
  strip_tac >> simp[compile_subscript_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  rename1 `f ce ty base_e s = (vv,s1)` >>
  `Q s1` by metis_tac[pairTheory.SND] >>
  Cases_on `place_type ce base_e`
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt pairarg_tac >> simp[] >>
      metis_tac[outcomes_free_lower_value, pairTheory.SND]) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt pairarg_tac >> simp[] >>
  metis_tac[outcomes_free_lower_value, pairTheory.SND]
QED
