Theory staticShadowPrim
Ancestors
  staticShadowDefs venomExecSemantics venomCallOracleDefs extCallOracle
  venomState venomInst list finite_map

Theorem static_shadow_pure1:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (exec_pure1 f inst s) (exec_pure1 f inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[exec_pure1_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_pure2:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (exec_pure2 f inst s) (exec_pure2 f inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[exec_pure2_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_pure3:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (exec_pure3 f inst s) (exec_pure3 f inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[exec_pure3_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_read0:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\ f sh = f s ==>
  static_shadow_result_rel (exec_read0 f inst s) (exec_read0 f inst sh)
Proof
  strip_tac >> simp[exec_read0_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_read1:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  (!v. f v sh = f v s) ==>
  static_shadow_result_rel (exec_read1 f inst s) (exec_read1 f inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[exec_read1_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def] >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_write2:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  (!v w. static_shadow_rel (f v w s) (f v w sh) /\
          (f v w s).vs_call_ctx.cc_static) ==>
  static_shadow_result_rel (exec_write2 f inst s) (exec_write2 f inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[exec_write2_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_memory_writes:
  static_shadow_rel s sh ==>
  static_shadow_rel (mstore off v s) (mstore off v sh) /\
  static_shadow_rel (mstore8 off v s) (mstore8 off v sh) /\
  static_shadow_rel (mcopy dst src sz s) (mcopy dst src sz sh) /\
  static_shadow_rel (write_memory_with_expansion off bs s)
                    (write_memory_with_expansion off bs sh)
Proof
  strip_tac >>
  `sh.vs_memory = s.vs_memory` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  simp[mstore_def, mstore8_def, mcopy_def, write_memory_with_expansion_def,
       static_shadow_rel_memory]
QED

