Theory deployOutcomesFreeAggregateBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list

Theorem outcomes_free_builtin_environment:
  (!item st. Q st ==> Q (SND (compile_env_var item st))) /\
  (!st. Q st ==> Q (SND (compile_builtin_calldatasize st))) /\
  ((?item. bi = Env item) \/ bi = CalldataLen) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >> Cases_on `bi` >> gvs[] >>
  simp[compile_builtin_dispatch_body_def, exprBopLoweringTheory.as_stack_val_pair]
QED

Theorem outcomes_free_builtin_concat:
  (!sz st. Q st ==> Q (SND (compile_alloc_buffer sz st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ADD ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_op MLOAD ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_void MSTORE ops st))) /\
  (!es ptr infos off st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_concat f ce es ptr infos off st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty (Concat n) args s))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  `Q st2` by metis_tac[pairTheory.SND] >>
  `Q st3` by metis_tac[pairTheory.SND] >>
  `Q st3a` by metis_tac[pairTheory.SND] >>
  `Q st3b` by metis_tac[pairTheory.SND] >>
  `Q st4a` by metis_tac[pairTheory.SND] >>
  `Q st4` by metis_tac[pairTheory.SND] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_builtin_make_array:
  (!sz st. Q st ==> Q (SND (compile_alloc_buffer sz st))) /\
  (!es tys ptr off st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_make_tuple f ce es tys ptr off st))) /\
  (!es ety sz lw ptr st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_make_array f ce es ety sz lw ptr st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty (MakeArray ety bnd) args s))
Proof
  strip_tac >> Cases_on `ety` >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[deployOutcomesFreeGeneratorsTheory.as_ptr_val_pair] >>
  metis_tac[pairTheory.SND]
QED
