(* An actual constructor write, with a protected caller interval.
   This is a single-segment probe, NOT a whole-callee frame theorem. *)
Theory tupleAssignImmutableDeployIntWritableFrameProbe
Ancestors
  immutableDeployOperandTransfer immutableDeployAssignFacts
  valueEncodingProps loweringStateRelDefs exprLoweringProps
  words

Theorem tuple_immutable_callee_constructor_word_frame:
  compile_imm_store_word imm dst value sa = ((),sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand dst s = SOME (n2w off) /\
  eval_operand value s = SOME v /\
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  32 <= type_memory_size tv /\ off < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = (mstore off v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (off,v) /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  drule_all immutable_assign_declared_region >> strip_tac >>
  qexists_tac `t` >> simp[wordsTheory.w2n_n2w] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  first_x_assum drule >>
  simp[regions_disjoint_def] >> decide_tac
QED
