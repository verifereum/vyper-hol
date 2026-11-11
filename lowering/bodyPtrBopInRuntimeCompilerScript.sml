Theory bodyPtrBopInRuntimeCompiler
Ancestors exprLowering context compileEnv bodyPtrBopInHeaderCode
  bodyPtrBopInLoopLayout fragExec rich_list


Theorem membership_runtime_loop_extends:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) NONE is_in sa = (op,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  simp[cs_extends_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_runtime_header_extends:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >>
  drule (SRULE [] (GEN_ALL membership_runtime_header_layout)) >> strip_tac >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED
