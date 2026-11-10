(* Resource boundary for the concrete array element-copy endpoint. *)
Theory bodyIntCallFamStmtForArrayResources
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArrayFrame
  bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier
  stmtSimForArrayLoop stmtSimProps compileEnv venomState venomExecSemantics
  venomInst finite_map list rich_list intCallFrame

Theorem intcall_array_copy_entry:
  array_entry_inputs fp.jc_ctx fp.jc_func ce bc fp.jc_cx es s id p sz dst
    ainst tv v fty (get_tenv fp.jc_cx) sa sb0 idx saved arrbase k stride
    ov ep j3 j4 bb sb0 /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  type_memory_bytes ce fty < 2 ** 64 /\
  sc.cs_next_var <= sb0.cs_next_var /\ local_ptrs_reserved bc sb0 /\
  (!x. not_fresh_at sc x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?s2. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK s2) /\
    intcall_joint_res fp bc (extend_local env id fty F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes) sb0 s2 /\
    s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    (!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s) /\
    s2.vs_allocas = s.vs_allocas /\ s.vs_alloca_next <= s2.vs_alloca_next
Proof
  strip_tac >>
  qhdtm_x_assum `array_entry_inputs` mp_tac >>
  rewrite_tac[array_entry_inputs_def] >> strip_tac >>
  drule_all intcall_array_body_entry_run_frame >>
  disch_then (qspecl_then [`j4`, `j3`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    (simp[mk_inst_def] >> metis_tac[iter_memory_copy_no_gas]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  drule_all intcall_array_prefix_continuation_frame >> strip_tac >>
  `s.vs_alloca_next <= s2.vs_alloca_next` by
    (drule intcall_marked_path_frontier_mono >> simp[]) >>
  `allocas_above fp.jc_lo s2` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!a len. fp.jc_prot a len ==>
     mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> simp[] >> first_x_assum irule >> disj1_tac >>
     fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
        allocas_above_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `lookup_var p s2 = SOME dst` by
    (fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_def]) >>
  qexists_tac `s2` >> simp[] >>
  irule intcall_for_declared_entry >> metis_tac[]
QED
