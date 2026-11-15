(* The counted bytes path restores the ordinary immutable statement relation. *)
Theory immutableAssignBytesOutcomeMem
Ancestors
  immutableAssignBytesPathMem immutableAssignCompose immutableDeployAssignAdmissible
  stmtSimDefs exprSimHypsDefs loweringPosts context compileEnv venomState
  loweringStateRelDefs arithmetic words

Theorem immutable_assign_bytes_mem_stmt_post:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty
    (type_memory_bytes ce ity) su = ((),sb) /\
  is_bytestring_type ity /\ is_bytestring_type sty /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv v /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at su x) /\
  (!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand op s = SOME a /\ mload (w2n a) s = n2w len /\
  val_in_memory itv v (w2n a) s.vs_memory /\
  len + 63 < dimword (:256) /\
  32 * (1 + word_size len) <= type_memory_size itv /\
  w2n a + 32 * (1 + word_size len) < dimword (:256) /\
  off + type_memory_size itv < dimword (:256) /\
  regions_disjoint off (type_memory_size itv) (w2n a) (val_footprint itv v) /\
  (!j. j < 1 + word_size len ==>
    w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
    w2n ((n2w off:bytes32)+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin t /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `immutable_value_admissible itv v` by
    metis_tac[evaluated_immutable_admissible] >>
  mp_tac (Q.INST [`dst` |-> `Lit (n2w off)`, `src` |-> `op`,
    `dty` |-> `ity`, `dtv` |-> `itv`, `sl` |-> `loc`,
    `memsz` |-> `type_memory_bytes ce ity`, `sm` |-> `su`,
    `imm` |-> `ce.ce_imm_alloca`, `b` |-> `n2w off`]
    (SPEC_ALL immutable_assign_bytes_mem_path_endpoint)) >>
  impl_tac >- (simp[eval_operand_def] >> metis_tac[]) >>
  strip_tac >> suspend "post"
QED

Resume immutable_assign_bytes_mem_stmt_post[post]:
  `w2n (n2w off : bytes32) = off` by simp[w2n_n2w] >>
  `stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule immutable_assign_suffix_stmt_post >> simp[] >>
     qexistsl_tac [`env`, `id`, `itv`, `ity`, `off`, `v`] >> simp[] >>
     rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  qexists_tac `t` >> gvs[]
QED

Finalise immutable_assign_bytes_mem_stmt_post
