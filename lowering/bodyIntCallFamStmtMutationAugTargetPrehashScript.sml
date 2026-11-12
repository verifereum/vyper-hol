(* Readonly dynamic-key prehash at a concrete memory-layout boundary. *)
Theory bodyIntCallFamStmtMutationAugTargetPrehash
Ancestors
  bodyIntCallFamStmtMutationBinop bodyIntCallJointContract
  exprSimMapKey exprSimHash exprSimHashBoundary exprLoweringProps compileEnv byte venomState list rich_list loweringStateRelDefs

Theorem intcall_key_prehash:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_keccak256_key key F sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      eval_operand op u = SOME (word_of_bytes_be (Keccak_256_w64 bs))
Proof
  strip_tac >> drule_all compile_keccak256_key_run >> strip_tac >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) (emitted_insts sa sb) /\
   sb.cs_next_var = sa.cs_next_var + 3` by
    metis_tac[mapping_suffix_shape] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (drule hash_run_path >>
     disch_then (qspecl_then [`t`, `s`, `emitted_insts sa sb`, `fp.jc_ctx`] mp_tac) >>
     fs[same_blocks_def, EVERY_MEM]) >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, word_of_bytes_be_def] >>
  irule intcall_expr_cont_readonly_path >> simp[] >>
  `local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    metis_tac[hash_readonly_state_rel] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    gvs[venom_state_component_equality] >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (rpt strip_tac >> gvs[lookup_var_def]) >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qexistsl [`F`, `0`] >> gvs[]
QED
