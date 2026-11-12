(* Operational memory witnesses shared by Dynamic staging and its counted path. *)
Theory appendDynamicMemoryStepPtr
Ancestors typedCopyPtr exprSimPtrTopLevelImmutableCopy annAssignPtrCopy fragExecPtr
  ptrDiscipline venomExecSemantics venomState venomInst finite_map words

Theorem dynamic_mload_clean_step_ptr:
  !PG G tn s id src out a.
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
    ?u Gf tf.
      u = update_var out (mload (w2n a) s) s /\
      step_inst_base (mk_inst id MLOAD [Var src] [out]) s = OK u /\
      Gf = step_prov PG G (mk_inst id MLOAD [Var src] [out]) u /\
      tf = step_taint (mk_inst id MLOAD [Var src] [out]) s u tn /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id MLOAD [Var src] [out]) s) /\
      (u with vs_vars := s.vs_vars) = s /\
      lookup_var out u = SOME (mload (w2n a) s) /\
      op_taint tf (Var out) = {} /\ tf.t_mem = tn.t_mem /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      (!p. p <> out ==> lookup_var p u = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `update_var out (mload (w2n a) s) s` >>
  qexists_tac `step_prov PG G (mk_inst id MLOAD [Var src] [out])
    (update_var out (mload (w2n a) s) s)` >>
  qexists_tac `step_taint (mk_inst id MLOAD [Var src] [out]) s
    (update_var out (mload (w2n a) s) s) tn` >>
  simp[] >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> irule ptr_inst_ok_mload >> simp[]) >>
  simp[mload_ghost_clean, eval_operand_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, op_taint_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem dynamic_mstore_clean_step_ptr:
  !PG G tn s id dst value a w.
    ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    ?u tf.
      u = mstore (w2n a) w s /\
      step_inst_base (mk_inst id MSTORE [Var dst;value] []) s = OK u /\
      step_prov PG G (mk_inst id MSTORE [Var dst;value] []) u = G /\
      tf = step_taint (mk_inst id MSTORE [Var dst;value] []) s u tn /\
      tf = (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id MSTORE [Var dst;value] []) s) /\
      (u with vs_memory := s.vs_memory) = s
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `mstore (w2n a) w s` >>
  qexists_tac `step_taint (mk_inst id MSTORE [Var dst;value] []) s
    (mstore (w2n a) w s) tn` >> simp[] >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  drule_all toplevel_immutable_mstore_ghost_frame >> strip_tac >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule ptr_inst_ok_mstore >> simp[]) >>
  simp[mstore_def]
QED

Theorem dynamic_mcopy_covered_step_ptr:
  !PG G tn s id dst src count_op a b n.
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
    ?u tf.
      u = mcopy (w2n b) (w2n a) (w2n n) s /\
      step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s = OK u /\
      step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] []) u = G /\
      tf = step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s u tn /\
      (!D fuel ctx fn. ~ctx_has_dalloca ctx ==>
        ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id MCOPY [Var dst;Var src;count_op] []) s) /\
      (u with vs_memory := s.vs_memory) = s /\
      tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      tf.t_imm = tn.t_imm /\
      tf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+w2n n}) UNION
        {w2n b+i | i < w2n n /\ w2n a+i IN tn.t_mem}
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `mcopy (w2n b) (w2n a) (w2n n) s` >>
  qexists_tac `step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
    (mcopy (w2n b) (w2n a) (w2n n) s) tn` >> simp[] >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  simp[mcopy_operand_ghost_frame, eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]) >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[step_taint_def, instruction_accessors, set_var_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def]
QED
