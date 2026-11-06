(* Header observation, not raw MCOPY, forces source cleanliness. *)
Theory bodyPtrStructLitHeaderClean
Ancestors bodyPtrStructLitFirstUse ptrSafeRun pred_set arithmetic
  context emitHelper compileEnv venomInst

Theorem mload_add_header_clean:
  !fn tn load add s s' t x p a.
    load.inst_opcode = MLOAD /\ load.inst_operands = [p] /\
    load.inst_outputs = [x] /\ eval_operand p s = SOME a /\
    add.inst_opcode = ADD /\ MEM (Var x) add.inst_operands /\
    taint_ok fn (step_taint load s s' tn) add t ==>
    !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    metis_tac[mload_tainted_header_add_rejected] >>
  gvs[ptrDisciplineTheory.mem_word_taint_def, EXTENSION] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `i - w2n a` mp_tac) >> simp[] >> decide_tac
QED

Theorem mload_add_ghost_header_clean:
  !fn tn tn1 G G1 PG fuel ctx load add s s1 t x p a.
    load.inst_opcode = MLOAD /\ load.inst_operands = [p] /\
    load.inst_outputs = [x] /\ eval_operand p s = SOME a /\
    step_inst fuel ctx load s = OK s1 /\
    ghost_step fuel ctx PG G tn load s = (G1,tn1) /\
    add.inst_opcode = ADD /\ MEM (Var x) add.inst_operands /\
    taint_ok fn tn1 add t ==>
    !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `tn1 = step_taint load s s1 tn` by
    gvs[ghost_step_def] >>
  metis_tac[mload_add_header_clean]
QED

Theorem compile_bytestring_copy_len_prefix:
  !p sa out sb.
    compile_bytestring_copy_len p sa = (out,sb) ==>
    ?sm sn x y.
      emit_op MLOAD [p] sa = (Var x,sm) /\
      emit_op ADD [Var x; Lit 31w] sm = (Var y,sn)
Proof
  simp[compile_bytestring_copy_len_def, comp_bind_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >>
  simp[comp_ignore_bind_def, comp_bind_def, emit_def, comp_return_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* The observed length is precisely the value consumed by the next ADD.
   No analogous observation is present in a raw MCOPY-only return. *)
Theorem compile_bytestring_copy_len_header_clean:
  !p sa out sb.
    compile_bytestring_copy_len p sa = (out,sb) ==>
    ?sm sn x y.
      emit_op MLOAD [p] sa = (Var x,sm) /\
      emit_op ADD [Var x; Lit 31w] sm = (Var y,sn) /\
      (!fn tn tn1 G G1 PG fuel ctx s s1 t a.
        eval_operand p s = SOME a /\
        step_inst fuel ctx (mk_inst sa.cs_next_id MLOAD [p] [x]) s = OK s1 /\
        ghost_step fuel ctx PG G tn
          (mk_inst sa.cs_next_id MLOAD [p] [x]) s = (G1,tn1) /\
        taint_ok fn tn1 (mk_inst sm.cs_next_id ADD [Var x; Lit 31w] [y]) t ==>
        !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_bytestring_copy_len_prefix >> strip_tac >>
  qexistsl_tac [`sm`, `sn`, `x`, `y`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) mload_add_ghost_header_clean >>
  simp[mk_inst_def] >>
  strip_tac >>
  first_x_assum (drule_at (Pat `taint_ok _ _ _ _`)) >>
  simp[mk_inst_def] >> strip_tac >> gvs[mk_inst_def] >> metis_tac[]
QED
