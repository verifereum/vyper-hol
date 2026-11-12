Theory typedCopyLoopAddressPathPtr
Ancestors
 typedCopyLoopControlPathPtr typedCopyLoopHeaderPtr annAssignPtrLength
 typedCopyPtr bodyPtrDefs fragGasPathPtr ptrDiscipline venomInst
 venomExecSemantics venomState finite_map words arithmetic list

Theorem typed_copy_loop_address_path_ptr:
 !D ctx fn PG G tn s bb pre post ctr so doff sp dp sr dr id i ss ds a b S T.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
 [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
  mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
  mk_inst (id+2) ADD [Var sr;Var so] [sp];
  mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ++ post /\
 s.vs_inst_idx = LENGTH pre /\
 lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
 lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
 ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
 ALL_DISTINCT [so;doff;sp;dp] /\
 (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
 i*ss < S /\ i*ss+ss <= S /\ i*ds < T /\ i*ds+ds <= T /\
 w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = s.vs_current_bb /\ sf.vs_inst_idx = LENGTH pre + 4 /\
 ~sf.vs_halted /\ sf.vs_allocas = s.vs_allocas /\
 sf.vs_fmp = s.vs_fmp /\ sf.vs_requests = s.vs_requests /\
 tnf.t_imm = tn.t_imm /\
 lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
 lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
 ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
 sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
 tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
 (!p. ~MEM p [so;doff;sp;dp] ==>
 lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
 op_taint tnf (Var p)=op_taint tn (Var p))
Proof
 typedCopyLoopAmbientLib.address_witnesses >>
 conj_tac >- suspend "path" >>
 `s4.vs_current_bb = s.vs_current_bb /\ s4.vs_inst_idx = LENGTH pre + 4 /\
  ~s4.vs_halted /\ s4.vs_allocas = s.vs_allocas /\
  s4.vs_fmp = s.vs_fmp /\ s4.vs_requests = s.vs_requests /\
  tn4.t_imm = tn.t_imm` by
  simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
   update_var_def, Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
   step_taint_def, imm_taint_def, mk_inst_def] >>
 simp[] >> suspend "resources"
QED

Resume typed_copy_loop_address_path_ptr[path]:
 `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
  (simp[Abbr `g1`, Abbr `tn1`, Abbr `s1`, NoAsms] >>
   irule typed_copy_control_arith_path_ptr >>
   simp[update_var_def] >>
   qexistsl [`id`, `MUL`, `[Var ctr;Lit (n2w ss)]`] >>
   simp[update_var_def, get_instruction_def, EL_APPEND_EQN, op_taint_def,
     step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
     eval_operand_def, word_mul_n2w, DISJ_IMP_THM, FORALL_AND_THM] >>
   gvs[op_taint_def]) >>
 `gas_path_ptr D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)` by
  (simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, NoAsms] >>
   irule typed_copy_control_arith_path_ptr >>
   simp[Abbr `s1`, update_var_def] >>
   qexistsl [`id+1`, `MUL`, `[Var ctr;Lit (n2w ds)]`] >>
   simp[Abbr `tn1`, update_var_def, lookup_var_def,
     get_instruction_def, EL_APPEND_EQN, op_taint_def, FLOOKUP_UPDATE,
     step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
     eval_operand_def, word_mul_n2w, DISJ_IMP_THM, FORALL_AND_THM] >>
   gvs[lookup_var_def, op_taint_def, FLOOKUP_UPDATE, word_mul_n2w]) >>
 `op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {}` by
  gvs[ptr_covers_def] >>
 `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)` by
  (simp[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`, NoAsms] >>
   irule annassign_copy_len_binop_path_ptr >>
   simp[] >>
   gvs[Abbr `s2`, Abbr `s1`, Abbr `tn2`, Abbr `tn1`,
     get_instruction_def, EL_APPEND_EQN, update_var_def, lookup_var_def,
     eval_operand_def, op_taint_def, FLOOKUP_UPDATE, ADD1]) >>
 `gas_path_ptr D 0 ctx fn PG g3 tn3 s3 0 g4 tn4 (OK s4)` by
  (simp[Abbr `g4`, Abbr `tn4`, Abbr `s4`, Abbr `t4`, NoAsms] >>
   irule annassign_copy_len_binop_path_ptr >>
   simp[] >>
   simp[Abbr `tn3`, Abbr `t3`, copy_len_binop_ghost_frame] >>
   gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`,
     Abbr `tn2`, Abbr `tn1`, get_instruction_def, EL_APPEND_EQN,
     update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
     FLOOKUP_UPDATE, ADD1]) >>
 metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume typed_copy_loop_address_path_ptr[resources]:
 typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers
QED

Finalise typed_copy_loop_address_path_ptr
