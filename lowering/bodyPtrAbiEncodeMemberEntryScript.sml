(* Checked source-address entry of an arbitrary complex member. *)
Theory bodyPtrAbiEncodeMemberEntry
Ancestors
  bodyPtrAbiEncodeOffset bodyPtrAbiEncodeStaticChild abiEncoderMemberCode
  abiEncoder abiDecoderContract abiDecoderReentry emitHelperProps emitHelper
  compileEnv exprLoweringProps fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map words list rich_list arithmetic

Theorem abi_encode_member_entry_checked_ptr_path:
  !total.
  compile_abi_encode_complex_elems (Var dst) (Var src)
    ((ei,abi_sz,mem_sz,dyn)::infos) so ho cursor st = (out,final) /\
  fn_has_code st final fn /\
  not_fresh_at st src /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s total /\ so < total /\ so+mem_sz <= total /\
  w2n a+so < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!v prepared. emit_op ADD [Var src; Lit (n2w so)] st = (v,prepared) ==>
    isPREFIX (emitted_insts st prepared) (DROP s.vs_inst_idx bb.bb_instructions)) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?elem_src prepared child_len child_end p G1 tn1 u.
    emit_op ADD [Var src; Lit (n2w so)] st = (elem_src,prepared) /\
    compile_abi_encode_child (Var dst) elem_src ei dyn ho cursor prepared = (child_len,child_end) /\
    compile_abi_encode_complex_elems (Var dst) (Var src) infos
      (so+mem_sz) (ho+abi_sz) cursor child_end = (out,final) /\
    fn_has_code st prepared fn /\ fn_has_code prepared child_end fn /\
    fn_has_code child_end final fn /\
    cs_extends st prepared /\ cs_extends prepared child_end /\ cs_extends child_end final /\
    prepared.cs_blocks = st.cs_blocks /\ prepared.cs_next_id = st.cs_next_id+1 /\
    prepared.cs_next_var = st.cs_next_var+1 /\
    prepared.cs_next_id <= child_end.cs_next_id /\ child_end.cs_next_id <= final.cs_next_id /\
    prepared.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= final.cs_next_var /\
    elem_src = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    lookup_var p u = SOME (n2w (w2n a+so)) /\ ptr_covers G1 tn1 p u mem_sz /\
    op_taint tn1 (Var p) = {} /\ not_fresh_at prepared p /\
    fresh_vars_wrt limit_st u /\ u.vs_inst_idx = s.vs_inst_idx+1 /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_data_section = s.vs_data_section /\
    u.vs_labels = s.vs_labels /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
    (!q. not_fresh_at st q ==> lookup_var q u = lookup_var q s /\
      FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  gen_tac >> strip_tac >> drule_all abi_encoder_member_cons_context >> strip_tac >>
  `isPREFIX (emitted_insts st prepared) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (first_x_assum irule >> goal_assum $ drule_at Any) >>
  drule_all abi_encode_offset_checked_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "frame"
QED

Resume abi_encode_member_entry_checked_ptr_path[frame]:
  gvs[] >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st t` by
    (drule_all abi_encode_offset_fresh_vars >> simp[]) >>
  drule_all abi_encode_static_child_address_control >> strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
   t.vs_labels = s.vs_labels` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def, update_var_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := s.vs_inst_idx+1`] >>
  fs[fresh_vars_wrt_def, lookup_var_def]
QED
Finalise abi_encode_member_entry_checked_ptr_path
