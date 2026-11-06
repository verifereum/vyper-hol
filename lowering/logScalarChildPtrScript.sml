(* Static scalar child execution; MCOPY and address arithmetic stay abstract. *)
Theory logScalarChildPtr
Ancestors
  logAbiStaticPtr logAbiPrefixPtr logInstSeqPtr logTopicScalarPtr
  abiEncoder abiEncoderChildCode emitHelper emitHelperProps exprLoweringProps compileEnv
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst instIdxIndep
  finite_map words arithmetic list rich_list
  logMembersInvariantPtr logAbiInputPtr abiEncoderMembersInput

Theorem compile_abi_copy_child_seq_ptr:
  compile_abi_encode_child (Var dst) (Var src) (AbiCopy 32) F ho dp sa = (out,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var src s = SOME (n2w a) /\
  ptr_covers G tn dst s cap /\ ptr_covers G tn src s 32 /\
  ho+32 <= cap /\ d+cap < dimword(:256) /\ a+32 < dimword(:256) /\
  (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    eval_operand out t = SOME 32w /\ op_taint tm out = {} /\ op_prov H out = NONE /\
    (!i. d+ho <= i /\ i < d+ho+32 ==> i NOTIN tm.t_mem) /\
    (!i. ~(d+ho <= i /\ i < d+ho+32) ==>
         (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    mem_agree_outside {i | d+ho <= i /\ i < d+ho+32} t.vs_memory s.vs_memory /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Var dst;Lit (n2w ho)] sa = (hd,sc)` >>
  `?hv. hd = Var hv` by (drule emitted_insts_emit_op >> metis_tac[]) >> gvs[] >>
  `ptr_covers G tn dst s (ho+32) /\
   eval_operand (Lit (n2w ho)) s = SOME (n2w ho) /\
   op_taint tn (Lit (n2w ho)) = {} /\
   w2n ((n2w d):256 word)+ho < dimword(:256)` by
    (gvs[ptr_covers_def, eval_operand_def, op_taint_def, w2n_n2w] >> decide_tac) >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  suspend "copy"
QED
Resume compile_abi_copy_child_seq_ptr[copy]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc)` >>
  `lookup_var src u1 = SOME (n2w a) /\ lookup_var hv u1 = SOME (n2w (d+ho)) /\
   ptr_covers H tk src u1 32 /\ ptr_covers H tk hv u1 32 /\
   (!i. a <= i /\ i < a+32 ==> i NOTIN tk.t_mem) /\
   d+ho+32 < dimword(:256)` by
    (gvs[Abbr `u1`, ptr_covers_def, lookup_var_def, word_add_n2w] >>
     metis_tac[LESS_EQ_LESS_TRANS, ADD_ASSOC, LESS_EQ_MONO_ADD_EQ]) >>
  drule_all compile_abi_copy_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `v` strip_assume_tac))) >>
  suspend "compose"
QED
Resume compile_abi_copy_child_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb) /\
   tk.t_imm = tn.t_imm` by suspend "code" >>
  qunabbrev_tac `u1` >> drule_all successful_seq_ptr_append >> strip_tac >>
  qexistsl_tac [`H`,`tm`,`v with vs_inst_idx := u.vs_inst_idx`] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  suspend "post"
QED
Resume compile_abi_copy_child_seq_ptr[code]:
  markerLib.RESUME_TAC >>
  `tk.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  simp[] >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`emit_op ADD _ sa = _`, `compile_abi_encode_to_buf _ _ _ sc = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `out = Lit 32w /\ emit_void MCOPY [Var hv;Var src;Lit 32w] sc = ((),sb)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, DROP_APPEND, mk_inst_def, is_terminator_def]
QED
Resume compile_abi_copy_child_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`eval_operand out v = _`, `op_taint tm out = _`, `op_prov H out = _`,
     `!i. d+ho <= i /\ _ ==> _`,
     `!i. ~(_ /\ _) ==> _`, `mem_agree_outside _ _ _`,
     `tm.t_stor = _`, `tm.t_trans = _`, `tm.t_imm = _`,
     `tk.t_stor = _`, `tk.t_trans = _`, `tk.t_imm = _`, `tk.t_mem = _`,
     `u.vs_memory = _`, `!p. not_fresh_at sa p ==> _`,
     `!p. lookup_var p v = _ /\ _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  simp_tac (srw_ss()) [eval_op_inst_idx, ADD_ASSOC, lookup_var_def] >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [lookup_var_def]) >>
  metis_tac[]
QED
Finalise compile_abi_copy_child_seq_ptr

Theorem robust_abi_encoder_members_input_cons:
  (!q. mem_agree_outside m mem q ==>
    abi_encoder_input (AbiComplex ((ei,asz,mz,dyn)::infos))
      (Tuple (ty::tys)) (ListV (av::avs)) a cap q) ==>
  (!q. mem_agree_outside m mem q ==> abi_encoder_input ei ty av a mz q) /\
  (!q. mem_agree_outside m mem q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (a+mz) (abi_encoder_member_span infos) q)
Proof
  strip_tac >> conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule abi_encoder_members_input_cons >> simp[]
QED

(* A cursor cell already clean before and after a child does not enlarge
   that child's taint-change footprint, even though its memory is written. *)
Theorem taint_frame_clean_exception:
  (!i. i IN clean ==> i NOTIN m) /\
  (!i. i IN clean ==> i NOTIN m') /\
  (!i. i NOTIN writes /\ i NOTIN clean ==> (i IN m' <=> i IN m)) ==>
  !i. i NOTIN writes ==> (i IN m' <=> i IN m)
Proof
  metis_tac[]
QED
