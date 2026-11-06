(* The tuple loop retains its base source pointer and generates one member
   address per iteration.  This boundary keeps its original capacity fixed. *)
Theory logScalarMembersStepPtr
Ancestors
  logScalarChildPtr logAbiPrefixPtr logTopicScalarPtr abiBuiltinPrefix
  emitHelperProps exprLoweringProps emitHelper compileEnv bodyPtrDefs
  ptrDiscipline venomState venomInst words arithmetic list

Theorem log_member_source_add_seq_ptr:
  emit_op ADD [Var src;Lit (n2w so)] st = (Var elem,next) /\
  lookup_var src s = SOME (n2w sb) /\ ptr_covers G tn src s srcCap /\
  so+mz <= srcCap /\ sb+srcCap < dimword(:256) /\
  next.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq (emitted_insts st next) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st next) s H tm /\
    abi_builtin_prefix st next limit_st s t /\
    lookup_var elem t = SOME (n2w (sb+so)) /\ ptr_covers H tm elem t mz /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ptr_covers G tn src s (so+mz) /\
   eval_operand (Var src) s = SOME (n2w sb) /\
   eval_operand (Lit (n2w so)) s = SOME (n2w so) /\
   op_taint tn (Lit (n2w so)) = {} /\
   w2n ((n2w sb):256 word)+so < dimword(:256)` by
    (gvs[ptr_covers_def, eval_operand_def, op_taint_def, w2n_n2w] >> decide_tac) >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  drule_all abi_builtin_emit_add >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u = t` by
    (qpat_x_assum `abi_builtin_prefix _ _ _ _ u` mp_tac >>
     simp_tac bool_ss [abi_builtin_prefix_def] >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK t` (fn th => rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  qpat_x_assum `lookup_var elem t = _` (fn th => assume_tac (PURE_REWRITE_RULE [word_add_n2w] th)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
