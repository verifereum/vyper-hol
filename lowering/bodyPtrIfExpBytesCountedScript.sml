Theory bodyPtrIfExpBytesCounted
Ancestors
  bodyPtrIfExpCopyHeader bodyPtrIfExpCopyInputs typedCopyPtr fragGasSeqPtr
  context compileEnv emitHelper exprLoweringProps rich_list venomInst
  venomState venomExecSemantics ptrSafeRun ptrDiscipline fragExec
  finite_map instIdxIndep

Theorem compile_store_bytestring_stages:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    ?s1 s2 s3 s4 r1 r2 r3 r4.
      emit_op MLOAD [src] sa = (r1,s1) /\
      emit_op ADD [r1; Lit 31w] s1 = (r2,s2) /\
      emit_op AND [r2; Lit (i2w (-32))] s2 = (r3,s3) /\
      emit_op ADD [r3; Lit 32w] s3 = (r4,s4) /\
      emit_void MCOPY [dst;src;r4] s4 = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_store_bytestring_code:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
      (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, DROP_APPEND1] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem copy_len_binop_step:
  !opc f left right s a b id tmp.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
    step_inst_base (mk_inst id opc [left;right] [tmp]) s =
      OK (update_var tmp (f a b) s)
Proof
  rpt strip_tac >> gvs[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem copy_len_binop_seq_ptr:
  !D ctx fn PG G tn s id opc left right tmp (f:256 word -> 256 word -> 256 word) a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tnf.
      inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id opc [left;right] [tmp]] s Gf tnf /\
      op_taint tnf (Var tmp) = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. p <> tmp ==>
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id opc [left;right] [tmp]) s =
     OK (update_var tmp (f a b) s)` by
    (irule copy_len_binop_step >> simp[]) >>
  simp[inst_seq_ptr_def] >>
  (conj_tac >- (irule ptr_inst_ok_copy_len_binop >> metis_tac[]) >>
   simp[copy_len_binop_ghost_frame])
QED

Theorem mload_clean_seq_ptr:
  !D ctx fn PG G tn s id src tmp a.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf.
      inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id MLOAD [Var src] [tmp]] s Gf tnf /\
      op_taint tnf (Var tmp) = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. p <> tmp ==>
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
     OK (update_var tmp (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  simp[mload_ghost_clean] >>
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_copy_len_binop_seq_ptr:
  !D ctx fn PG G tn s sa sb opc left right out (f:256 word -> 256 word -> 256 word) a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    emit_op opc [left;right] sa = (Var out,sb) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tnf.
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
      op_taint tnf (Var out) = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
         emitted_insts_def, DROP_APPEND1] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `?Gf tnf.
     inst_seq_ptr D 0 ctx fn PG G tn
       [mk_inst sa.cs_next_id opc [left;right] [out]] s Gf tnf /\
     op_taint tnf (Var out) = {} /\
     tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
     tnf.t_trans = tn.t_trans /\
     (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
                       op_taint tnf (Var p) = op_taint tn (Var p))` by
    (irule copy_len_binop_seq_ptr >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[] >> metis_tac[]
QED

Theorem inst_seq_ptr_append_run:
  !code s t.
    EVERY (\i. ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==>
    !G tn G1 tn1 G2 tn2 tail.
      inst_seq_ptr D lo ctx fn PG G tn code s G1 tn1 /\
      inst_seq_ptr D lo ctx fn PG G1 tn1 tail
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH code) G2 tn2 ==>
      inst_seq_ptr D lo ctx fn PG G tn (code ++ tail) s G2 tn2
Proof
  Induct >- simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[inst_seq_ptr_def] >>
  first_x_assum irule >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  qexistsl_tac [`G1`, `tn1`] >> gvs[arithmeticTheory.ADD_CLAUSES]
QED
