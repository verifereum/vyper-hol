Theory bodyPtrIfExpBytesCounted
Ancestors
  bodyPtrIfExpCopyHeader bodyPtrIfExpCopyInputs typedCopyPtr fragGasSeqPtr
  context compileEnv emitHelper exprLoweringProps rich_list venomInst
  venomState venomExecSemantics ptrSafeRun ptrDiscipline fragExec
  finite_map instIdxIndep ghostPcTransportPtr

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
  !opc (f:256 word -> 256 word -> 256 word) D ctx fn PG G tn s sa sb left right out a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    emit_op opc [left;right] sa = (Var out,sb) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tnf sf.
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      lookup_var out sf = SOME (f a b) /\
      (sf with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s) /\
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
  `step_inst_base (mk_inst sa.cs_next_id opc [left;right] [out]) s =
     OK (update_var out (f a b) s)` by
    (irule copy_len_binop_step >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`, `update_var out (f a b) s`] >>
  gvs[run_inst_seq_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
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

Theorem emit_mload_clean_seq_ptr:
  !D ctx fn PG G tn s sa sb src out a.
    emit_op MLOAD [Var src] sa = (Var out,sb) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      lookup_var out sf = SOME (mload (w2n a) s) /\
      (sf with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s) /\
      op_taint tnf (Var out) = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
         emitted_insts_def, DROP_APPEND1] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `?Gf tnf.
     inst_seq_ptr D 0 ctx fn PG G tn
       [mk_inst sa.cs_next_id MLOAD [Var src] [out]] s Gf tnf /\
     op_taint tnf (Var out) = {} /\
     tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
     tnf.t_trans = tn.t_trans /\
     (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
                       op_taint tnf (Var p) = op_taint tn (Var p))` by
    (irule mload_clean_seq_ptr >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `update_var out (mload (w2n a) s) s`] >>
  simp[] >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  gvs[run_inst_seq_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem compile_bytestring_copy_len_stages:
  !src sa sb count.
    compile_bytestring_copy_len src sa = (count,sb) ==>
    ?s1 s2 s3 v1 v2 v3 v4.
      emit_op MLOAD [src] sa = (Var v1,s1) /\
      emit_op ADD [Var v1; Lit 31w] s1 = (Var v2,s2) /\
      emit_op AND [Var v2; Lit (i2w (-32))] s2 = (Var v3,s3) /\
      emit_op ADD [Var v3; Lit 32w] s3 = (Var v4,sb) /\
      count = Var v4
Proof
  rpt gen_tac >>
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >> metis_tac[]
QED


(* This existential summary compresses intermediate runtime/ghost contexts;
   it changes no execution semantics and is opened only at interface proofs. *)
Definition clean_emitted_prefix_def:
  clean_emitted_prefix D ctx fn PG sa sb out w s G tn <=>
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    ?Gf tnf sf.
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      eval_operand out sf = SOME w /\
      (sf with vs_vars := s.vs_vars) = s /\
      op_taint tnf out = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
End

Theorem clean_emitted_prefix_mload:
  !D ctx fn PG G tn s sa sb src out a.
    emit_op MLOAD [Var src] sa = (Var out,sb) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    clean_emitted_prefix D ctx fn PG sa sb (Var out)
      (mload (w2n a) s) s G tn
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, emitted_insts_def,
         DROP_APPEND1] >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  simp[clean_emitted_prefix_def] >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[eval_operand_def] >> metis_tac[]
QED


Theorem clean_emitted_prefix_binop:
  !opc (f:256 word -> 256 word -> 256 word) D ctx fn PG sa sm sb operand out w k s G tn.
    clean_emitted_prefix D ctx fn PG sa sm operand w s G tn /\
    emit_op opc [operand; Lit k] sm = (Var out,sb) /\
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    ~ctx_has_dalloca ctx /\
    emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
    (!p. not_fresh_at sa p ==> not_fresh_at sm p) ==>
    clean_emitted_prefix D ctx fn PG sa sb (Var out) (f w k) s G tn
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `clean_emitted_prefix _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[clean_emitted_prefix_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `t` strip_assume_tac)))) >>
  `emitted_insts sm sb = [mk_inst sm.cs_next_id opc [operand;Lit k] [out]] /\
   (!p. not_fresh_at sm p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
         emitted_insts_def, DROP_APPEND1] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand operand (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)) = SOME w /\
   eval_operand (Lit k) (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)) = SOME k /\
   op_taint tn1 (Lit k) = {}` by simp[op_taint_def, eval_operand_def] >>
  drule_all emit_copy_len_binop_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G1`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `u` strip_assume_tac)))) >>
  `step_inst_base (mk_inst sm.cs_next_id opc [operand;Lit k] [out]) t =
     OK (update_var out (f w k) t)` by
    (irule copy_len_binop_step >> simp[eval_operand_def]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn
     (emitted_insts sa sm ++ emitted_insts sm sb) s G2 tn2` by
    (irule inst_seq_ptr_append_run >> metis_tac[]) >>
  conj_tac >- (simp[mk_inst_def] >> metis_tac[is_terminator_def]) >>
  qexistsl_tac [`G2`, `tn2`, `update_var out (f w k) t`] >>
  simp[] >>
  conj_tac >-
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[run_inst_seq_def]) >>
  gvs[run_inst_seq_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  gvs[lookup_var_def] >> metis_tac[]
QED

Theorem copy_len_stages_structure:
  !sa s1 s2 s3 sb src v1 v2 v3 v4.
    emit_op MLOAD [src] sa = (Var v1,s1) /\
    emit_op ADD [Var v1;Lit 31w] s1 = (Var v2,s2) /\
    emit_op AND [Var v2;Lit (i2w (-32))] s2 = (Var v3,s3) /\
    emit_op ADD [Var v3;Lit 32w] s3 = (Var v4,sb) ==>
    emitted_insts sa s2 = emitted_insts sa s1 ++ emitted_insts s1 s2 /\
    emitted_insts sa s3 = emitted_insts sa s2 ++ emitted_insts s2 s3 /\
    emitted_insts sa sb = emitted_insts sa s3 ++ emitted_insts s3 sb /\
    (!p. not_fresh_at sa p ==> not_fresh_at s1 p /\
       not_fresh_at s2 p /\ not_fresh_at s3 p)
Proof
  rpt strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, not_fresh_at_def,
      emitted_insts_def, DROP_APPEND1] >>
  simp[DROP_APPEND] >> rpt strip_tac >> decide_tac
QED

Theorem compile_bytestring_copy_len_clean_prefix:
  !D ctx fn PG G tn s sa sb src count a.
    compile_bytestring_copy_len (Var src) sa = (count,sb) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    clean_emitted_prefix D ctx fn PG sa sb count
      ((mload (w2n a) s + 31w && i2w (-32)) + 32w) s G tn
Proof
  rpt strip_tac >>
  drule compile_bytestring_copy_len_stages >> strip_tac >> gvs[] >>
  drule_all copy_len_stages_structure >> strip_tac >>
  `clean_emitted_prefix D ctx fn PG sa s1 (Var v1)
     (mload (w2n a) s) s G tn` by
    (irule clean_emitted_prefix_mload >> metis_tac[]) >>
  `clean_emitted_prefix D ctx fn PG sa s2 (Var v2)
     (mload (w2n a) s + 31w) s G tn` by
    (irule (Q.SPECL [`ADD`, `word_add`] clean_emitted_prefix_binop) >> metis_tac[]) >>
  `clean_emitted_prefix D ctx fn PG sa s3 (Var v3)
     (mload (w2n a) s + 31w && i2w (-32)) s G tn` by
    (irule (Q.SPECL [`AND`, `word_and`] clean_emitted_prefix_binop) >> metis_tac[]) >>
  irule (Q.SPECL [`ADD`, `word_add`] clean_emitted_prefix_binop) >> metis_tac[]
QED

Theorem compile_bytestring_copy_len_seq_ptr:
  !D ctx fn PG G tn s sa sb src count a.
    compile_bytestring_copy_len (Var src) sa = (count,sb) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      eval_operand count sf =
        SOME ((mload (w2n a) s + 31w && i2w (-32)) + 32w) /\
      (sf with vs_vars := s.vs_vars) = s /\
      op_taint tnf count = {} /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >> drule_all compile_bytestring_copy_len_clean_prefix >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] mp_tac) >>
  simp[clean_emitted_prefix_def]
QED

Theorem mcopy_operand_seq_ptr:
  !D ctx fn PG G tn s id dst src count_op a b n.
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
    ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MCOPY [Var dst;Var src;count_op] []] s G
      (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
     OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac >- (irule fragExecPtrTheory.ptr_inst_ok_mcopy_operand >> simp[]) >>
  simp[mcopy_operand_ghost_frame, eval_operand_def]
QED
