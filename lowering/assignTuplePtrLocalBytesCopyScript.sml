(* Counted straight-line checks for the bytestring copy prefix. *)
Theory assignTuplePtrLocalBytesCopy
Ancestors
  wordLoadStorePtr typedCopyPtr fragGasSeqPtr ghostPcTransportPtr instIdxIndep
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomInstProofs venomInst venomState
  bodyPtrDefs ptrSafeRun ptrDiscipline finite_map arithmetic list

Theorem inst_seq_ptr_append_run:
  !xs s t G tn G1 tn1 ys G2 tn2.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\ 
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G1 tn1 ys
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2 ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct >- simp[inst_seq_ptr_def, run_inst_seq_def] >>
  rpt gen_tac >> Cases_on `step_inst_base h s` >>
  simp[inst_seq_ptr_def, run_inst_seq_def] >> strip_tac >>
  first_x_assum irule >> conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tn1`] >>
  fs[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES]
QED

Theorem mload_clean_seq_ptr:
  !D ctx fn PG G tn s id src out a.
    ~ctx_has_dalloca ctx /\ ptr_covers G tn src s 32 /\
    lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?G' tn' t.
      run_inst_seq [mk_inst id MLOAD [Var src] [out]] s = OK t /\
      inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id MLOAD [Var src] [out]] s G' tn' /\
      t = update_var out (mload (w2n a) s) s /\
      op_taint tn' (Var out) = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. p <> out ==>
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst id MLOAD [Var src] [out]` >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  `step_inst_base i s = OK t` by
    simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_read1_def, eval_operand_def] >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  conj_tac >- (simp[Abbr `i`] >> irule ptr_inst_ok_mload >> simp[]) >>
  simp[Abbr `i`, Abbr `t`] >>
  `op_taint (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn) (Var out) = {} /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn).t_trans = tn.t_trans` by
    (irule mload_ghost_clean >> simp[eval_operand_def]) >>
  simp[] >>
  simp[step_taint_def, step_prov_def, set_var_taint_def, set_prov_def,
       mk_inst_def, out_prov_def, out_taint_def, adopt_reset_def,
       imm_taint_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem copy_len_binop_seq_ptr:
  !D ctx fn PG G tn s id opc left right out f a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    ~ctx_has_dalloca ctx /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} ==>
    ?G' tn' t.
      run_inst_seq [mk_inst id opc [left;right] [out]] s = OK t /\
      inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst id opc [left;right] [out]] s G' tn' /\
      t = update_var out (f a b) s /\
      op_taint tn' (Var out) = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. p <> out ==>
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  qabbrev_tac `i = mk_inst id opc [left;right] [out]` >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  `step_inst_base i s = OK t` by
    (gvs[Abbr `i`, Abbr `t`] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  simp[Abbr `i`, Abbr `t`, copy_len_binop_ghost_frame] >>
  gvs[] >> simp[step_taint_def, set_var_taint_def, adopt_reset_def,
               imm_taint_def, mk_inst_def]
QED

Theorem inst_seq_ptr_append_normalized:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq xs s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = s.vs_inst_idx + LENGTH xs /\
  inst_seq_ptr D 0 ctx fn PG G tn xs s G1 tn1 /\
  run_inst_seq ys t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
  u.vs_inst_idx = t.vs_inst_idx + LENGTH ys /\
  inst_seq_ptr D 0 ctx fn PG G1 tn1 ys t G2 tn2 ==>
  run_inst_seq (xs ++ ys) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  u.vs_inst_idx = s.vs_inst_idx + LENGTH (xs ++ ys) /\
  inst_seq_ptr D 0 ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  strip_tac >> conj_tac
  >- (qpat_assum `run_inst_seq xs s = _`
        (mp_then Any (qspec_then `ys` SUBST1_TAC) run_inst_seq_append) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  conj_tac >- simp[LENGTH_APPEND] >>
  irule inst_seq_ptr_append_run >> conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := s.vs_inst_idx`, `tn1`] >>
  `t with vs_inst_idx := LENGTH xs + s.vs_inst_idx = t` by
    (simp[venom_state_component_equality] >> decide_tac) >> simp[]
QED

Theorem emit_mload_clean_normalized_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s 32 /\
  lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?G' tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    lookup_var out t = SOME (mload (w2n a) s) /\
    op_taint tn' (Var out) = {} /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `!p. not_fresh_at sa p ==> p <> out` by gvs[not_fresh_at_def] >>
  drule_all mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`]
    (qspec_then `sa.cs_next_id` (qspec_then `out` strip_assume_tac))) >>
  qexistsl_tac [`G'`, `tn'`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gs[] >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  fs[]
QED

Theorem emit_copy_len_binop_normalized_ptr:
  emit_op opc [left;right] sa = (Var out,sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?G' tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    lookup_var out t = SOME (f a b) /\ op_taint tn' (Var out) = {} /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!p. not_fresh_at sa p ==> p <> out` by gvs[not_fresh_at_def] >>
  qpat_assum `eval_operand left s = SOME a`
    (mp_then (Pat `eval_operand left s = SOME a`) mp_tac copy_len_binop_seq_ptr) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `G`]
    (qspec_then `sa.cs_next_id` (qspec_then `out` strip_assume_tac))) >>
  qexistsl_tac [`G'`, `tn'`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gs[] >> (simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    conj_tac >- simp[venom_state_component_equality] >>
    rpt strip_tac >>
    `p <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >> fs[])
QED
