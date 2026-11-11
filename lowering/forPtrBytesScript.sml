(* Counted bytestring copies: only the length word must be clean. *)
Theory forPtrBytes
Ancestors wordLoadStorePtr instIdxIndep forPtrSeqCompose forPtrBulk typedCopyPtr representationCleanPtr valueCopyBytes
  exprSimBufferStore valueEncoding valueEncodingProps bodyPtrDefs
  loweringPosts venomState venomExecSemantics venomInst ptrSafeRun
  ptrDiscipline fragGasSeqPtr ghostPcTransportPtr finite_map exprLoweringProps
  context compileEnv loweringStateRelDefs emitHelper loweringSlice list rich_list words integer_word arithmetic

Theorem for_bytes_copy_header:
  ((?cap bs. tv = BaseTV (BytesT (Dynamic cap)) /\ v = BytesV bs /\
              len = LENGTH bs) \/
   (?cap str. tv = BaseTV (StringT cap) /\ v = StringV str /\
               len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v p m) ==>
  mload p s = n2w len /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `val_in_memory tv v p s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[]
  >- (conj_tac >- metis_tac[buffer_bytes_header] >>
      drule robust_val_in_memory_bytes_clean >> simp[]) >>
  conj_tac >- metis_tac[buffer_string_header] >>
  drule robust_val_in_memory_string_clean >> simp[]
QED

Theorem for_copy_len_binop_step:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id opc [left; right] [tmp]) s =
    OK (update_var tmp (f a b) s)
Proof
  strip_tac >> gvs[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem for_copy_len_binop_checked:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ u = update_var tmp (f a b) s /\
  g = step_prov PG G (mk_inst id opc [left; right] [tmp]) u /\
  t = step_taint (mk_inst id opc [left; right] [tmp]) s u tn ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id opc [left; right] [tmp]] s g t /\
  run_inst_seq [mk_inst id opc [left; right] [tmp]] s = OK u /\
  lookup_var tmp u = SOME (f a b) /\ op_taint t (Var tmp) = {} /\
  u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
  t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
  (!p. p <> tmp ==> lookup_var p u = lookup_var p s /\
    FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base (mk_inst id opc [left; right] [tmp]) s = OK u` by
    (simp[] >> irule for_copy_len_binop_step >> simp[]) >>
  conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_copy_len_binop >>
      simp[] >> metis_tac[]) >>
  conj_tac >- simp[run_inst_seq_def] >>
  gvs[] >> (conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (irule (cj 1 copy_len_binop_ghost_frame) >> simp[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- (irule (cj 2 copy_len_binop_ghost_frame) >> simp[]) >>
  conj_tac >- (irule (cj 3 copy_len_binop_ghost_frame) >> simp[]) >>
  conj_tac >- (irule (cj 4 copy_len_binop_ghost_frame) >> simp[]) >>
  gen_tac >> disch_tac >> conj_tac
  >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule (cj 5 copy_len_binop_ghost_frame) >> simp[])
QED

Theorem for_bytes_copy_code:
  compile_store_bytestring src dst sa = ((),sb) ==>
  ?t0 t1 t2 t3.
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [src] [t0];
       mk_inst (sa.cs_next_id+1) ADD [Var t0; Lit 31w] [t1];
       mk_inst (sa.cs_next_id+2) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (sa.cs_next_id+3) ADD [Var t2; Lit 32w] [t3];
       mk_inst (sa.cs_next_id+4) MCOPY [dst; src; Var t3] []] /\
    ALL_DISTINCT [t0;t1;t2;t3] /\
    (!p. not_fresh_at sa p ==> p <> t0 /\ p <> t1 /\ p <> t2 /\ p <> t3)
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[] >> qexistsl [`"%" ++ toString sa.cs_next_var`,
    `"%" ++ toString (sa.cs_next_var+1)`,
    `"%" ++ toString (sa.cs_next_var+2)`,
    `"%" ++ toString (sa.cs_next_var+3)`] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, DECIDE ``!n:num. n <= n+1 /\ n <= n+2 /\ n <= n+3``]
QED

Theorem for_copy_len_binop_covers:
  (opc = ADD \/ opc = AND) /\ tmp <> p /\ ptr_covers G tn p s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id opc [left;right] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [left;right] [tmp]) s (update_var tmp w s) tn)
    p (update_var tmp w s) n
Proof
  strip_tac >>
  `FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [tmp])
      (update_var tmp w s)) p = FLOOKUP G p /\
   op_taint (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp w s) tn) (Var p) = op_taint tn (Var p)` by
    (irule (cj 5 copy_len_binop_ghost_frame) >> simp[]) >>
  gvs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem for_bytes_copy_steps:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3 /\
  src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
  u0 = update_var t0 (mload (w2n a) s) s /\
  u1 = update_var t1 (mload (w2n a) s + 31w) u0 /\
  u2 = update_var t2 ((mload (w2n a) s + 31w) && i2w (-32)) u1 /\
  u3 = update_var t3 (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) u2 ==>
  step_inst_base (mk_inst id MLOAD [Var src] [t0]) s = OK u0 /\
  step_inst_base (mk_inst (id+1) ADD [Var t0; Lit 31w] [t1]) u0 = OK u1 /\
  step_inst_base (mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2]) u1 = OK u2 /\
  step_inst_base (mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]) u2 = OK u3 /\
  step_inst_base (mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []) u3 =
    OK (mcopy (w2n b) (w2n a)
      (w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w)) u3)
Proof
  strip_tac >>
  `eval_operand (Var t0) u0 = SOME (mload (w2n a) s) /\
   eval_operand (Var t1) u1 = SOME (mload (w2n a) s + 31w) /\
   eval_operand (Var t2) u2 = SOME ((mload (w2n a) s + 31w) && i2w (-32)) /\
   eval_operand (Var t3) u3 = SOME (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) /\
   eval_operand (Var src) u3 = SOME a /\ eval_operand (Var dst) u3 = SOME b` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  rpt conj_tac >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, exec_pure2_def, eval_operand_def] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem for_bytes_copy_run:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3 /\
  src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
  u0 = update_var t0 (mload (w2n a) s) s /\
  u1 = update_var t1 (mload (w2n a) s + 31w) u0 /\
  u2 = update_var t2 ((mload (w2n a) s + 31w) && i2w (-32)) u1 /\
  u3 = update_var t3 (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) u2 ==>
  run_inst_seq
    [mk_inst id MLOAD [Var src] [t0];
     mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
     mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
     mk_inst (id+3) ADD [Var t2; Lit 32w] [t3];
     mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []] s =
    OK (mcopy (w2n b) (w2n a)
      (w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w)) u3)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [t0]) s = OK u0 /\
   step_inst_base (mk_inst (id+1) ADD [Var t0; Lit 31w] [t1]) u0 = OK u1 /\
   step_inst_base (mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2]) u1 = OK u2 /\
   step_inst_base (mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]) u2 = OK u3 /\
   step_inst_base (mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []) u3 =
     OK (mcopy (w2n b) (w2n a)
       (w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w)) u3)` by
    (irule for_bytes_copy_steps >> simp[]) >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`u0 = _`, `u1 = _`, `u2 = _`, `u3 = _`] >>
  simp[run_inst_seq_def]
QED

(* Consumer probe for the cursor-uniform composition boundary. *)
Theorem for_copy_len_binop_cons:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ u = update_var tmp (f a b) s /\
  g = step_prov PG G (mk_inst id opc [left;right] [tmp]) u /\
  t = step_taint (mk_inst id opc [left;right] [tmp]) s u tn /\
  (!k. inst_seq_ptr D 0 ctx fn PG g t code
    (u with vs_inst_idx := k) gf tf) ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    (mk_inst id opc [left;right] [tmp] :: code)
    (s with vs_inst_idx := k) gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule for_inst_seq_ptr_cons_nonterminator >>
  conj_tac >- (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl [`g`, `t`, `u`] >>
  reverse conj_tac >- (simp[] >> irule for_copy_len_binop_step >> simp[]) >>
  simp[] >> gen_tac >>
  irule (cj 1 for_copy_len_binop_checked) >> simp[] >>
  qexists `f` >>
  `update_var tmp (f a b) (s with vs_inst_idx := k) =
    (update_var tmp (f a b) s) with vs_inst_idx := k` by simp[update_var_def] >>
  simp[]
QED

Theorem for_copy_len_binop_endpoint:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ?u g t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc [left;right] [tmp]] (s with vs_inst_idx := k) g t) /\
    step_inst_base (mk_inst id opc [left;right] [tmp]) s = OK u /\
    run_inst_seq [mk_inst id opc [left;right] [tmp]] s = OK u /\
    lookup_var tmp u = SOME (f a b) /\ op_taint t (Var tmp) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> lookup_var p u = lookup_var p s /\
      FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `u = update_var tmp (f a b) s` >>
  qabbrev_tac `g = step_prov PG G (mk_inst id opc [left;right] [tmp]) u` >>
  qabbrev_tac `t = step_taint (mk_inst id opc [left;right] [tmp]) s u tn` >>
  qexistsl [`u`, `g`, `t`] >> conj_tac
  >- (irule for_copy_len_binop_cons >> simp[inst_seq_ptr_def] >>
      qexists `f` >> simp[Abbr `u`, Abbr `g`, Abbr `t`]) >>
  conj_tac >- (simp[Abbr `u`] >> irule for_copy_len_binop_step >> simp[]) >>
  qsuff_tac `inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc [left;right] [tmp]] s g t /\
    run_inst_seq [mk_inst id opc [left;right] [tmp]] s = OK u /\
    lookup_var tmp u = SOME (f a b) /\ op_taint t (Var tmp) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> lookup_var p u = lookup_var p s /\
      FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))`
  >- simp[] >>
  irule for_copy_len_binop_checked >> simp[Abbr `u`, Abbr `g`, Abbr `t`]
QED

Theorem for_copy_len_last_two:
  lookup_var p s = SOME w /\ op_taint tn (Var p) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id AND [Var p; Lit (i2w (-32))] [q];
       mk_inst (id+1) ADD [Var q; Lit 32w] [r]]
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq [mk_inst id AND [Var p; Lit (i2w (-32))] [q];
       mk_inst (id+1) ADD [Var q; Lit 32w] [r]] s = OK sf /\
    lookup_var r sf = SOME ((w && i2w (-32)) + 32w) /\
    op_taint tf (Var r) = {} /\ sf.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x <> q /\ x <> r ==> lookup_var x sf = lookup_var x s /\
      FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?u g t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id AND [Var p; Lit (i2w (-32))] [q]] (s with vs_inst_idx := k) g t) /\
    step_inst_base (mk_inst id AND [Var p; Lit (i2w (-32))] [q]) s = OK u /\
    run_inst_seq [mk_inst id AND [Var p; Lit (i2w (-32))] [q]] s = OK u /\
    lookup_var q u = SOME (w && i2w (-32)) /\ op_taint t (Var q) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!x. x <> q ==> lookup_var x u = lookup_var x s /\
      FLOOKUP g x = FLOOKUP G x /\ op_taint t (Var x) = op_taint tn (Var x))` by
    (irule for_copy_len_binop_endpoint >> simp[eval_operand_def, op_taint_def]) >>
  `?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG g t
      [mk_inst (id+1) ADD [Var q; Lit 32w] [r]] (u with vs_inst_idx := k) gf tf) /\
    step_inst_base (mk_inst (id+1) ADD [Var q; Lit 32w] [r]) u = OK sf /\
    run_inst_seq [mk_inst (id+1) ADD [Var q; Lit 32w] [r]] u = OK sf /\
    lookup_var r sf = SOME ((w && i2w (-32)) + 32w) /\ op_taint tf (Var r) = {} /\
    sf.vs_memory = u.vs_memory /\ tf.t_mem = t.t_mem /\
    tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\
    (!x. x <> r ==> lookup_var x sf = lookup_var x u /\
      FLOOKUP gf x = FLOOKUP g x /\ op_taint tf (Var x) = op_taint t (Var x))` by
    (irule for_copy_len_binop_endpoint >> simp[eval_operand_def, op_taint_def]) >>
  qexistsl [`sf`, `gf`, `tf`] >> conj_tac
  >- (irule for_inst_seq_ptr_cons_nonterminator >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`g`, `t`, `u`] >> simp[]) >>
  simp[run_inst_seq_def] >> metis_tac[]
QED

Theorem for_copy_len_suffix:
  lookup_var t0 s = SOME w /\ op_taint tn (Var t0) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+1) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+2) ADD [Var t2; Lit 32w] [t3]]
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq [mk_inst id ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+1) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+2) ADD [Var t2; Lit 32w] [t3]] s = OK sf /\
    lookup_var t3 sf = SOME (((w + 31w) && i2w (-32)) + 32w) /\
    op_taint tf (Var t3) = {} /\ sf.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. p <> t1 /\ p <> t2 /\ p <> t3 ==> lookup_var p sf = lookup_var p s /\
      FLOOKUP gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `?u g t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var t0; Lit 31w] [t1]] (s with vs_inst_idx := k) g t) /\
    step_inst_base (mk_inst id ADD [Var t0; Lit 31w] [t1]) s = OK u /\
    run_inst_seq [mk_inst id ADD [Var t0; Lit 31w] [t1]] s = OK u /\
    lookup_var t1 u = SOME (w+31w) /\ op_taint t (Var t1) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!p. p <> t1 ==> lookup_var p u = lookup_var p s /\
      FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))` by
    (irule for_copy_len_binop_endpoint >> simp[eval_operand_def, op_taint_def]) >>
  `?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG g t
      [mk_inst (id+1) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+2) ADD [Var t2; Lit 32w] [t3]] (u with vs_inst_idx := k) gf tf) /\
    run_inst_seq [mk_inst (id+1) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+2) ADD [Var t2; Lit 32w] [t3]] u = OK sf /\
    lookup_var t3 sf = SOME (((w+31w) && i2w (-32)) + 32w) /\
    op_taint tf (Var t3) = {} /\ sf.vs_memory = u.vs_memory /\
    tf.t_mem = t.t_mem /\ tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\
    (!p. p <> t2 /\ p <> t3 ==> lookup_var p sf = lookup_var p u /\
      FLOOKUP gf p = FLOOKUP g p /\ op_taint tf (Var p) = op_taint t (Var p))` by
    (irule (SRULE [GSYM ADD_ASSOC]
      (Q.INST [`id` |-> `id+1`] (SPEC_ALL for_copy_len_last_two))) >> simp[]) >>
  qexistsl [`sf`, `gf`, `tf`] >> conj_tac
  >- (irule for_inst_seq_ptr_cons_nonterminator >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`g`, `t`, `u`] >> simp[]) >>
  simp[Once run_inst_seq_def] >> metis_tac[]
QED

Theorem for_copy_header_variable_frame:
  p <> tmp ==>
  lookup_var p (update_var tmp w s) = lookup_var p s /\
  FLOOKUP (step_prov PG G (mk_inst id MLOAD [src] [tmp])
    (update_var tmp w s)) p = FLOOKUP G p /\
  op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
    (update_var tmp w s) tn) (Var p) = op_taint tn (Var p)
Proof
  strip_tac >>
  gvs[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem for_copy_header_endpoint:
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?u g t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [tmp]] (s with vs_inst_idx := k) g t) /\
    step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u /\
    lookup_var tmp u = SOME (mload (w2n a) s) /\ op_taint t (Var tmp) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> lookup_var p u = lookup_var p s /\
      FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var tmp (mload (w2n a) s) s` >>
  qabbrev_tac `g = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u` >>
  qabbrev_tac `t = step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn` >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_read1_def, eval_operand_def, Abbr `u`]) >>
  `~is_terminator (mk_inst id MLOAD [Var src] [tmp]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  qexistsl [`u`, `g`, `t`] >> conj_tac
  >- (gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
                      exec_result_map_def, Abbr `g`, Abbr `t`] >>
      irule ptr_inst_ok_mload >> simp[]) >>
  simp[] >> conj_tac
  >- simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint t (Var tmp) = {} /\ t.t_mem = tn.t_mem /\
   t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans` by
    (simp[Abbr `t`, Abbr `u`] >> irule mload_ghost_clean >> simp[eval_operand_def]) >>
  simp[] >> conj_tac >- simp[Abbr `u`, update_var_def] >>
  gen_tac >> disch_tac >>
  simp_tac pure_ss [Abbr `g`, Abbr `t`, Abbr `u`] >>
  irule for_copy_header_variable_frame >> simp[]
QED

Theorem for_bytes_length_prefix:
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [t0];
       mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]]
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq [mk_inst id MLOAD [Var src] [t0];
       mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]] s = OK sf /\
    lookup_var t3 sf = SOME (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) /\
    op_taint tf (Var t3) = {} /\ sf.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. p <> t0 /\ p <> t1 /\ p <> t2 /\ p <> t3 ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `?u g t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [t0]] (s with vs_inst_idx := k) g t) /\
    step_inst_base (mk_inst id MLOAD [Var src] [t0]) s = OK u /\
    lookup_var t0 u = SOME (mload (w2n a) s) /\ op_taint t (Var t0) = {} /\
    u.vs_memory = s.vs_memory /\ t.t_mem = tn.t_mem /\
    t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
    (!p. p <> t0 ==> lookup_var p u = lookup_var p s /\
      FLOOKUP g p = FLOOKUP G p /\ op_taint t (Var p) = op_taint tn (Var p))` by
    (irule for_copy_header_endpoint >> simp[]) >>
  `?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG g t
      [mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]] (u with vs_inst_idx := k) gf tf) /\
    run_inst_seq [mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
       mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
       mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]] u = OK sf /\
    lookup_var t3 sf = SOME (((mload (w2n a) s+31w) && i2w (-32)) + 32w) /\
    op_taint tf (Var t3) = {} /\ sf.vs_memory = u.vs_memory /\
    tf.t_mem = t.t_mem /\ tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\
    (!p. p <> t1 /\ p <> t2 /\ p <> t3 ==> lookup_var p sf = lookup_var p u /\
      FLOOKUP gf p = FLOOKUP g p /\ op_taint tf (Var p) = op_taint t (Var p))` by
    (irule (SRULE [GSYM ADD_ASSOC]
      (Q.INST [`id` |-> `id+1`] (SPEC_ALL for_copy_len_suffix))) >> simp[]) >>
  qexistsl [`sf`, `gf`, `tf`] >> conj_tac
  >- (irule for_inst_seq_ptr_cons_nonterminator >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`g`, `t`, `u`] >> simp[]) >>
  simp[Once run_inst_seq_def] >> metis_tac[]
QED

Theorem for_ptr_covers_transport:
  lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
  op_taint tf (Var p) = op_taint tn (Var p) ==>
  (ptr_covers gf tf p sf n <=> ptr_covers G tn p s n)
Proof
  simp[ptr_covers_def]
QED

Theorem for_bytes_runtime_extent:
  len <= cap /\ 32 + 32 * word_size cap < dimword (:256) ==>
  w2n ((((n2w len:bytes32) + 31w) && i2w (-32)) + 32w) =
    32 + 32 * word_size len /\
  32 + 32 * word_size len <= 32 + 32 * word_size cap /\
  32 + 32 * word_size len < dimword (:256)
Proof
  strip_tac >>
  `word_size len <= word_size cap` by
    (irule exprSimHypsTheory.word_size_monotone >> simp[]) >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  simp[buffer_round_size]
QED

Theorem for_bytes_copy_endpoint:
  pre = [mk_inst id MLOAD [Var src] [t0];
         mk_inst (id+1) ADD [Var t0; Lit 31w] [t1];
         mk_inst (id+2) AND [Var t1; Lit (i2w (-32))] [t2];
         mk_inst (id+3) ADD [Var t2; Lit 32w] [t3]] /\
  n = (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) /\
  32 <= w2n n /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
  dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3 /\
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ val_wf tv v /\ val_footprint tv v <= w2n n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (pre ++ [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []])
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq (pre ++ [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []]) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + w2n n}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. p <> t0 /\ p <> t1 /\ p <> t2 /\ p <> t3 ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all for_bytes_length_prefix >> disch_then (strip_assume_tac o SPEC_ALL) >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   ptr_covers gf tf src sf (w2n n) /\ ptr_covers gf tf dst sf (w2n n)` by
    (simp[] >> conj_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `?tfinal sfinal.
    inst_seq_ptr D 0 ctx fn PG gf tf
      [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []] sf gf tfinal /\
    run_inst_seq [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []] sf = OK sfinal /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+w2n n} sfinal.vs_memory sf.vs_memory /\
    tfinal.t_stor = tf.t_stor /\ tfinal.t_trans = tf.t_trans /\
    (!p. lookup_var p sfinal = lookup_var p sf /\ op_taint tfinal (Var p) = op_taint tf (Var p)) /\
    (!m. mem_agree_outside tfinal.t_mem sfinal.vs_memory m ==> val_in_memory tv v (w2n b) m)` by
    (irule for_bulk_copy_robust_checked >> simp[eval_operand_def] >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG gf tf
     [mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []]
     (sf with vs_inst_idx := k) gf tfinal` by
    (`step_inst_base (mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []) sf =
       OK (mcopy (w2n b) (w2n a) (w2n n) sf)` by
       (simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
     qpat_x_assum `step_inst_base _ sf = _` (fn th =>
       qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
         (strip_assume_tac o SRULE [inst_seq_ptr_def, th])) >>
     qpat_x_assum `tfinal = _` SUBST1_TAC >>
     irule for_bulk_copy_checked_uniform >> simp[eval_operand_def]) >>
  qexistsl [`sfinal`, `gf`, `tfinal`] >> conj_tac
  >- (irule for_inst_seq_ptr_append_uniform >>
      reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`gf`, `sf`, `tf`] >> simp[]) >>
  conj_tac
  >- (rev_drule run_inst_seq_append >>
      disch_then (qspec_then `[mk_inst (id+4) MCOPY [Var dst; Var src; Var t3] []]` mp_tac) >>
      simp[]) >> gvs[]
QED

Theorem for_bytes_typed_layout:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?len cap.
    ((?bs. tv = BaseTV (BytesT (Dynamic cap)) /\ v = BytesV bs /\ len = LENGTH bs) \/
     (?str. tv = BaseTV (StringT cap) /\ v = StringV str /\ len = LENGTH str)) /\
    len <= cap /\ type_memory_size tv = 32 + 32 * word_size cap /\
    val_footprint tv v <= 32 + 32 * word_size len
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
    val_footprint_def, type_memory_size_def] >>
  simp[valueTypingMemoryPropsTheory.word_size_capacity]
QED

Theorem for_compile_bytes_copy_checked:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + type_memory_size tv}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> drule_all for_bytes_typed_layout >> strip_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    (irule for_bytes_copy_header >> metis_tac[]) >>
  `32 + 32 * word_size cap < dimword (:256)` by metis_tac[] >>
  drule_all for_bytes_runtime_extent >> strip_tac >>
  drule for_bytes_copy_code >> strip_tac >>
  `src <> t0 /\ src <> t1 /\ src <> t2 /\ src <> t3 /\
   dst <> t0 /\ dst <> t1 /\ dst <> t2 /\ dst <> t3` by metis_tac[] >>
  qabbrev_tac `pre = [mk_inst sa.cs_next_id MLOAD [Var src] [t0];
    mk_inst (sa.cs_next_id+1) ADD [Var t0; Lit 31w] [t1];
    mk_inst (sa.cs_next_id+2) AND [Var t1; Lit (i2w (-32))] [t2];
    mk_inst (sa.cs_next_id+3) ADD [Var t2; Lit 32w] [t3]]` >>
  `pre = [mk_inst sa.cs_next_id MLOAD [Var src] [t0];
    mk_inst (sa.cs_next_id+1) ADD [Var t0; Lit 31w] [t1];
    mk_inst (sa.cs_next_id+2) AND [Var t1; Lit (i2w (-32))] [t2];
    mk_inst (sa.cs_next_id+3) ADD [Var t2; Lit 32w] [t3]]` by simp[Abbr `pre`] >>
  qabbrev_tac `n = (((mload (w2n a) s + 31w) && i2w (-32)) + 32w)` >>
  `n = (((mload (w2n a) s + 31w) && i2w (-32)) + 32w)` by simp[Abbr `n`] >>
  `32 <= w2n n /\ w2n n <= type_memory_size tv /\ val_footprint tv v <= w2n n` by
    (gvs[Abbr `n`]) >>
  `ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n)` by
    (gvs[ptr_covers_def] >> conj_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all for_bytes_copy_endpoint >> disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`sf`, `gf`, `tf`] >> gvs[Abbr `pre`] >>
  gvs[mem_agree_outside_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem for_iter_bytes_copy_checked:
  is_bytestring_type ty /\
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + type_memory_size tv}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    gvs[forPtrCopyInterfaceTheory.for_memory_element_copy_dispatch] >>
  irule for_compile_bytes_copy_checked >> simp[] >> metis_tac[]
QED
