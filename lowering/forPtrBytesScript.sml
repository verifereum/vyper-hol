(* Counted bytestring copies: only the length word must be clean. *)
Theory forPtrBytes
Ancestors forPtrBulk typedCopyPtr representationCleanPtr valueCopyBytes
  exprSimBufferStore valueEncoding valueEncodingProps bodyPtrDefs
  loweringPosts venomState venomExecSemantics venomInst ptrSafeRun
  ptrDiscipline fragGasSeqPtr ghostPcTransportPtr finite_map exprLoweringProps
  context compileEnv emitHelper loweringSlice list rich_list words integer_word arithmetic

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
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_pure2_def]
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
