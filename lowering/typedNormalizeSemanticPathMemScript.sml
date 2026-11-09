(* Typed semantic instantiation of finite static-array memory paths. *)
Theory typedNormalizeSemanticPathMem
Ancestors
  typedArrayCompilerPathMem typedNormalizeSemanticMem typedMemoryCopy
  valueEncodingProps valueEncodingTyping exprLowering compileEnv venomState
  venomExecSemantics fragGasPathMem arithmetic words list vyperTyping
  valueEncoding exprSimDefs exprSimProps loweringPosts valueEncodingProofs

Theorem normalize_sarray_indexed_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  type_memory_bytes ce st = type_memory_size stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  (!j. j < n ==> val_wf stv (f j) /\ val_wf dtv (f j) /\
    value_has_type stv (f j) /\ value_has_type dtv (f j)) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword(:256) /\
  a + type_memory_size stv * n <= s.vs_alloca_next /\
  b + type_memory_size dtv * n <= s.vs_alloca_next /\
  a + type_memory_size stv * n < dimword(:256) /\
  b + type_memory_size dtv * n < dimword(:256) /\
  (a + type_memory_size stv * n <= b \/ b + type_memory_size dtv * n <= a) /\
  (!j. j < n ==> val_in_memory stv (f j)
    (a + type_memory_size stv * j) s.vs_memory) /\
  (!cv sp dp sc ec u sw dw.
    val_wf stv cv /\ val_wf dtv cv /\
    value_has_type stv cv /\ value_has_type dtv cv /\
    compile_store_memory_typed ce dp dt sp st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand sp u = SOME sw /\ eval_operand dp u = SOME dw /\
    val_in_memory stv cv (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      val_in_memory dtv cv (w2n dw) v.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
      LENGTH u.vs_memory <= LENGTH v.vs_memory) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!j. j < n ==> val_in_memory dtv (f j)
      (b + type_memory_size dtv * j) t.vs_memory) /\
    (!p k. p+k <= b \/ b+type_memory_size dtv*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Child ==> _` >> disch_tac >>
  mp_tac (Q.INST [`Src` |-> `\j p m. val_in_memory stv (f j) p m`,
    `D` |-> `\j p m. val_in_memory dtv (f j) p m`] typed_sarray_compiler_path_mem) >>
  (impl_tac >- (simp[] >>
    (conj_tac >- gvs[]) >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- (rpt strip_tac >> irule normalize_indexed_value_local >> metis_tac[])) >>
    (conj_tac >- (rpt strip_tac >> irule normalize_indexed_value_local >> metis_tac[])) >>
    (conj_tac >- (qpat_x_assum `!j. j < n ==> val_in_memory stv _ _ _`
      mp_tac >> simp[MULT_COMM])) >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    `a + j * type_memory_size stv + type_memory_size stv <=
       a + n * type_memory_size stv /\
     b + j * type_memory_size dtv + type_memory_size dtv <=
       b + n * type_memory_size dtv` by
      metis_tac[typed_copy_array_subinterval] >>
    `a + j * type_memory_size stv < dimword(:256) /\
     b + j * type_memory_size dtv < dimword(:256)` by decide_tac >>
    `(!x. Var ("%" ++ toString (sa.cs_next_var+5)) = Var x \/
            Var ("%" ++ toString (sa.cs_next_var+6)) = Var x ==>
         not_fresh_at sc x)` by (simp[] >> metis_tac[]) >>
    qpat_x_assum `Child` mp_tac >> simp[Abbr `Child`] >>
    disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
    disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
    disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
    disch_then (qspec_then `f j` mp_tac) >> simp[] >>
    (impl_tac >- (rpt conj_tac >> gvs[])) >>
    strip_tac >> qexistsl_tac [`v`, `g`] >> simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl_tac [`t`, `g`] >>
  qpat_x_assum `Abbrev (Child = _)` kall_tac >>
  qpat_x_assum `Child` kall_tac >>
  gvs[MULT_COMM, ADD_COMM] >> first_assum ACCEPT_TAC
QED

Theorem normalize_sarray_semantic_path_mem:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  type_memory_bytes ce st = type_memory_size stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  type_widens_to tenv st dt /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  value_has_type (ArrayTV stv (Fixed n)) value /\
  value_has_type (ArrayTV dtv (Fixed n)) value /\
  val_wf (ArrayTV stv (Fixed n)) value /\
  val_wf (ArrayTV dtv (Fixed n)) value /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword(:256) /\
  a + type_memory_size (ArrayTV stv (Fixed n)) <= s.vs_alloca_next /\
  b + type_memory_size (ArrayTV dtv (Fixed n)) <= s.vs_alloca_next /\
  a + type_memory_size (ArrayTV stv (Fixed n)) < dimword(:256) /\
  b + type_memory_size (ArrayTV dtv (Fixed n)) < dimword(:256) /\
  (a + type_memory_size (ArrayTV stv (Fixed n)) <= b \/
   b + type_memory_size (ArrayTV dtv (Fixed n)) <= a) /\
  val_in_memory (ArrayTV stv (Fixed n)) value a s.vs_memory /\
  (!cv sp dp sc ec u sw dw.
    val_wf stv cv /\ val_wf dtv cv /\
    value_has_type stv cv /\ value_has_type dtv cv /\
    compile_store_memory_typed ce dp dt sp st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand sp u = SOME sw /\ eval_operand dp u = SOME dw /\
    val_in_memory stv cv (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      val_in_memory dtv cv (w2n dw) v.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
      LENGTH u.vs_memory <= LENGTH v.vs_memory) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Fixed n)) value b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size (ArrayTV dtv (Fixed n)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `value` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `SArrayV kvs` >>
  qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Child ==> _` >> disch_tac >>
  `value_has_type (ArrayTV stv (Fixed n)) (ArrayV (SArrayV kvs)) /\
   value_has_type (ArrayTV dtv (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_def] >>
  drule_all typed_copy_sarray_representation >> strip_tac >>
  qabbrev_tac `f = \i. case ALOOKUP kvs i of
    NONE => default_value stv | SOME v => v` >>
  `!i. i < n ==> value_has_type stv (f i) /\ value_has_type dtv (f i)` by
    (rpt gen_tac >> strip_tac >>
     `default_value stv = default_value dtv` by
       metis_tac[typed_copy_default_widening] >>
     qpat_x_assum `Abbrev (Child = _)` kall_tac >>
     qpat_x_assum `Child` kall_tac >>
     simp[Abbr `f`] >> Cases_on `ALOOKUP kvs i` >> simp[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
          cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     conj_tac >> irule valueEncodingProofsTheory.sparse_has_type_lookup >>
     qexistsl_tac [`i`,`kvs`,`n`] >> simp[]) >>
  mp_tac (Q.INST [`f` |-> `f`] normalize_sarray_indexed_path_mem) >>
  (impl_tac >-
    (reverse (rpt conj_tac)
     >- (qpat_x_assum `Child` mp_tac >>
         simp[Abbr `Child`,NoAsms,ADD_COMM]) >>
     qpat_x_assum `Abbrev (Child = _)` kall_tac >>
     qpat_x_assum `Child` kall_tac >>
     gvs[type_memory_size_def,MULT_COMM,ADD_COMM,Abbr `f`])) >>
  strip_tac >> qexistsl_tac [`t`,`g`] >>
  qpat_x_assum `Abbrev (Child = _)` kall_tac >>
  qpat_x_assum `Child` kall_tac >>
  gvs[type_memory_size_def, MULT_COMM, ADD_COMM] >> first_assum ACCEPT_TAC
QED
