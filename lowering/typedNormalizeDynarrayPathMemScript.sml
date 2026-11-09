(* Same-endpoint typed semantics for finite dynamic-array normalization. *)
Theory typedNormalizeDynarrayPathMem
Ancestors
  typedDynarrayCompilerPathMem typedDynarrayPrefixPathMem
  typedNormalizeSemanticPathMem typedNormalizeSemanticMem typedMemoryCopy
  valueEncodingProps valueEncodingTyping valueEncodingProofs vyperTyping
  exprLowering compileEnv venomState venomExecSemantics fragGasPathMem
  arithmetic words list valueEncoding exprSimDefs exprSimProps loweringPosts
  abiStaticAggregateProps

Theorem normalize_dynarray_semantic_path_mem:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  type_memory_bytes ce st = type_memory_size stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  scap <= cap /\ cap < dimword(:256) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword(:256) /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword(:256) /\
  (a + type_memory_size (ArrayTV stv (Dynamic scap)) <= b \/
   b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= a) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) a s.vs_memory /\
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
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size (ArrayTV dtv (Dynamic cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Child ==> _` >> disch_tac >>
  rename1 `val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vals))` >>
  `!i. i < LENGTH vals ==> val_wf stv (EL i vals) /\ val_wf dtv (EL i vals) /\
    value_has_type stv (EL i vals) /\ value_has_type dtv (EL i vals)` by
    (gvs[typed_copy_dynarray_wf,value_has_type_def,all_have_type_EVERY,EVERY_EL]) >>
  `LENGTH vals <= scap /\ LENGTH vals <= cap` by gvs[typed_copy_dynarray_wf] >>
  `a+32+type_memory_size stv*LENGTH vals <= a+type_memory_size stv*scap+32 /\
   b+32+type_memory_size dtv*LENGTH vals <= b+type_memory_size dtv*cap+32` by
    (simp[] >> conj_tac >> simp[LE_MULT_LCANCEL]) >>
  `a+32+type_memory_size stv*LENGTH vals <= s.vs_alloca_next /\
   b+32+type_memory_size dtv*LENGTH vals <= s.vs_alloca_next /\
   a+32+type_memory_size stv*LENGTH vals < dimword(:256) /\
   b+32+type_memory_size dtv*LENGTH vals < dimword(:256)` by
    (qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac >>
     rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >> decide_tac) >>
  suspend "prefix"
QED
Resume normalize_dynarray_semantic_path_mem[prefix]:
  `a < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size (ArrayTV stv (Dynamic scap))`,
    `dz` |-> `type_memory_size (ArrayTV dtv (Dynamic cap))`,
    `p` |-> `n2w a`, `d` |-> `n2w b`,
    `n` |-> `LENGTH (vals:value list)`] typed_dynarray_prefix_path_mem) >>
  (impl_tac >-
    (qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac >>
     gvs[type_memory_size_def,typed_copy_dynarray_representation,mem_word_at_eq_mload] >>
     metis_tac[LESS_EQ_TRANS])) >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  suspend "suffix"
QED
Resume normalize_dynarray_semantic_path_mem[suffix]:
  mp_tac (Q.INST [`s` |-> `q`, `a` |-> `a+32`, `b` |-> `b+32`,
    `sm` |-> `sa with cs_next_var := sa.cs_next_var+5`,
    `Src` |-> `\j p m. val_in_memory stv (EL j vals) p m`,
    `D` |-> `\j p m. val_in_memory dtv (EL j vals) p m`,
    `n` |-> `LENGTH (vals:value list)`] typed_dynarray_suffix_path_mem) >>
  (impl_tac >- (simp[] >> suspend "suffix_premises")) >>
  strip_tac >> suspend "finish"
QED
Resume normalize_dynarray_semantic_path_mem[suffix_premises]:
  reverse (rpt conj_tac) >- suspend "child" >>
  qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac
  >- (`val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vals)) a q.vs_memory` by
        (irule val_in_memory_mem_agree >> (conj_tac >- first_assum ACCEPT_TAC) >>
         qexistsl_tac [`type_memory_size (ArrayTV stv (Dynamic scap))`, `s.vs_memory`] >>
         gvs[]) >>
      gvs[typed_copy_dynarray_representation,ADD_COMM])
  >- (rpt strip_tac >> irule normalize_indexed_value_local >> metis_tac[])
  >- (rpt strip_tac >> irule normalize_indexed_value_local >> metis_tac[])
  >- (pure_rewrite_tac[type_memory_size_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
  qpat_x_assum `a+32+_ <= a+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
  qpat_x_assum `b+32+_ <= b+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
  qpat_x_assum `_ \/ _` mp_tac >>
  map_every Q.SPEC_TAC
    [(`LENGTH vals * type_memory_size stv`, `ns`),
     (`LENGTH vals * type_memory_size dtv`, `nd`),
     (`scap * type_memory_size stv`, `ss`),
     (`cap * type_memory_size dtv`, `ds`)] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> fs[]) >> gvs[]
QED
Resume normalize_dynarray_semantic_path_mem[finish]:
  qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac >>
  qexistsl_tac [`t`,`g`] >>
  conj_tac >- metis_tac[gas_path_mem_then,ADD_CLAUSES] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "representation" >>
  conj_tac >- suspend "outside" >>
  reverse conj_tac >- suspend "registers" >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = q` mp_tac >>
  qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
  qpat_x_assum `s.vs_current_bb = _` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED
Resume normalize_dynarray_semantic_path_mem[child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `j < LENGTH vals` >>
  `a+32+j*type_memory_size stv+type_memory_size stv <=
      a+32+LENGTH vals*type_memory_size stv /\
   b+32+j*type_memory_size dtv+type_memory_size dtv <=
      b+32+LENGTH vals*type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  `a+32+type_memory_size stv*j < dimword(:256) /\
   b+32+type_memory_size dtv*j < dimword(:256)` by
    (fs[Once MULT_COMM] >> decide_tac) >>
  `(!x. Var ("%" ++ toString (sa.cs_next_var+10)) = Var x \/
          Var ("%" ++ toString (sa.cs_next_var+11)) = Var x ==>
      not_fresh_at sc x)` by (simp[] >> metis_tac[]) >>
  qpat_x_assum `Child` mp_tac >> simp[Abbr `Child`] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspec_then `EL j vals` mp_tac) >> simp[] >>
  (impl_tac >-
    (conj_tac >- (rpt strip_tac >> gvs[]) >>
     rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
     qpat_x_assum `a+32+_ <= a+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     qpat_x_assum `b+32+_ <= b+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     rpt strip_tac >> decide_tac)) >>
  strip_tac >> qexistsl_tac [`v`,`g`] >> simp[] >> first_assum ACCEPT_TAC
QED
Resume normalize_dynarray_semantic_path_mem[representation]:
  simp[typed_copy_dynarray_representation,mem_word_at_eq_mload] >>
  reverse conj_tac >- gvs[MULT_COMM,ADD_COMM] >>
  `mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> simp[]) >>
  `mem_word_at b t.vs_memory = mem_word_at b q.vs_memory` by
    simp[mem_word_at_bytes] >>
  gvs[GSYM mem_word_at_eq_mload,mstore_mem_word_at_same]
QED
Resume normalize_dynarray_semantic_path_mem[outside]:
  rpt gen_tac >> disch_then (mk_asm "outside") >>
  `b+32+type_memory_bytes ce dt*LENGTH vals <=
    b+type_memory_size (ArrayTV dtv (Dynamic cap))` by
    (simp[type_memory_size_def,MULT_COMM,LE_MULT_RCANCEL]) >>
  `p+k <= b+32 \/ b+32+type_memory_bytes ce dt*LENGTH vals <= p` by
    (pop_assum mp_tac >> asm "outside" mp_tac >>
     map_every Q.SPEC_TAC
       [(`type_memory_size (ArrayTV dtv (Dynamic cap))`,`sz`),
        (`type_memory_bytes ce dt*LENGTH vals`,`ns`)] >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `p+k <= w2n (n2w b:bytes32) \/ w2n (n2w b:bytes32)+32 <= p` by
    (asm "outside" mp_tac >> simp[type_memory_size_def] >>
     rpt strip_tac >> fs[] >> decide_tac) >>
  metis_tac[]
QED
Resume normalize_dynarray_semantic_path_mem[registers]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at (sa with cs_next_var := sa.cs_next_var+5) x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  metis_tac[]
QED
Finalise normalize_dynarray_semantic_path_mem
