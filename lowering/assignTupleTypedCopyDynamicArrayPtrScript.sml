(* Dynamic typed-copy execution: live length and recursive loop resources. *)
Theory assignTupleTypedCopyDynamicArrayPtr
Ancestors
  assignBasePtrBytesPrefix assignTupleTypedCopyArrayPtr typedCopyLayoutPtr
  bodyPtrPopMemoryHeader bodyPtrMakeArrayWordStore bodyPtrMakeArrayCopyStep
  wordLoadStorePtr valueEncodingProps representationCleanPtr
  augAssignPtrScalarCertificate
  augAssignPtrScalarSafety augAssignPtrScalarRun
  typedNormalizeDynarrayLoop typedCopyAmbientFramePtr
  bodyPtrDefs ptrDiscipline ptrSafeRun fragGasSeqPtr
  venomState venomInst venomExecSemantics venomInstProofs
  exprSimBufferStore valueEncodingDefs exprLoweringProps fragExec finite_map words arithmetic list pred_set

Theorem typed_dynarray_load_length_ptr:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm u.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [len]] (s with vs_inst_idx := k) H tm) /\
    run_inst_seq [mk_inst id MLOAD [Var src] [len]] s = OK u /\
    u = update_var len (n2w (LENGTH vs)) s /\
    lookup_var len u = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> len ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def, mem_bytes_at_def]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  drule_all assign_base_bytes_mload_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `id`, `len`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `u`] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The bound check keeps the loaded scalar live and provenance-free. *)
Theorem typed_dynarray_check_length_ptr:
  lookup_var len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  len <> long /\ len <> ok /\ ~ctx_has_dalloca ctx ==>
  ?H tm.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s H tm /\
    run_inst_seq
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s =
      OK (update_var ok 1w (update_var long 0w s)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> long /\ p <> ok ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+1) ISZERO [Var long] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  `scalar_code {len} code` by
    simp[Abbr `code`, scalar_code_def, scalar_shape_def, scalar_binary_def,
         scalar_unary_def, scalar_available_def, mk_inst_def] >>
  `!v. v IN {len} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var long 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     `n < dimword(:256)` by decide_tac >>
     gvs[lookup_var_def]) >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >>
  gvs[Abbr `code`, mk_inst_def, op_prov_def] >> metis_tac[]
QED

(* The checked prefix chooses a single semantic/ghost endpoint. *)
Triviality typed_dynarray_load_check_ptr:
  code =
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] []] /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ LENGTH vs <= cap /\ cap < dimword(:256) /\
  len <> long /\ len <> ok /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic source_cap))
      (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm u.
    inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
    run_inst_seq code s = OK u /\
    u = update_var ok 1w (update_var long 0w
      (update_var len (n2w (LENGTH vs)) s)) /\
    lookup_var len u = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> len /\ p <> long /\ p <> ok ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all typed_dynarray_load_length_ptr >>
  disch_then (qspecl_then [`len`, `id`, `fn`, `PG`, `D`]
    (qx_choose_then `g1` (qx_choose_then `t1`
      (qx_choose_then `s1` strip_assume_tac)))) >>
  qabbrev_tac `s2 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var len s2 = SOME (n2w (LENGTH vs))` by simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  mp_tac (Q.INST [`s` |-> `s2`, `G` |-> `g1`, `tn` |-> `t1`,
    `n` |-> `LENGTH (vs:value list)`, `id` |-> `id+1`] typed_dynarray_check_length_ptr) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2` strip_assume_tac)) >>
  qexistsl_tac [`g2`, `t2`,
    `update_var ok 1w (update_var long 0w s1)`] >>
  conj_tac >- suspend "checked_prefix" >>
  conj_tac >- suspend "checked_run" >>
  gvs[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED
Resume typed_dynarray_load_check_ptr[checked_prefix]:
  qpat_x_assum `code = _` SUBST1_TAC >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >>
  qpat_x_assum `run_inst_seq [_] s = OK s1` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  gvs[Abbr `s2`, ADD_ASSOC, inst_seq_ptr_def]
QED
Resume typed_dynarray_load_check_ptr[checked_run]:
  `LENGTH vs < dimword(:256)` by decide_tac >>
  qpat_x_assum `run_inst_seq [_] s = OK s1` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, exec_pure1_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
QED
Finalise typed_dynarray_load_check_ptr

(* A clean header store exposes the actual singleton endpoint and its complete
   exterior frame; all variables (not only older compiler variables) survive. *)
Triviality typed_dynarray_store_length_frag_ptr:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id MSTORE [Var dst; value] []] /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?tm u.
    frag_exec_ptr cx ctx PG sa sb (\g t v. g = G /\ t = tn /\ v = s)
      (\g t v. g = G /\ t = tm /\ v = u) R /\
    (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
      mem_word_at (w2n a) m = w) /\
    (u with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p n. p+n <= w2n a \/ w2n a+32 <= p ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!p. p < w2n a \/ w2n a+32 <= p ==>
      (p IN tm.t_mem <=> p IN tn.t_mem)) /\
    (!x. lookup_var x u = lookup_var x s /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  qabbrev_tac `tm = step_taint (mk_inst id MSTORE [Var dst; value] []) s u tn` >>
  `step_prov PG G (mk_inst id MSTORE [Var dst; value] []) u = G /\
   tm.t_var = tn.t_var /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
   tm.t_imm = tn.t_imm /\
   tm.t_mem = tn.t_mem DIFF {p | w2n a <= p /\ p < w2n a+32}` by
    simp[Abbr `tm`, Abbr `u`, mstore_raw_ghost_frame] >>
  qexistsl_tac [`tm`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (irule mstore_frag_ptr >> simp[] >>
      qexistsl_tac [`dst`, `id`, `value`] >>
      simp[Abbr `tm`, Abbr `u`]) >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_raw_robust_word >>
      qexistsl_tac [`dst`, `id`, `s`, `tn`, `tm`, `value`] >>
      gvs[Abbr `tm`, Abbr `u`]) >>
  conj_tac >- simp[Abbr `u`, mstore_def] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[Abbr `u`] >>
      irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[Abbr `u`, mstore_def, lookup_var_def, op_taint_def]
QED

(* The child premise ranges over actual compiler slices and arbitrary runtime
   states. Capacity windows are geometric, not taint-cleanliness assumptions. *)
Theorem compile_copy_dynarray_typed_child_frag_ptr:
  !ce st dt stv dtv vs source_cap cap dst src sa sb cx ctx PG R.
  type_memory_size stv = type_memory_bytes ce st /\
  type_memory_size dtv = type_memory_bytes ce dt /\
  LENGTH vs <= source_cap /\ LENGTH vs <= cap /\ cap < dimword(:256) /\
  EVERY (\v. value_has_type stv v /\ value_has_type dtv v) vs /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (dt = st ==> dtv = stv) /\
  (!sc ec sop dop v.
    compile_store_memory_typed ce dop dt sop st sc = ((),ec) /\
    (!x. sop = Var x \/ dop = Var x ==> not_fresh_at sc x) /\
    value_has_type stv v /\ value_has_type dtv v ==>
    !G tn s p q.
    eval_operand sop s = SOME p /\ eval_operand dop s = SOME q /\
    (type_memory_bytes ce st = 0 \/
      ?x. sop = Var x /\ ptr_covers G tn x s (type_memory_bytes ce st)) /\
    (type_memory_bytes ce dt = 0 \/
      ?x. dop = Var x /\ ptr_covers G tn x s (type_memory_bytes ce dt)) /\
    w2n p + type_memory_bytes ce st <= s.vs_alloca_next /\
    w2n q + type_memory_bytes ce dt <= s.vs_alloca_next /\
    w2n p + type_memory_bytes ce st <= dimword(:256) /\
    w2n q + type_memory_bytes ce dt <= dimword(:256) /\
    (w2n p + type_memory_bytes ce st <= w2n q \/
      w2n q + type_memory_bytes ce dt <= w2n p) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n p) m) ==>
    frag_exec_ptr cx ctx PG sc ec (\g t u. g = G /\ t = tn /\ u = s)
      (\H tm u.
        (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
          val_in_memory dtv v (w2n q) m) /\
        (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
          vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
          vs_prev_bb := s.vs_prev_bb|>) = s /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!a n. a+n <= w2n q \/ w2n q + type_memory_bytes ce dt <= a ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory) /\
        (!a. a < w2n q \/ w2n q + type_memory_bytes ce dt <= a ==>
          (a IN tm.t_mem <=> a IN tn.t_mem)) /\
        (!x. not_fresh_at sc x ==>
          lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x))) R) ==>
  !G tn s p q.
  eval_operand src s = SOME p /\ eval_operand dst s = SOME q /\
  (32 + source_cap * type_memory_bytes ce st = 0 \/
    ?x. src = Var x /\ ptr_covers G tn x s
      (32 + source_cap * type_memory_bytes ce st)) /\
  (32 + cap * type_memory_bytes ce dt = 0 \/
    ?x. dst = Var x /\ ptr_covers G tn x s
      (32 + cap * type_memory_bytes ce dt)) /\
  w2n p + (32 + source_cap * type_memory_bytes ce st) <= s.vs_alloca_next /\
  w2n q + (32 + cap * type_memory_bytes ce dt) <= s.vs_alloca_next /\
  w2n p + (32 + source_cap * type_memory_bytes ce st) <= dimword(:256) /\
  w2n q + (32 + cap * type_memory_bytes ce dt) <= dimword(:256) /\
  (w2n p + (32 + source_cap * type_memory_bytes ce st) <= w2n q \/
    w2n q + (32 + cap * type_memory_bytes ce dt) <= w2n p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic source_cap))
      (ArrayV (DynArrayV vs)) (w2n p) m) ==>
  frag_exec_ptr cx ctx PG sa sb (\g t u. g = G /\ t = tn /\ u = s)
    (\H tm u.
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory (ArrayTV dtv (Dynamic cap))
          (ArrayV (DynArrayV vs)) (w2n q) m) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
        vs_prev_bb := s.vs_prev_bb|>) = s /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!a n. a+n <= w2n q \/ w2n q + (32 + cap * type_memory_bytes ce dt) <= a ==>
        mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory) /\
      (!a. a < w2n q \/ w2n q + (32 + cap * type_memory_bytes ce dt) <= a ==>
        (a IN tm.t_mem <=> a IN tn.t_mem)) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))) R
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dt = st`
  >- suspend "equal_layout"
  >> suspend "element_loop"
QED
