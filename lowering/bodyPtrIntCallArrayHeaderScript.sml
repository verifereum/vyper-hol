(* Dynamic typed-copy prefix: representation supplies the checked length. *)
Theory bodyPtrIntCallArrayHeader
Ancestors bodyPtrBopInHeaderControl bodyPtrBopInMemoryContents bodyPtrBopInElementLoad
  bodyPtrIntCallFieldOffset augAssignPtrStore annAssignPtrLength
  typedCopyLayoutPtr valueEncodingProps vyperTyping venomMemDefs bodyPtrDefs
  venomExecSemantics venomState ptrDiscipline fragGasPathPtr
  words finite_map pred_set arithmetic freshWrites bodyPtrMakeArrayWordStore
  loweringPosts exprSimProps emitHelperProps valueEncodingTyping

Theorem intcall_dynamic_checked_length[local]:
  !D ctx fn PG G tn s bb id src hdr flag valid stv dtv scap dcap vs a.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [hdr]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) GT [Var hdr;Lit (n2w dcap)] [flag]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ISZERO [Var flag] [valid]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ASSERT [Var valid] []) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    value_has_type (ArrayTV dtv (Dynamic dcap)) (ArrayV (DynArrayV vs)) /\
    dcap < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
    ?H tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      z = (update_var valid 1w (update_var flag 0w
        (update_var hdr (n2w (LENGTH vs)) s)) with vs_inst_idx := s.vs_inst_idx+4) /\
      tf = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
      (hdr <> flag /\ hdr <> valid ==> FLOOKUP H hdr = NONE) /\
      (!x. x <> hdr /\ x <> flag /\ x <> valid ==> FLOOKUP H x = FLOOKUP G x)
Proof
  rpt gen_tac >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    metis_tac[dynarray_memory_header_clean] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, valueEncodingTheory.mem_word_at_def]) >>
  `LENGTH vs <= dcap` by fs[value_has_type_def] >>
  drule_all membership_positioned_mload_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >>
  drule_all membership_loaded_header_capacity_path >>
  strip_tac >> metis_tac[]
QED

Theorem intcall_dynamic_checked_prefix[local]:
  (do len <- compile_ptr_load F NONE LocMemory (Var src);
      flag <- emit_op GT [len;Lit (n2w dcap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sm) /\
  fn_has_code sa sm fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  value_has_type (ArrayTV dtv (Dynamic dcap)) (ArrayV (DynArrayV vs)) /\
  dcap < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tf z.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
    z.vs_current_bb = sm.cs_current_bb /\
    z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
    eval_operand len z = SOME (n2w (LENGTH vs)) /\
    op_prov H len = NONE /\ op_taint tf len = {} /\
    (z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all bodyPtrBopInHeaderCodeTheory.membership_runtime_header_code >> strip_tac >>
  drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  qpat_x_assum `s.vs_current_bb = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  drule_all intcall_dynamic_checked_length >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       op_taint_def, venom_state_component_equality] >>
  conj_tac
  >- simp[op_prov_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var) /\
   x <> STRING #"%" (toString (sa.cs_next_var+1)) /\
   x <> STRING #"%" (toString (sa.cs_next_var+2))` by
    (fs[compileEnvTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  simp[]
QED

(* The four compiler intervals are exactly the dynamic-copy header prefix.
   Keeping the cut points explicit lets either payload branch reuse the path. *)
Theorem intcall_dynamic_array_header_counted:
  (do len <- compile_ptr_load F NONE LocMemory (Var src);
      flag <- emit_op GT [len;Lit (n2w dcap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sm) /\
  emit_void MSTORE [Var dst;len] sm = ((),sc) /\
  compile_with_byte_offset (Var src) 32 sc = (sp,sd) /\
  compile_with_byte_offset (Var dst) 32 sd = (dp,se) /\
  fn_has_code sa sm fn /\ fn_has_code sm sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32 + scap * type_memory_size stv) /\
  ptr_covers G tn dst s (32 + dcap * type_memory_size dtv) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV dtv (Dynamic dcap)) (ArrayV (DynArrayV vs)) /\
  dcap < dimword (:256) /\
  w2n a + val_footprint (ArrayTV stv (Dynamic scap))
    (ArrayV (DynArrayV vs)) < dimword (:256) /\
  w2n b + 32 + dcap * type_memory_size dtv < dimword (:256) /\
  (w2n a + 32 + scap * type_memory_size stv <= w2n b \/
   w2n b + 32 + dcap * type_memory_size dtv <= w2n a) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tf z ps pd.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
    sp = Var ps /\ dp = Var pd /\
    not_fresh_at se ps /\ not_fresh_at se pd /\
    z.vs_current_bb = se.cs_current_bb /\
    z.vs_inst_idx = LENGTH se.cs_current_insts /\ ~z.vs_halted /\
    eval_operand len z = SOME (n2w (LENGTH vs)) /\
    op_prov H len = NONE /\ op_taint tf len = {} /\
    lookup_var ps z = SOME (n2w (w2n a+32)) /\
    lookup_var pd z = SOME (n2w (w2n b+32)) /\
    ptr_covers H tf ps z (scap * type_memory_size stv) /\
    ptr_covers H tf pd z (dcap * type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
      mem_word_at (w2n b) m = n2w (LENGTH vs) /\
      val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
    z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
    z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `ptr_covers G tn src s 32` by (fs[ptr_covers_def] >> decide_tac) >>
  drule_all intcall_dynamic_checked_prefix >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H1 t1 (OK z1)` >>
  `ptr_covers H1 t1 dst z1 32 /\ lookup_var dst z1 = SOME b` by
    (gvs[ptr_covers_def] >> decide_tac) >>
  drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sc.cs_next_var` by
    (drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
     drule emitted_insts_emit_void >> simp[]) >>
  `not_fresh_at sc src /\ not_fresh_at sc dst` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   ptr_covers H1 tnf src sf (32 + scap * type_memory_size stv) /\
   ptr_covers H1 tnf dst sf (32 + dcap * type_memory_size dtv)` by
    (gvs[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  `w2n a + 32 < dimword (:256)` by
    (fs[val_footprint_def, valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `32 + scap * type_memory_size stv <= 32 + scap * type_memory_size stv` by simp[] >>
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H1 tnf sf 0 H2 t2 (OK z2)` >>
  `not_fresh_at sd dst` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var dst z2 = SOME b /\
   ptr_covers H2 t2 dst z2 (32 + dcap * type_memory_size dtv)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `w2n b + 32 < dimword (:256)` by decide_tac >>
  `32 + dcap * type_memory_size dtv <= 32 + dcap * type_memory_size dtv` by simp[] >>
  qpat_x_assum `compile_with_byte_offset (Var src) 32 sc = _` kall_tac >>
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H2 t2 z2 0 H3 t3 (OK z3)` >>
  `not_fresh_at se p /\
   lookup_var p z3 = SOME (n2w (w2n a+32)) /\
   ptr_covers H3 t3 p z3 (scap * type_memory_size stv)` by
    (gvs[ptr_covers_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `z1.vs_memory = s.vs_memory /\ z2.vs_memory = sf.vs_memory /\
   z3.vs_memory = sf.vs_memory` by fs[venom_state_component_equality] >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    mem_word_at (w2n b) m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     `mem_agree_outside tnf.t_mem
       (mstore (w2n b) (n2w (LENGTH vs)) z1).vs_memory m` by gvs[] >>
     drule_all mstore_raw_robust_word >> simp[]) >>
  `val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))` by
    metis_tac[value_has_type_val_wf] >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m` by
    (rpt strip_tac >> irule mstore_robust_exterior >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w2n b`, `z1`, `tn.t_mem`, `n2w (LENGTH vs)`] >>
     conj_tac >- gvs[] >> conj_tac
     >- (simp[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
         gvs[value_has_type_def] >> decide_tac) >>
     gvs[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H3 t3 (OK z3)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  `len = Var ("%" ++ toString sa.cs_next_var)` by
    (drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >> simp[]) >>
  `not_fresh_at sc ("%" ++ toString sa.cs_next_var)` by
    (drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
     drule emitted_insts_emit_void >> simp[compileEnvTheory.not_fresh_at_def]) >>
  `not_fresh_at sd ("%" ++ toString sa.cs_next_var)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl_tac [`H3`, `t3`, `z3`, `p`, `p'`] >> simp[] >>
  (conj_tac >- (gvs[eval_operand_def] >> metis_tac[]) >>
   conj_tac >- (gvs[op_prov_def] >> metis_tac[]) >>
   conj_tac >- (gvs[op_taint_def] >> metis_tac[]) >>
   conj_tac >- gvs[step_taint_def, imm_taint_def] >>
   `z3.vs_allocas = s.vs_allocas /\ z3.vs_alloca_next = s.vs_alloca_next /\
    z3.vs_fmp = s.vs_fmp /\ z3.vs_accounts = s.vs_accounts /\
    z3.vs_transient = s.vs_transient /\ z3.vs_call_ctx = s.vs_call_ctx` by
     gvs[venom_state_component_equality, mstore_def] >>
   simp[] >> conj_tac
   >- (rpt strip_tac >>
       `not_fresh_at sc x /\ not_fresh_at sd x` by
         metis_tac[freshWritesTheory.not_fresh_at_mono] >>
       gvs[op_taint_def] >> metis_tac[]) >>
   rpt strip_tac >>
   `mem_bytes_at i 1 (mstore (w2n b) (n2w (LENGTH vs)) z1).vs_memory =
    mem_bytes_at i 1 z1.vs_memory` by
     (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
   gvs[])
QED
