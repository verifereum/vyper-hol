(* Checked load/store of the accumulated Concat length. *)
Theory bodyPtrBytestringBuiltinsConcatSuffix
Ancestors
  bodyPtrBytestringBuiltinsConcatCompile annAssignPtrLength bodyPtrPopMemoryStore
  assignTuplePtrLoadStep bodyPtrEnvBuiltinsSelectorBuffer
  fragGasPathPtr bodyPtrDefs emitHelper emitHelperProps compileEnv
  venomState venomInst ptrDiscipline words finite_map pred_set arithmetic
  valueEncodingProps venomMemProps bodyPtrSubscriptSeamMapFrame
  bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrSignedConvertSourceFrame
  exprSimAlloc loweringHalt exprSimProps

Theorem concat_suffix_path_ptr:
  emit_op MLOAD [Var ov] sa = (fo,sm) /\
  emit_void MSTORE [Var bv;fo] sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var bv s = SOME a /\ lookup_var ov s = SOME ow /\
  not_fresh_at sa bv /\ ptr_covers G tn bv s bsz /\ 32 <= bsz /\
  ptr_covers G tn ov s 32 /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) ==>
  ?out H tm u t un.
    fo = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n a) (mload (w2n ow) s) u)
      with vs_inst_idx := SUC u.vs_inst_idx /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    u.vs_memory = s.vs_memory /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    un.t_var = tm.t_var /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    un.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a+32}
      t.vs_memory s.vs_memory /\
    ptr_covers H un bv t bsz
Proof
  strip_tac >>
  `?out. fo = Var out` by metis_tac[emitted_insts_emit_op] >> gvs[] >>
  drule_all annassign_emit_mload_clean_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `ptr_covers Gf tnf bv sf bsz` by
    (qpat_x_assum `ptr_covers _ _ bv _ bsz` mp_tac >>
     qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `bv` mp_tac) >>
     qpat_x_assum `not_fresh_at sa bv` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def]) >>
  `ptr_covers Gf tnf bv sf 32` by
    (qpat_x_assum `ptr_covers _ _ bv _ bsz` mp_tac >>
     qpat_x_assum `32 <= bsz` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  `lookup_var bv sf = SOME a` by metis_tac[] >>
  `eval_operand (Var out) sf = SOME (mload (w2n ow) s)` by simp[eval_operand_def] >>
  drule_all pop_emit_mstore_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume concat_suffix_path_ptr[assemble]:
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tn' (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `!p. op_taint tn' (Var p) = op_taint tnf (Var p)` by
    simp[op_taint_def] >>
  `ptr_covers Gf tn' bv t bsz` by
    (qpat_x_assum `ptr_covers Gf tnf bv sf bsz` mp_tac >>
     qpat_x_assum `!v. lookup_var v t = _` (qspec_then `bv` mp_tac) >>
     qpat_x_assum `!p. op_taint tn' _ = _` (qspec_then `bv` mp_tac) >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`,`tn'`] >>
  qpat_x_assum `t = _` (SUBST_ALL_TAC) >>
  fs[] >> rpt strip_tac >> metis_tac[]
QED

Finalise concat_suffix_path_ptr

Theorem concat_suffix_memory_post:
  t = (mstore B (n2w k) u) with vs_inst_idx := ix /\
  u.vs_memory = s.vs_memory /\
  un.t_mem = tn.t_mem DIFF {i | B <= i /\ i < B+32} /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) ==>
  mload B t = n2w k /\
  mem_bytes_at (B+32) k t.vs_memory = mem_bytes_at (B+32) k s.vs_memory /\
  (!i. B <= i /\ i < B+32+k ==> i NOTIN un.t_mem)
Proof
  strip_tac >> gvs[] >>
  conj_tac >-
    (`mload B ((mstore B (n2w k) u) with vs_inst_idx := ix) =
      mload B (mstore B (n2w k) u)` by simp[mload_def] >>
     metis_tac[mload_mstore_same]) >>
  conj_tac >- simp[mstore_mem_bytes_at_disjoint] >>
  simp[] >> rpt strip_tac >>
  Cases_on `i < B+32` >- simp[] >>
  `i NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]
QED

Theorem concat_suffix_frame:
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  t = (mstore B w u) with vs_inst_idx := ix /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
  un.t_mem SUBSET tn.t_mem /\
  MEM binst (fn_insts fn) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\ 32 <= bsz /\
  (!name b k. local_region ce es.scopes s name b k ==>
    B+bsz <= b \/ b+k <= B) ==>
  stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es H un t /\
  ghost_kept ce es sa G tn s H un /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `t = (mstore B w s) with <|vs_vars := t.vs_vars; vs_inst_idx := ix|>` by
    fs[venom_state_component_equality, mstore_def] >>
  `stmt_state_rel ctx fn ce cx es (mstore B w s)` by
    (irule literal_mstore_state_rel >>
     simp[] >> qexistsl_tac [`B`,`binst`,`bsz`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `!x v. not_fresh_at sa x /\ lookup_var x (mstore B w s) = SOME v ==>
    lookup_var x t = SOME v` by
    (simp[lookup_var_def, mstore_def] >> metis_tac[lookup_var_def]) >>
  `stmt_state_rel ctx fn ce cx es t` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`mstore B w s`,`sa`] >> simp[] >> gvs[]) >>
  `ghost_kept ce es sa G tn s H un` by
    (irule ghost_kept_memory_subset >> simp[] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx` by
    fs[venom_state_component_equality, mstore_def] >>
  `stor_taint_ok cx un t` by
    (fs[ghost_inv_def, stor_taint_ok_def] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory` by fs[venom_state_component_equality] >>
  `!name b k. local_region ce es.scopes s name b k ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (rpt strip_tac >>
     `b+k <= B \/ B+32 <= b` by
       (qpat_x_assum `!name b k. local_region _ _ s _ _ _ ==> _` drule >>
        decide_tac) >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `ghost_inv d ce cx es H un t` suffices_by simp[] >>
  irule hash_ghost_inv_region_frame >>
  conj_tac >- (qpat_x_assum `stor_taint_ok _ _ _` mp_tac >>
    qpat_x_assum `t = _ with vs_inst_idx := _` SUBST1_TAC >>
    simp[stor_taint_ok_def]) >>
  qexistsl_tac [`G`,`ctx`,`fn`,`s`,`sa`,`tn`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
