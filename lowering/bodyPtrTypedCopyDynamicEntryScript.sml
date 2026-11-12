(* Compiler-facing entry to the counted dynamic-array copy. *)
Theory bodyPtrTypedCopyDynamicEntry
Ancestors bodyPtrTypedCopyDynamicControl typedDynLoopCode dynCopyCode
  abiBytestringCode bytesCopyCode fragExec loweringStateRelDefs rich_list

Theorem typed_copy_dynamic_entry_counted:
  (!s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too];
     mk_inst (id+2) ISZERO [Var too] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [Var dst;Var len] [];
     mk_inst (id+5) ADD [Var src;Lit 32w] [sp];
     mk_inst (id+6) ADD [Var dst;Lit 32w] [dp]] ++ suffix /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+S) /\ ptr_covers G tn dst s (32+T) /\
  w2n a+32+S < dimword(:256) /\ w2n b+32+T < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  ALL_DISTINCT [len;too;ok;sp;dp] /\
  (!p. MEM p [len;too;ok;sp;dp] ==> src <> p /\ dst <> p) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = LENGTH prefix+7 /\
    ~u.vs_halted /\ lookup_var len u = SOME (n2w n) /\
    FLOOKUP H len = NONE /\ op_taint tf (Var len) = {} /\
    lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
    ptr_covers H tf sp u S /\ ptr_covers H tf dp u T /\
    u.vs_memory = (mstore (w2n b) (n2w n) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. ~MEM p [len;too;ok;sp;dp] ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))) ==>
  !sa s ctx fn src dst a b S T n cap G tn PG D.
  fn_has_code sa (dyn_copy_prefix_state sa (Var dst) (Var src) cap) fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+S) /\ ptr_covers G tn dst s (32+T) /\
  w2n a+32+S < dimword(:256) /\ w2n b+32+T < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w n /\ n <= cap /\ cap < dimword(:256) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = (dyn_copy_prefix_state sa (Var dst) (Var src) cap).cs_current_bb /\
    u.vs_inst_idx = LENGTH (dyn_copy_prefix_state sa (Var dst) (Var src) cap).cs_current_insts /\
    ~u.vs_halted /\
    lookup_var (EL 0 (compiler_var_names sa.cs_next_var 5)) u = SOME (n2w n) /\
    FLOOKUP H (EL 0 (compiler_var_names sa.cs_next_var 5)) = NONE /\
    op_taint tf (Var (EL 0 (compiler_var_names sa.cs_next_var 5))) = {} /\
    lookup_var (EL 3 (compiler_var_names sa.cs_next_var 5)) u = SOME (a+32w) /\
    lookup_var (EL 4 (compiler_var_names sa.cs_next_var 5)) u = SOME (b+32w) /\
    ptr_covers H tf (EL 3 (compiler_var_names sa.cs_next_var 5)) u S /\
    ptr_covers H tf (EL 4 (compiler_var_names sa.cs_next_var 5)) u T /\
    u.vs_memory = (mstore (w2n b) (n2w n) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `fn_has_code sa _ fn`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  gvs[dyn_copy_prefix_state_fields, IS_PREFIX_APPEND] >>
  `!p. MEM p (compiler_var_names sa.cs_next_var 5) ==> ~not_fresh_at sa p` by
    (simp[compiler_var_names_def, listTheory.MEM_GENLIST, not_fresh_at_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `ALL_DISTINCT (compiler_var_names sa.cs_next_var 5)` by
    simp[compiler_var_names_distinct] >>
  `!p. MEM p (compiler_var_names sa.cs_next_var 5) ==> src <> p /\ dst <> p` by
    metis_tac[] >>
  rename1 `ptr_covers G tn src s (sourceSpan+32)` >>
  rename1 `ptr_covers G tn dst s (destSpan+32)` >>
  qsuff_tac `?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    ~u.vs_halted /\ lookup_var (EL 0 (compiler_var_names sa.cs_next_var 5)) u = SOME (n2w n) /\
    FLOOKUP H (EL 0 (compiler_var_names sa.cs_next_var 5)) = NONE /\
    op_taint tf (Var (EL 0 (compiler_var_names sa.cs_next_var 5))) = {} /\
    lookup_var (EL 3 (compiler_var_names sa.cs_next_var 5)) u = SOME (a+32w) /\
    lookup_var (EL 4 (compiler_var_names sa.cs_next_var 5)) u = SOME (b+32w) /\
    ptr_covers H tf (EL 3 (compiler_var_names sa.cs_next_var 5)) u sourceSpan /\
    ptr_covers H tf (EL 4 (compiler_var_names sa.cs_next_var 5)) u destSpan /\
    u.vs_memory = (mstore (w2n b) (n2w n) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. ~MEM p (compiler_var_names sa.cs_next_var 5) ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))`
  >- (strip_tac >> qexistsl_tac [`H`, `tf`, `u`] >>
      qpat_x_assum `!s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D. _` kall_tac >>
      gvs[compiler_var_names_five, dyn_copy_prefix_insts_def] >>
      metis_tac[]) >>
  qpat_x_assum `!s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D. _`
    (qspec_then `s` mp_tac) >>
  simp[compiler_var_names_five] >> disch_then irule >>
  fs[compiler_var_names_five] >>
  qexistsl_tac [`cap`, `dst`, `sa.cs_next_id`, `src`, `l`] >>
  simp[dyn_copy_prefix_insts_def, compiler_var_names_five] >>
  first_assum ACCEPT_TAC
QED
