Theory bodyPtrBytestringBuiltinsConcatDispatch
Ancestors
  bodyPtrBytestringBuiltinsConcatEndpoint bodyPtrBytestringBuiltinsConcatFixed
  bodyPtrBytestringBuiltinsConcatLookup bodyPtrBytestringBuiltinsScratchSeparation
  bodyPtrDefs compileEnv exprLoweringProps

Theorem concat_fixed_arm_endpoint:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var off] [tmp]) /\
  get_instruction bb (s.vs_inst_idx+1) =
    SOME (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) /\
  get_instruction bb (s.vs_inst_idx+2) =
    SOME (mk_inst (id+2) MSTORE [Var dst; value] []) /\
  get_instruction bb (s.vs_inst_idx+3) =
    SOME (mk_inst (id+3) ADD [Var tmp; Lit (n2w (LENGTH bs))] [next]) /\
  get_instruction bb (s.vs_inst_idx+4) =
    SOME (mk_inst (id+4) MSTORE [Var off; Var next] []) /\
  lookup_var off s = SOME b /\ lookup_var root s = SOME a /\
  ptr_covers G tn off s 32 /\ ptr_covers G tn root s cap /\
  mload (w2n b) s = n2w k /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a <= i /\ i < w2n a+k ==> i NOTIN tn.t_mem) /\
  k+32 <= cap /\ w2n a+k < dimword(:256) /\ LENGTH bs <= 32 /\
  (w2n a+(k+LENGTH bs) <= w2n b \/ w2n b+32 <= w2n a) /\
  root <> tmp /\ root <> dst /\ root <> next /\ tmp <> dst /\
  off <> tmp /\ off <> dst /\ off <> next /\ dst <> next /\
  (!q. value = Var q ==> q <> tmp /\ q <> dst) /\
  eval_operand value s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
  op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> x <> tmp /\ x <> dst /\ x <> next) /\
  (!name lb len. local_region cenv es.scopes s name lb len ==>
    w2n a+cap <= lb \/ lb+len <= w2n a) /\
  (!name lb len. local_region cenv es.scopes s name lb len ==>
    w2n b+32 <= lb \/ lb+len <= w2n b) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
    mem_bytes_at (w2n a) (k+LENGTH bs) t.vs_memory =
      mem_bytes_at (w2n a) k s.vs_memory ++ bs /\
    mload (w2n b) t = n2w (k+LENGTH bs) /\
    ptr_covers H tm root t cap /\ ptr_covers H tm off t 32 /\
    t.vs_inst_idx = s.vs_inst_idx+5 /\
    t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
    (!i. w2n a <= i /\ i < w2n a+k+LENGTH bs ==> i NOTIN tm.t_mem) /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tm.t_mem) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all concat_fixed_arm_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `!name lb len i. local_region cenv es.scopes s name lb len /\
    lb <= i /\ i < lb+len ==>
    i NOTIN ({j | w2n a+k <= j /\ j < w2n a+k+32} UNION
             {j | w2n b <= j /\ j < w2n b+32})` by
    (match_mp_tac (Q.INST [`sz` |-> `32`, `cap` |-> `cap`]
      scratch_two_windows_separated) >>
     asm_rewrite_tac[] >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule concat_scratch_semantic_endpoint >> simp[] >>
     qexistsl_tac [`s`, `st`,
       `{j | w2n a+k <= j /\ j < w2n a+k+32} UNION
        {j | w2n b <= j /\ j < w2n b+32}`] >> simp[] >> gvs[]) >>
  `ghost_inv d cenv cx es Gf tnf t` by
    (irule concat_scratch_ghost_endpoint >>
     qpat_assum `stmt_state_rel _ _ _ _ _ s`
       (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [
       `{j | w2n a+k <= j /\ j < w2n a+k+32} UNION
        {j | w2n b <= j /\ j < w2n b+32}`, `tn`, `st`, `G`] >> simp[] >> gvs[]) >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[]
QED

Theorem concat_bytes_arm_endpoint:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var input] [len]) /\
  get_instruction bb (s.vs_inst_idx+1) =
    SOME (mk_inst (id+1) ADD [Var input; Lit 32w] [src]) /\
  get_instruction bb (s.vs_inst_idx+2) =
    SOME (mk_inst (id+2) MLOAD [Var off] [offset]) /\
  get_instruction bb (s.vs_inst_idx+3) =
    SOME (mk_inst (id+3) ADD [Var root; Var offset] [dst]) /\
  get_instruction bb (s.vs_inst_idx+4) =
    SOME (mk_inst (id+4) MCOPY [Var dst;Var src;Var len] []) /\
  get_instruction bb (s.vs_inst_idx+5) =
    SOME (mk_inst (id+5) ADD [Var offset;Var len] [next]) /\
  get_instruction bb (s.vs_inst_idx+6) =
    SOME (mk_inst (id+6) MSTORE [Var off;Var next] []) /\
  lookup_var input s = SOME b /\ lookup_var root s = SOME a /\
  lookup_var off s = SOME c /\
  ptr_covers G tn input s source_cap /\ ptr_covers G tn input s 32 /\
  ptr_covers G tn root s cap /\ ptr_covers G tn off s 32 /\
  mload (w2n b) s = n2w (LENGTH bs) /\ mload (w2n c) s = n2w k /\
  mem_bytes_at (w2n b+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. (w2n b <= i /\ i < w2n b+32+LENGTH bs) \/
       (w2n c <= i /\ i < w2n c+32) \/
       (w2n a <= i /\ i < w2n a+k) ==> i NOTIN tn.t_mem) /\
  32+LENGTH bs <= source_cap /\ w2n b+32 < dimword(:256) /\
  k+LENGTH bs <= cap /\ w2n a+k < dimword(:256) /\
  LENGTH bs < dimword(:256) /\
  (w2n a+(k+LENGTH bs) <= w2n c \/ w2n c+32 <= w2n a) /\
  ALL_DISTINCT [len;src;offset;dst;next] /\
  (~MEM root [len;src;offset;dst;next]) /\
  (~MEM off [len;src;offset;dst;next]) /\ input <> len /\
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> ~MEM x [len;src;offset;dst;next]) /\
  (!name lb size. local_region cenv es.scopes s name lb size ==>
    w2n a+cap <= lb \/ lb+size <= w2n a) /\
  (!name lb size. local_region cenv es.scopes s name lb size ==>
    w2n c+32 <= lb \/ lb+size <= w2n c) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
    mem_bytes_at (w2n a) (k+LENGTH bs) t.vs_memory =
      mem_bytes_at (w2n a) k s.vs_memory ++ bs /\
    mload (w2n c) t = n2w (k+LENGTH bs) /\
    ptr_covers H tm root t cap /\ ptr_covers H tm off t 32 /\
    t.vs_inst_idx = s.vs_inst_idx+7 /\
    t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
    (!i. w2n a <= i /\ i < w2n a+k+LENGTH bs ==> i NOTIN tm.t_mem) /\
    (!i. w2n c <= i /\ i < w2n c+32 ==> i NOTIN tm.t_mem) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bodyPtrBytestringBuiltinsConcatBytesTheory.concat_bytes_arm_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `!name lb size i. local_region cenv es.scopes s name lb size /\
    lb <= i /\ i < lb+size ==>
    i NOTIN ({j | w2n a+k <= j /\ j < w2n a+k+LENGTH bs} UNION
             {j | w2n c <= j /\ j < w2n c+32})` by
    (match_mp_tac (Q.INST [`sz` |-> `32`] scratch_two_windows_separated) >>
     asm_rewrite_tac[] >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule concat_scratch_semantic_endpoint >> simp[] >>
     qexistsl_tac [`s`, `st`,
       `{j | w2n a+k <= j /\ j < w2n a+k+LENGTH bs} UNION
        {j | w2n c <= j /\ j < w2n c+32}`] >> simp[] >> gvs[]) >>
  `ghost_inv d cenv cx es Gf tnf t` by
    (irule concat_scratch_ghost_endpoint >>
     qpat_assum `stmt_state_rel _ _ _ _ _ s`
       (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [
       `{j | w2n a+k <= j /\ j < w2n a+k+LENGTH bs} UNION
        {j | w2n c <= j /\ j < w2n c+32}`, `tn`, `st`, `G`] >> simp[] >> gvs[]) >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[]
QED
