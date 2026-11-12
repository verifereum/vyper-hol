Theory bodyPtrBytestringBuiltinsUintLoop
Ancestors
  bodyPtrBytestringBuiltinsUintFinal bodyPtrBytestringBuiltinsUintZeroResult
  bodyPtrBytestringBuiltinsUintBodyStep bodyPtrBytestringBuiltinsUintBlockInv
  exprSimUint2Str bodyPtrDefs fragGasPathPtr venomState venomExecSemantics
  words list arithmetic codegenRel valueEncoding
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintFrame

Theorem u2s_loop_invariant_ptr:
  !x s str G tn.
  (!bb. MEM bb (u2s_blocks a op (Var p) n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  u2s_digits a b n X x str s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n (LENGTH str) G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  X < dimword(:256) /\ 78 <= n /\ 32 <= buf_size /\
  b+(buf_size+n) < dimword(:256) /\
  LENGTH (num_to_dec_string X)+32 <= type_memory_size (BaseTV (StringT cap)) /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es a G0 tn0 s0 G' tn' /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    lookup_var (u2s_var a 2) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    (!mem'. mem_agree_outside tn'.t_mem t.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) mem') /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0
Proof
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `c = jump_to (u2s_label a (if x = 0 then 4 else 2))
    (update_var (u2s_var a 4) (bool_to_word (x = 0)) s)` >>
  `lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256)` by
    gvs[u2s_digits_def] >>
  `lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then
      `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `c = jump_to (u2s_label a (if x = 0 then 4 else 2))
    (update_var (u2s_var a 4) (bool_to_word (x = 0)) s)` by simp[Abbr `c`] >>
  drule_all u2s_cond_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `u2s_digits a b n X x str c` by metis_tac[] >>
  `c.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
   c.vs_inst_idx = 0 /\ ~c.vs_halted` by
    simp[Abbr `c`, jump_to_def, update_var_def] >>
  Cases_on `x = 0`
  >- suspend "final"
  >> suspend "body"
QED

Resume u2s_loop_invariant_ptr[final]:
  gvs[] >>
  `str = num_to_dec_string X` by gvs[u2s_digits_def] >>
  `u2s_digits a b n X 0 str c` by metis_tac[] >>
  `LENGTH str+32 <= type_memory_size (BaseTV (StringT cap))` by simp[] >>
  `lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then
      `<|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  drule_all u2s_final_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' c 0 gr tr (OK out)` >>
  qexistsl_tac [`gr`, `tr`, `out`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume u2s_loop_invariant_ptr[body]:
  gvs[] >>
  `0 < x /\ x DIV 10 < x` by simp[DIV_LESS] >>
  `LENGTH str < n` by (irule u2s_digits_room >> metis_tac[]) >>
  `n+32 <= buf_size+n` by decide_tac >>
  `lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then
      `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `u2s_digits a b n X x str c` by metis_tac[] >>
  drule_all u2s_body_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' c 0 gb tb (OK outbody)` >>
  `~outbody.vs_halted` by metis_tac[u2s_safe_halted] >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`outbody`, `CHR (48+x MOD 10)::str`, `gb`, `tb`] mp_tac) >>
  simp[ADD1] >> strip_tac >>
  qexistsl_tac [`G''`, `tn''`, `t`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise u2s_loop_invariant_ptr

Theorem u2s_check_exit_invariant_ptr:
  (!bb. MEM bb (u2s_blocks a op (Var p) n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  lookup_var (u2s_var a 0) s = SOME (n2w X) /\
  lookup_var (u2s_var a 1) s = SOME 0w /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n 0 G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  X < dimword(:256) /\ 78 <= n /\ 32 <= buf_size /\
  b+(buf_size+n) < dimword(:256) /\
  LENGTH (num_to_dec_string X)+32 <= type_memory_size (BaseTV (StringT cap)) /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es a G0 tn0 s0 G' tn' /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    lookup_var (u2s_var a 2) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
    val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
      (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
    (!mem'. mem_agree_outside tn'.t_mem t.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) mem') /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qabbrev_tac `c = jump_to (u2s_label a (if X = 0 then 3 else 1))
    (update_var (u2s_var a 3) (bool_to_word (X = 0)) s)` >>
  `lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then
      `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `c = jump_to (u2s_label a (if X = 0 then 3 else 1))
    (update_var (u2s_var a 3) (bool_to_word (X = 0)) s)` by simp[Abbr `c`] >>
  drule_all u2s_check_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `c.vs_current_bb = u2s_label a (if X = 0 then 3 else 1) /\
   c.vs_inst_idx = 0 /\ ~c.vs_halted` by
    simp[Abbr `c`, jump_to_def, update_var_def] >>
  Cases_on `X = 0`
  >- suspend "zero"
  >> suspend "positive"
QED

Resume u2s_check_exit_invariant_ptr[zero]:
  gvs[] >>
  `num_to_dec_string 0 = "0"` by EVAL_TAC >>
  `1 <= n /\ 33 <= type_memory_size (BaseTV (StringT cap))` by gvs[] >>
  `lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then
      `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  drule_all u2s_zero_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' c 0 gr tr (OK out)` >>
  qexistsl_tac [`gr`, `tr`, `out`] >> simp[] >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume u2s_check_exit_invariant_ptr[positive]:
  gvs[] >>
  `u2s_digits a b n X X [] s` by (irule u2s_digits_initial >> simp[]) >>
  `u2s_digits a b n X X [] c` by metis_tac[] >>
  qspecl_then [`X`, `c`, `[]`, `G'`, `tn'`] mp_tac u2s_loop_invariant_ptr >>
  simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' c 0 gr tr (OK out)` >>
  qexistsl_tac [`gr`, `tr`, `out`] >> simp[] >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Finalise u2s_check_exit_invariant_ptr
