Theory bodyPtrBytestringBuiltinsUint2Str
Ancestors
  bodyPtrBytestringBuiltinsUintLoop bodyPtrBytestringBuiltinsUintBlockInv
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintFrame
  exprSimUint2Str bodyPtrDefs fragGasPathPtr venomState venomExecSemantics
  words list arithmetic codegenRel valueEncoding

Theorem u2s_setup_exit_invariant_ptr:
  (!bb. MEM bb (u2s_blocks a op (Var p) n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = a.cs_current_bb /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = a.cs_current_insts ++ u2s_setup a op (Var p) /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,buf_size+n) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {} /\ not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  eval_operand op s = SOME (n2w X) /\ (!k. op <> Var (u2s_var a k)) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\
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
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `entry = jump_to (u2s_label a 0)
    (update_var (u2s_var a 2) (n2w b)
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w X) s)))` >>
  `entry = jump_to (u2s_label a 0)
    (update_var (u2s_var a 2) (n2w b)
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w X) s)))` by
    simp[Abbr `entry`] >>
  drule_all u2s_setup_invariant_ptr >>
  disch_then (qspecl_then [`n`, `PG`, `D`] strip_assume_tac) >>
  `entry.vs_current_bb = u2s_label a 0 /\ entry.vs_inst_idx = 0 /\
   ~entry.vs_halted /\ lookup_var (u2s_var a 0) entry = SOME (n2w X) /\
   lookup_var (u2s_var a 1) entry = SOME 0w` by
    simp[Abbr `entry`, jump_to_def, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all u2s_check_exit_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G''`, `tn''`, `t`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  metis_tac[u2s_safe_halted]
QED
