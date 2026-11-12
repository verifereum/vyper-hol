Theory bodyPtrBytestringBuiltinsUintZeroResult
Ancestors
  bodyPtrBytestringBuiltinsUintZero bodyPtrBytestringBuiltinsUintInvariant
  bodyPtrBytestringBuiltinsUintBody bodyPtrBytestringBuiltinsUintBlockInv
  bodyPtrBytestringBuiltinsUintGhost
  exprSimUint2Str fragGasPathPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list rich_list
  codegenRel contextCodegenRel bodyPtrDefs

Theorem u2s_zero_counted_invariant_ptr:
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  b+(buf_size+n) < dimword(:256) /\ 32 <= buf_size /\ 1 <= n /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G' tn' t /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    tn'.t_mem = (tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
      DIFF {j | b+n-1 <= j /\ j < b+n-1+32} /\
    t = jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1))
      (mstore (b+n-1) 1w
        (update_var (u2s_var a 13) (n2w (b+n-1))
          (update_var (u2s_var a 12) (n2w (b+n))
            (mstore (b+n) 48w (update_var (u2s_var a 11) (n2w (b+n)) s))))))
Proof
  strip_tac >> `n+32 <= buf_size+n` by decide_tac >>
  drule_all u2s_zero_prefix_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_rename_tac `gas_path_ptr _ _ _ _ _ G tn s _ gp tp (OK prefix)` >>
  `prefix.vs_current_bb = u2s_label a 3 /\ prefix.vs_inst_idx = 2 /\
   ~prefix.vs_halted` by
    simp[update_var_def, mstore_def, write_memory_with_expansion_def] >>
  drule_all u2s_zero_suffix_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_rename_tac `gas_path_ptr _ _ _ _ _ gp tp prefix _ gr tr (OK out)` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 gr tr (OK out)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)) >>
  qexistsl_tac [`gr`, `tr`, `out`] >>
  simp[] >> qabbrev_tac `memst = mstore (b+n) 48w (update_var (u2s_var a 11) (n2w (b+n)) s)` >>
  simp[update_var_def, mstore_def, write_memory_with_expansion_def, jump_to_def]
QED

Theorem u2s_zero_endpoint_representation:
  1 <= n ==>
  val_in_memory ty (StringV "0") (b+n-1)
    (jump_to lbl (update_var (u2s_var a 2) (n2w (b+n-1))
      (mstore (b+n-1) 1w
        (update_var (u2s_var a 13) (n2w (b+n-1))
          (update_var (u2s_var a 12) v
            (mstore (b+n) 48w (update_var (u2s_var a 11) v s))))))).vs_memory
Proof
  strip_tac >>
  mp_tac (Q.GENL [`s1`, `s2`, `s3`, `s4`, `s5`, `t`] u2s_zero_encoding) >>
  simp[jump_to_def]
QED

Theorem u2s_zero_endpoint_safe:
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr s /\
  local_ptrs_reserved cenv a /\ not_fresh_at a p /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ n+32 <= sz ==>
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr
    (jump_to lbl (update_var (u2s_var a 2) (n2w (b+n-1))
      (mstore (b+n-1) 1w
        (update_var (u2s_var a 13) (n2w (b+n-1))
          (update_var (u2s_var a 12) v
            (mstore (b+n) 48w (update_var (u2s_var a 11) v s)))))))
Proof
  strip_tac >> irule u2s_safe_jump >>
  mp_tac (Q.GENL [`s1`, `s2`, `s3`, `s4`, `s5`, `t`]
    (Q.INST [`buf` |-> `Var p`, `s0` |-> `sr`] u2s_zero_safe)) >> simp[]
QED

Theorem u2s_zero_invariant_ptr:
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  b+(buf_size+n) < dimword(:256) /\ 32 <= buf_size /\ 1 <= n /\
  33 <= type_memory_size (BaseTV (StringT cap)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es a G0 tn0 s0 G' tn' /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    lookup_var (u2s_var a 2) t = SOME (n2w (b+n-1)) /\
    val_in_memory (BaseTV (StringT cap)) (StringV "0") (b+n-1) t.vs_memory /\
    (!mem'. mem_agree_outside tn'.t_mem t.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT cap)) (StringV "0") (b+n-1) mem') /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0
Proof
  strip_tac >> drule_all u2s_zero_counted_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 gr tr (OK out)` >>
  `u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr out` by
    (qpat_assum `out = _` SUBST1_TAC >> irule u2s_zero_endpoint_safe >> simp[]) >>
  `!mem'. mem_agree_outside tr.t_mem out.vs_memory mem' ==>
    val_in_memory (BaseTV (StringT cap)) (StringV "0") (b+n-1) mem'` by
    (rpt strip_tac >> irule uint_string_clean_robust >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (rpt strip_tac >> simp[] >> decide_tac) >>
     qpat_assum `out = _` SUBST1_TAC >>
     irule u2s_zero_endpoint_representation >> simp[]) >>
  qexistsl_tac [`gr`, `tr`, `out`] >> simp[] >>
  qpat_assum `u2s_ptr_state _ _ _ _ _ _ _ _ _ _ _ _ _ gr tr out`
    (mp_then Any strip_assume_tac u2s_ptr_state_ambient) >>
  conj_tac >- metis_tac[] >> simp[] >>
  conj_tac
  >- (qpat_assum `out = _` SUBST1_TAC >>
      simp[jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (qpat_assum `out = _` SUBST1_TAC >>
      irule u2s_zero_endpoint_representation >> simp[]) >>
  qpat_assum `out = _` SUBST1_TAC >> simp[jump_to_def]
QED
