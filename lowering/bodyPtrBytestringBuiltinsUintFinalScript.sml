Theory bodyPtrBytestringBuiltinsUintFinal
Ancestors
  bodyPtrBytestringBuiltinsUintExit bodyPtrBytestringBuiltinsUintBodyStep
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintGhost
  bodyPtrBytestringBuiltinsUintBody exprSimUint2Str bodyPtrDefs
  fragGasPathPtr ptrDiscipline venomState venomExecSemantics words list
  codegenRel valueEncoding

Theorem u2s_final_invariant_ptr:
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  u2s_digits a b n X 0 str s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n (LENGTH str) G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  b+(buf_size+n) < dimword(:256) /\ 32 <= buf_size /\
  LENGTH str+32 <= type_memory_size (BaseTV (StringT cap)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es a G0 tn0 s0 G' tn' /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    lookup_var (u2s_var a 2) t = SOME (n2w (b+n-LENGTH str)) /\
    val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
      (b+n-LENGTH str) t.vs_memory /\
    (!mem'. mem_agree_outside tn'.t_mem t.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
        (b+n-LENGTH str) mem') /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  `lookup_var (u2s_var a 1) s = SOME (n2w (LENGTH str))` by gvs[u2s_digits_def] >>
  drule_all u2s_final_counted_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 gr tr (OK out)` >>
  `LENGTH str <= n` by metis_tac[u2s_ptr_state_suffix] >>
  `b <= b+n-LENGTH str /\ b+n-LENGTH str+32 <= b+(buf_size+n)` by decide_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr out` by
    (qpat_assum `out = _` SUBST1_TAC >> irule u2s_final_endpoint_safe >> simp[]) >>
  `!mem'. mem_agree_outside tr.t_mem out.vs_memory mem' ==>
    val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
      (b+n-LENGTH str) mem'` by
    (drule (Q.INST [`s` |-> `s`, `tn` |-> `tn`, `tn'` |-> `tr`]
       u2s_final_endpoint_robust) >> disch_then drule >>
     strip_tac >> qpat_assum `out = _` SUBST1_TAC >> rpt strip_tac >>
     first_x_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >> simp[]) >>
  qexistsl_tac [`gr`, `tr`, `out`] >> simp[] >>
  drule u2s_ptr_state_ambient >> strip_tac >> simp[] >>
  qpat_assum `out = _` SUBST1_TAC >>
  simp[u2s_final_endpoint_memory, jump_to_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- gvs[update_var_def, jump_to_def] >>
  irule uint_digits_header_representation >> metis_tac[]
QED
