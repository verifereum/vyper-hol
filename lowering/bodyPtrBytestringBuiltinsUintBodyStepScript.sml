Theory bodyPtrBytestringBuiltinsUintBodyStep
Ancestors
  bodyPtrBytestringBuiltinsUintBody bodyPtrBytestringBuiltinsUintBlockInv
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintBlocks
  exprSimUint2Str exprLoweringProps localPtrsProps codegenRel contextCodegenRel
  venomState venomExecSemantics ptrDiscipline bodyPtrDefs finite_map words list
  fragGasPathPtr

Theorem u2s_store_tail_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\ i < n /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 4 /\
  lookup_var (u2s_var a 8) s = SOME (n2w (b+n-i)) /\
  lookup_var (u2s_var a 6) s = SOME (n2w (48+x MOD 10)) /\
  op_taint tn (Var (u2s_var a 6)) = {} /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  ptr_covers G tn (u2s_var a 8) s 32 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n (i+1) G' tn' t /\
    t = jump_to (u2s_label a 1)
      (update_var (u2s_var a 1) (n2w i+1w)
        (update_var (u2s_var a 10) (n2w i+1w)
          (update_var (u2s_var a 0) (safe_div (n2w x) 10w)
            (update_var (u2s_var a 9) (safe_div (n2w x) 10w)
              (mstore (b+n-i) (n2w (48+x MOD 10)) s)))))
Proof
  strip_tac >> drule_all u2s_body_store_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ ts (OK stored)` >>
  `?gt tt. gas_path_ptr D 0 ctx fn PG G ts stored 0 gt tt
      (OK (jump_to (u2s_label a 1)
        (update_var (u2s_var a 1) (n2w i+1w)
          (update_var (u2s_var a 10) (n2w i+1w)
            (update_var (u2s_var a 0) (safe_div (n2w x) 10w)
              (update_var (u2s_var a 9) (safe_div (n2w x) 10w) stored)))))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n (i+1) gt tt
      (jump_to (u2s_label a 1)
        (update_var (u2s_var a 1) (n2w i+1w)
          (update_var (u2s_var a 10) (n2w i+1w)
            (update_var (u2s_var a 0) (safe_div (n2w x) 10w)
              (update_var (u2s_var a 9) (safe_div (n2w x) 10w) stored)))))` by
    (irule u2s_tail_invariant_ptr >>
     simp[Abbr `stored`, mstore_def, write_memory_with_expansion_def,
          lookup_var_def] >>
     conj_tac >- (qexists_tac `Var p` >> simp[]) >> gvs[lookup_var_def]) >>
  qexistsl_tac [`gt`, `tt`] >>
  goal_assum (drule_at Any) >>
  gvs[Abbr `stored`, update_var_def, jump_to_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
