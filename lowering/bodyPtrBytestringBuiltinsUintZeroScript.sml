Theory bodyPtrBytestringBuiltinsUintZero
Ancestors
  bodyPtrBytestringBuiltinsUintExit bodyPtrBytestringBuiltinsUintBody
  bodyPtrBytestringBuiltinsUintBlockInv bodyPtrBytestringBuiltinsUintBodyStep
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintBlocks
  exprSimUint2Str fragGasPathPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list rich_list
  codegenRel contextCodegenRel bodyPtrDefs

Theorem u2s_zero_address_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\
  n+32 <= sz /\ b+sz < dimword(:256) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (G |+ (u2s_var a 11,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 11,{}))
    (OK (update_var (u2s_var a 11) (n2w (b+n)) s with vs_inst_idx := 1)) /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (G |+ (u2s_var a 11,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 11,{}))
    (update_var (u2s_var a 11) (n2w (b+n)) s with vs_inst_idx := 1) /\
  ptr_covers (G |+ (u2s_var a 11,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 11,{})) (u2s_var a 11)
    (update_var (u2s_var a 11) (n2w (b+n)) s with vs_inst_idx := 1) 32
Proof
  strip_tac >> drule u2s_ptr_state_buffer >> strip_tac >>
  conj_tac
  >- (`gas_path_ptr_edge D 0 ctx fn PG G tn s 0
        (G |+ (u2s_var a 11,(b,sz)))
        (tn with t_var := tn.t_var |+ (u2s_var a 11,{}))
        (OK (update_var (u2s_var a 11) (n2w (b+n)) s with vs_inst_idx := 1))` by
       (`1 = SUC s.vs_inst_idx` by simp[] >>
        pop_assum (fn th => once_rewrite_tac[th]) >>
        rewrite_tac[GSYM word_add_n2w] >> irule uint_pointer_add_site_edge >> simp[] >>
        qexistsl_tac [`a.cs_next_id+18`, `Var p`, `Lit (n2w n)`] >>
        simp[get_instruction_def, u2s_zero_def, u2s_inst_def,
             eval_operand_def, op_taint_def, op_prov_def]) >>
      `~(update_var (u2s_var a 11) (n2w (b+n)) s with vs_inst_idx := 1).vs_halted`
        by simp[update_var_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac
  >- (pure_rewrite_tac[u2s_ptr_state_index] >>
      irule u2s_ptr_state_pointer_update >> simp[]) >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w] >>
  `b+n < dimword(:256)` by decide_tac >> simp[] >> decide_tac
QED

Theorem u2s_zero_digit_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 1 /\
  lookup_var (u2s_var a 11) s = SOME (n2w (b+n)) /\
  ptr_covers G tn (u2s_var a 11) s 32 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
    (OK (mstore (b+n) 48w s with vs_inst_idx := 2)) /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G
    (tn with t_mem := tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
    (mstore (b+n) 48w s with vs_inst_idx := 2)
Proof
  strip_tac >>
  `b <= b+n /\ b+n+32 <= b+sz /\ b+n < dimword(:256)` by decide_tac >>
  conj_tac
  >- (`gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
        (tn with t_mem := tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
        (OK (mstore (b+n) 48w s with vs_inst_idx := 2))` by
       (`2 = SUC s.vs_inst_idx` by simp[] >>
        pop_assum (fn th => once_rewrite_tac[th]) >>
        irule uint_mstore_counted_edge >> simp[] >>
        qexistsl_tac [`a.cs_next_id+19`, `u2s_var a 11`, `Lit 48w`] >>
        simp[get_instruction_def, u2s_zero_def, u2s_inst_def,
             eval_operand_def, op_taint_def]) >>
      `~(mstore (b+n) 48w s with vs_inst_idx := 2).vs_halted` by
        simp[mstore_def, write_memory_with_expansion_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  pure_rewrite_tac[u2s_ptr_state_index] >>
  irule u2s_ptr_state_clean_store_frame >> simp[] >>
  conj_tac >- (qexists_tac `Lit 48w` >> simp[eval_operand_def, op_taint_def]) >>
  metis_tac[]
QED

Theorem u2s_zero_header_address_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 2 /\
  lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\ 1 <= n ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (G |+ (u2s_var a 12,(b,sz)) |+ (u2s_var a 13,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 12,{}) |+ (u2s_var a 13,{}))
    (OK (update_var (u2s_var a 13) (n2w (b+n-1))
      (update_var (u2s_var a 12) (n2w (b+n)) s) with vs_inst_idx := 4))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (u2s_var a 12,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 12,{}))
    (OK (update_var (u2s_var a 12) (n2w b + n2w n) s with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+20`, `Var p`, `Lit (n2w n)`] >>
     simp[get_instruction_def, u2s_zero_def, u2s_inst_def, eval_operand_def,
          op_taint_def, op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 13,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 13,{}))
    (OK (update_var (u2s_var a 13) (n2w (b+n)-1w) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    (irule uint_pointer_sub_site_edge >>
     simp[Abbr `mid`, Abbr `g`, Abbr `t`, update_var_def] >>
     qexistsl_tac [`Lit 1w`, `a.cs_next_id+21`, `u2s_var a 12`] >>
     simp[get_instruction_def, u2s_zero_def, u2s_inst_def, eval_operand_def,
          op_taint_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def,
          GSYM word_add_n2w]) >>
  `~(update_var (u2s_var a 13) (n2w (b+n)-1w) mid with
      vs_inst_idx := SUC mid.vs_inst_idx).vs_halted` by
    simp[update_var_def, Abbr `mid`] >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 13,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 13,{}))
    (OK (update_var (u2s_var a 13) (n2w (b+n)-1w) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[Abbr `g`, Abbr `t`, Abbr `mid`, update_var_def,
      GSYM word_add_n2w, GSYM n2w_sub] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_zero_header_address_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 2 /\
  1 <= n /\ b+sz < dimword(:256) /\ buf_size+n <= sz ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var (u2s_var a 13) (n2w (b+n-1))
        (update_var (u2s_var a 12) (n2w (b+n)) s) with vs_inst_idx := 4)) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (update_var (u2s_var a 13) (n2w (b+n-1))
        (update_var (u2s_var a 12) (n2w (b+n)) s) with vs_inst_idx := 4) /\
    ptr_covers G' tn' (u2s_var a 13)
      (update_var (u2s_var a 13) (n2w (b+n-1))
        (update_var (u2s_var a 12) (n2w (b+n)) s) with vs_inst_idx := 4) buf_size /\
    FLOOKUP G' (u2s_var a 13) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 13)) = {} /\ tn'.t_mem = tn.t_mem
Proof
  strip_tac >> drule u2s_ptr_state_buffer >> strip_tac >>
  drule_all u2s_zero_header_address_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (pure_rewrite_tac[u2s_ptr_state_index] >>
      drule (Q.INST [`k` |-> `12`] u2s_ptr_state_pointer_update) >> simp[] >>
      disch_then (qspecl_then [`n2w (b+n)`, `(b,sz)`] assume_tac) >>
      drule (Q.INST [`k` |-> `13`] u2s_ptr_state_pointer_update) >> simp[] >>
      disch_then (qspecl_then [`n2w (b+n-1)`, `(b,sz)`] mp_tac) >> simp[]) >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w] >>
  `b+n-1 < dimword(:256)` by decide_tac >> simp[] >> decide_tac
QED

Theorem u2s_zero_header_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  1 <= n /\ n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 4 /\
  lookup_var (u2s_var a 13) s = SOME (n2w (b+n-1)) /\
  ptr_covers G tn (u2s_var a 13) s 32 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-1 <= j /\ j < b+n-1+32})
    (OK (mstore (b+n-1) 1w s with vs_inst_idx := 5)) /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-1 <= j /\ j < b+n-1+32})
    (mstore (b+n-1) 1w s with vs_inst_idx := 5)
Proof
  strip_tac >>
  `b <= b+n-1 /\ b+n-1+32 <= b+sz /\ b+n-1 < dimword(:256)` by decide_tac >>
  conj_tac
  >- (`gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
        (tn with t_mem := tn.t_mem DIFF {j | b+n-1 <= j /\ j < b+n-1+32})
        (OK (mstore (b+n-1) 1w s with vs_inst_idx := 5))` by
       (`5 = SUC s.vs_inst_idx` by simp[] >>
        pop_assum (fn th => once_rewrite_tac[th]) >>
        irule uint_mstore_counted_edge >> simp[] >>
        qexistsl_tac [`a.cs_next_id+22`, `u2s_var a 13`, `Lit 1w`] >>
        simp[get_instruction_def, u2s_zero_def, u2s_inst_def,
             eval_operand_def, op_taint_def]) >>
      `~(mstore (b+n-1) 1w s with vs_inst_idx := 5).vs_halted` by
        simp[mstore_def, write_memory_with_expansion_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  pure_rewrite_tac[u2s_ptr_state_index] >>
  irule u2s_ptr_state_clean_store_frame >> simp[] >>
  conj_tac >- (qexists_tac `Lit 1w` >> simp[eval_operand_def, op_taint_def]) >>
  metis_tac[]
QED

Theorem u2s_zero_result_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 5 /\
  lookup_var (u2s_var a 13) s = SOME w /\
  FLOOKUP G (u2s_var a 13) = SOME site /\ op_taint tn (Var (u2s_var a 13)) = {} /\
  ptr_covers G tn (u2s_var a 13) s buf_size ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (u2s_label a 5) (update_var (u2s_var a 2) w s))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) w s)) /\
    ptr_covers G' tn' (u2s_var a 2)
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) w s)) buf_size /\
    tn'.t_mem = tn.t_mem
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (G |+ (u2s_var a 2,site)) (tn with t_var := tn.t_var |+ (u2s_var a 2,{}))
      (OK (update_var (u2s_var a 2) w s with vs_inst_idx := 6))` by
    (`6 = SUC s.vs_inst_idx` by simp[] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule uint_pointer_assign_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+23`, `Var (u2s_var a 13)`] >>
     simp[get_instruction_def, u2s_zero_def, u2s_inst_def, eval_operand_def,
          op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ gr tr (OK mid)` >>
  `gas_path_ptr D 0 ctx fn PG gr tr mid 0 gr tr (OK (jump_to (u2s_label a 5) mid))` by
    (irule uint_jump_counted_path >> simp[Abbr `mid`, update_var_def] >>
     qexists_tac `a.cs_next_id+24` >>
     simp[get_instruction_def, u2s_zero_def, u2s_inst_def]) >>
  qexistsl_tac [`gr`, `tr`] >> conj_tac
  >- (gvs[Abbr `mid`, update_var_def, jump_to_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac
  >- (irule u2s_ptr_state_jump >> simp[Abbr `gr`, Abbr `tr`] >>
      irule u2s_ptr_state_pointer_update >> simp[]) >>
  gvs[ptr_covers_def, Abbr `gr`, Abbr `tr`, op_taint_def, lookup_var_def,
      update_var_def, jump_to_def, FLOOKUP_UPDATE]
QED

Theorem u2s_zero_tail_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  1 <= n /\ n+32 <= sz /\ b+sz < dimword(:256) /\ 32 <= buf_size /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 4 /\
  lookup_var (u2s_var a 13) s = SOME (n2w (b+n-1)) /\
  FLOOKUP G (u2s_var a 13) = SOME site /\ op_taint tn (Var (u2s_var a 13)) = {} /\
  ptr_covers G tn (u2s_var a 13) s buf_size ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1))
        (mstore (b+n-1) 1w s)))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1))
        (mstore (b+n-1) 1w s))) /\
    ptr_covers G' tn' (u2s_var a 2)
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1))
        (mstore (b+n-1) 1w s))) buf_size /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n-1 <= j /\ j < b+n-1+32}
Proof
  strip_tac >>
  `ptr_covers G tn (u2s_var a 13) s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  drule_all u2s_zero_header_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ ts (OK stored)` >>
  `?gr tr. gas_path_ptr D 0 ctx fn PG G ts stored 0 gr tr
      (OK (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1)) stored))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i gr tr
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1)) stored)) /\
    ptr_covers gr tr (u2s_var a 2)
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1)) stored)) buf_size /\
    tr.t_mem = ts.t_mem` by
    (irule u2s_zero_result_invariant_ptr >>
     simp[Abbr `stored`, Abbr `ts`, mstore_def, write_memory_with_expansion_def,
          lookup_var_def, op_taint_def] >>
     conj_tac >- (gvs[op_taint_def]) >>
     gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  qexistsl_tac [`gr`, `tr`] >>
  gvs[Abbr `stored`, Abbr `ts`, update_var_def, jump_to_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_zero_prefix_invariant_ptr:
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn' t /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr t /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32} /\
    t = (mstore (b+n) 48w (update_var (u2s_var a 11) (n2w (b+n)) s)
      with vs_inst_idx := 2)
Proof
  strip_tac >> drule_all u2s_zero_address_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ ga ta (OK addr)` >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr addr` by
    (simp[Abbr `addr`] >> irule u2s_safe_index >> irule u2s_safe_update >> simp[]) >>
  drule u2s_safe_store_frame >> strip_tac >>
  `lookup_var (u2s_var a 11) addr = SOME (n2w (b+n)) /\
   addr.vs_current_bb = u2s_label a 3 /\ addr.vs_inst_idx = 1 /\ ~addr.vs_halted` by
    simp[Abbr `addr`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  drule_all u2s_zero_digit_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ ga ta addr _ _ ts (OK stored)` >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr stored` by
    (simp[Abbr `stored`] >> irule u2s_safe_index >>
     irule u2s_safe_mstore >> simp[]) >>
  qexistsl_tac [`ga`, `ts`, `stored`] >> simp[Abbr `ts`, Abbr `ta`] >>
  `stored = (mstore (b+n) 48w (update_var (u2s_var a 11) (n2w (b+n)) s)
    with vs_inst_idx := 2)` by
    simp[Abbr `stored`, Abbr `addr`, mstore_def, write_memory_with_expansion_def,
         update_var_def] >>
  gvs[] >> irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem u2s_zero_suffix_invariant_ptr:
  u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr s /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  b+(buf_size+n) < dimword(:256) /\ 32 <= buf_size /\ 1 <= n /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 2 ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G' tn' t /\
    ptr_covers G' tn' (u2s_var a 2) t buf_size /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n-1 <= j /\ j < b+n-1+32} /\
    t = jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-1))
      (mstore (b+n-1) 1w
        (update_var (u2s_var a 13) (n2w (b+n-1))
          (update_var (u2s_var a 12) (n2w (b+n)) s))))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`sz` |-> `buf_size+n`]
    u2s_zero_header_address_invariant_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ ga ta (OK addr)` >>
  `u2s_safe ctx fn cenv cx es a (Var p) b (buf_size+n) inst sr addr` by
    (simp[Abbr `addr`] >> irule u2s_safe_index >>
     ntac 2 (irule u2s_safe_update >> simp[])) >>
  drule u2s_safe_store_frame >> strip_tac >>
  `lookup_var (u2s_var a 13) addr = SOME (n2w (b+n-1)) /\
   addr.vs_current_bb = u2s_label a 3 /\ addr.vs_inst_idx = 4 /\
   ~addr.vs_halted /\ n+32 <= buf_size+n` by
    simp[Abbr `addr`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i ga ta addr /\
   ptr_covers ga ta (u2s_var a 13) addr buf_size` by simp[Abbr `addr`] >>
  drule_all u2s_zero_tail_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_rename_tac `gas_path_ptr _ _ _ _ _ ga ta addr _ gr tr _` >>
  qexistsl_tac [`gr`, `tr`] >> goal_assum (drule_at Any) >>
  gvs[Abbr `addr`, update_var_def, jump_to_def,
      mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ gr tr _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  goal_assum (drule_at Any) >> simp[]
QED
