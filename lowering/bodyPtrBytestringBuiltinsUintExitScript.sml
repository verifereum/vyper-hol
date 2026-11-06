Theory bodyPtrBytestringBuiltinsUintExit
Ancestors
  bodyPtrBytestringBuiltinsUintBodyStep bodyPtrBytestringBuiltinsUintBody
  bodyPtrBytestringBuiltinsUintBlockInv bodyPtrBytestringBuiltinsUintInvariant
  bodyPtrBytestringBuiltinsUintBlocks bodyPtrBytestringBuiltinsUintArithmetic
  bodyPtrBytestringBuiltinsUintGhost exprSimUint2Str
  fragGasPathPtr fragGasSeqPtr typedCopyPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list rich_list
  codegenRel contextCodegenRel bodyPtrDefs

Theorem u2s_final_address_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
  lookup_var p s = SOME (n2w b) /\ lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  op_taint tn (Var (u2s_var a 1)) = {} /\ i <= n ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (G |+ (u2s_var a 14,(b,sz)) |+ (u2s_var a 15,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 14,{}) |+ (u2s_var a 15,{}))
    (OK (update_var (u2s_var a 15) (n2w (b+n-i))
      (update_var (u2s_var a 14) (n2w (b+n)) s) with vs_inst_idx := 2))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (u2s_var a 14,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 14,{}))
    (OK (update_var (u2s_var a 14) (n2w b + n2w n) s with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+25`, `Var p`, `Lit (n2w n)`] >>
     simp[get_instruction_def, u2s_final_def, u2s_inst_def, eval_operand_def,
          op_taint_def, op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 15,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 15,{}))
    (OK (update_var (u2s_var a 15) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    (irule uint_pointer_sub_site_edge >>
     simp[Abbr `mid`, Abbr `g`, Abbr `t`, update_var_def] >>
     qexistsl_tac [`Var (u2s_var a 1)`, `a.cs_next_id+26`, `u2s_var a 14`] >>
     simp[get_instruction_def, u2s_final_def, u2s_inst_def, eval_operand_def,
          op_taint_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def] >>
     gvs[op_taint_def, lookup_var_def, GSYM word_add_n2w]) >>
  `~(update_var (u2s_var a 15) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx).vs_halted` by
    simp[update_var_def, Abbr `mid`] >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 15,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 15,{}))
    (OK (update_var (u2s_var a 15) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[Abbr `g`, Abbr `t`, Abbr `mid`, update_var_def,
      GSYM word_add_n2w, GSYM n2w_sub] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_final_address_ptr_state:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (G |+ (u2s_var a 14,(b,sz)) |+ (u2s_var a 15,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 14,{}) |+ (u2s_var a 15,{}))
    (update_var (u2s_var a 15) (n2w (b+n-i))
      (update_var (u2s_var a 14) (n2w (b+n)) s) with vs_inst_idx := 2)
Proof
  strip_tac >>
  drule (Q.INST [`k` |-> `14`] u2s_ptr_state_pointer_update) >> simp[] >>
  disch_then (qspecl_then [`n2w (b+n)`, `(b,sz)`] assume_tac) >>
  drule (Q.INST [`k` |-> `15`] u2s_ptr_state_pointer_update) >> simp[] >>
  disch_then (qspecl_then [`n2w (b+n-i)`, `(b,sz)`] mp_tac) >> simp[]
QED

Theorem u2s_final_address_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  b+(buf_size+n) < dimword(:256) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var (u2s_var a 15) (n2w (b+n-i))
        (update_var (u2s_var a 14) (n2w (b+n)) s) with vs_inst_idx := 2)) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b (buf_size+n) n i G' tn'
      (update_var (u2s_var a 15) (n2w (b+n-i))
        (update_var (u2s_var a 14) (n2w (b+n)) s) with vs_inst_idx := 2) /\
    ptr_covers G' tn' (u2s_var a 15)
      (update_var (u2s_var a 15) (n2w (b+n-i))
        (update_var (u2s_var a 14) (n2w (b+n)) s) with vs_inst_idx := 2) buf_size
Proof
  strip_tac >> drule u2s_ptr_state_buffer >> strip_tac >>
  drule u2s_ptr_state_suffix >> strip_tac >>
  `op_taint tn (Var (u2s_var a 1)) = {}` by
    (drule (Q.INST [`k` |-> `1`] u2s_ptr_state_scalar) >> simp[]) >>
  drule_all u2s_final_address_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (drule_all u2s_final_address_ptr_state >> simp[]) >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w] >>
  `b+n-i < dimword(:256)` by decide_tac >> simp[] >> decide_tac
QED

Theorem u2s_ptr_state_clean_store_frame:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= at /\ at+32 <= b+sz /\ at < dimword(:256) /\
  lookup_var dst s = SOME (n2w at) /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G
    (tn with t_mem := tn.t_mem DIFF {j | at <= j /\ j < at+32})
    (mstore at w s)
Proof
  strip_tac >> drule u2s_ptr_state_ambient >> strip_tac >>
  `b <= w2n (n2w at:bytes32) /\ w2n (n2w at:bytes32)+32 <= b+sz` by
    simp[w2n_n2w] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`[]`, `G`, `0`] mp_tac) >> simp[w2n_n2w] >> strip_tac >>
  drule_all clean_mstore_ghost_inv >>
  disch_then (qspecl_then [`[]`, `0`] mp_tac) >>
  simp[w2n_n2w, clean_mstore_taint_state, mstore_ghost_frame] >> strip_tac >>
  drule_all clean_mstore_ghost_kept >>
  disch_then (qspecl_then [`[]`, `0`] mp_tac) >>
  simp[w2n_n2w, clean_mstore_taint_state, mstore_ghost_frame] >> strip_tac >>
  gvs[u2s_ptr_state_def, op_taint_def, lookup_var_def,
      mstore_def, write_memory_with_expansion_def]
QED

Theorem uint_pointer_assign_ghost:
  op_prov G op = SOME site /\ op_taint tn op = {} /\ eval_operand op s = SOME w ==>
  step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s) =
    G |+ (out,site) /\
  step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def]
QED

Theorem uint_pointer_assign_site_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [op] [out]) /\
  eval_operand op s = SOME w /\ op_prov G op = SOME site /\ op_taint tn op = {} ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (out,site))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all uint_pointer_assign_ghost >>
  disch_then (qspecl_then [`out`, `id`, `PG`] strip_assume_tac) >>
  drule_all uint_assign_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> simp[]
QED

Theorem u2s_final_header_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 2 /\
  lookup_var (u2s_var a 15) s = SOME (n2w (b+n-i)) /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  ptr_covers G tn (u2s_var a 15) s 32 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
    (OK (mstore (b+n-i) (n2w i) s with vs_inst_idx := 3)) /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
    (mstore (b+n-i) (n2w i) s with vs_inst_idx := 3)
Proof
  strip_tac >> drule u2s_ptr_state_suffix >> strip_tac >>
  `op_taint tn (Var (u2s_var a 1)) = {}` by
    (drule (Q.INST [`k` |-> `1`] u2s_ptr_state_scalar) >> simp[]) >>
  `b <= b+n-i /\ b+n-i+32 <= b+sz /\ b+n-i < dimword(:256)` by decide_tac >>
  conj_tac
  >- (`gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
        (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
        (OK (mstore (b+n-i) (n2w i) s with vs_inst_idx := 3))` by
       (`3 = SUC s.vs_inst_idx` by simp[] >>
        pop_assum (fn th => once_rewrite_tac[th]) >>
        irule uint_mstore_counted_edge >> simp[] >>
        qexistsl_tac [`a.cs_next_id+27`, `u2s_var a 15`, `Var (u2s_var a 1)`] >>
        simp[get_instruction_def, u2s_final_def, u2s_inst_def, eval_operand_def]) >>
      `~(mstore (b+n-i) (n2w i) s with vs_inst_idx := 3).vs_halted` by
        simp[mstore_def, write_memory_with_expansion_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  pure_rewrite_tac[u2s_ptr_state_index] >>
  irule u2s_ptr_state_clean_store_frame >> simp[] >>
  conj_tac >- (qexists_tac `Var (u2s_var a 1)` >> simp[eval_operand_def]) >>
  metis_tac[]
QED

Theorem u2s_final_result_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 3 /\
  lookup_var (u2s_var a 15) s = SOME w /\
  FLOOKUP G (u2s_var a 15) = SOME site /\ op_taint tn (Var (u2s_var a 15)) = {} /\
  ptr_covers G tn (u2s_var a 15) s buf_size ==>
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
      (OK (update_var (u2s_var a 2) w s with vs_inst_idx := 4))` by
    (`4 = SUC s.vs_inst_idx` by simp[] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule uint_pointer_assign_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+28`, `Var (u2s_var a 15)`] >>
     simp[get_instruction_def, u2s_final_def, u2s_inst_def, eval_operand_def,
          op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ gr tr (OK mid)` >>
  `gas_path_ptr D 0 ctx fn PG gr tr mid 0 gr tr (OK (jump_to (u2s_label a 5) mid))` by
    (irule uint_jump_counted_path >> simp[Abbr `mid`, update_var_def] >>
     qexists_tac `a.cs_next_id+29` >>
     simp[get_instruction_def, u2s_final_def, u2s_inst_def]) >>
  qexistsl_tac [`gr`, `tr`] >> conj_tac
  >- (gvs[Abbr `mid`, update_var_def, jump_to_def] >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac
  >- (irule u2s_ptr_state_jump >> simp[Abbr `gr`, Abbr `tr`] >>
      irule u2s_ptr_state_pointer_update >> simp[]) >>
  gvs[ptr_covers_def, Abbr `gr`, Abbr `tr`, op_taint_def, lookup_var_def,
      update_var_def, jump_to_def, FLOOKUP_UPDATE]
QED

Theorem u2s_final_tail_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  n+32 <= sz /\ b+sz < dimword(:256) /\ 32 <= buf_size /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 2 /\
  lookup_var (u2s_var a 15) s = SOME (n2w (b+n-i)) /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  FLOOKUP G (u2s_var a 15) = SOME site /\ op_taint tn (Var (u2s_var a 15)) = {} /\
  ptr_covers G tn (u2s_var a 15) s buf_size ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i))
        (mstore (b+n-i) (n2w i) s)))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i))
        (mstore (b+n-i) (n2w i) s))) /\
    ptr_covers G' tn' (u2s_var a 2)
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i))
        (mstore (b+n-i) (n2w i) s))) buf_size /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32}
Proof
  strip_tac >>
  `ptr_covers G tn (u2s_var a 15) s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  drule_all u2s_final_header_invariant_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ ts (OK stored)` >>
  `?gr tr. gas_path_ptr D 0 ctx fn PG G ts stored 0 gr tr
      (OK (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i)) stored))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i gr tr
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i)) stored)) /\
    ptr_covers gr tr (u2s_var a 2)
      (jump_to (u2s_label a 5) (update_var (u2s_var a 2) (n2w (b+n-i)) stored)) buf_size /\
    tr.t_mem = ts.t_mem` by
    (irule u2s_final_result_invariant_ptr >>
     simp[Abbr `stored`, Abbr `ts`, mstore_def, write_memory_with_expansion_def,
          lookup_var_def, op_taint_def] >>
     conj_tac >- (gvs[op_taint_def]) >>
     gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  qexistsl_tac [`gr`, `tr`] >>
  gvs[Abbr `stored`, Abbr `ts`, update_var_def, jump_to_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
