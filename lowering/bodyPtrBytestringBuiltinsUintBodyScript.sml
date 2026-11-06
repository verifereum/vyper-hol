Theory bodyPtrBytestringBuiltinsUintBody
Ancestors
  bodyPtrBytestringBuiltinsUintBlockInv bodyPtrBytestringBuiltinsUintInvariant
  bodyPtrBytestringBuiltinsUintBlocks bodyPtrBytestringBuiltinsUintArithmetic
  bodyPtrBytestringBuiltinsUintGhost exprSimUint2Str
  fragGasPathPtr fragGasSeqPtr typedCopyPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list rich_list
  codegenRel contextCodegenRel bodyPtrDefs

Theorem uint_pointer_binop_ghost:
  (opc = ADD \/ opc = SUB) ==>
  step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out w s) =
    set_prov G [out] (first_prov G [left;right]) /\
  step_taint (mk_inst id opc [left;right] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem uint_pointer_add_site_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = SOME site ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (out,site))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (x+y) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all uint_pointer_add_counted_edge >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  simp[uint_pointer_binop_ghost, first_prov_def, set_prov_def]
QED

Theorem uint_pointer_sub_site_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id SUB [Var root;delta] [out]) /\
  lookup_var root s = SOME x /\ eval_operand delta s = SOME (n2w i) /\
  op_taint tn (Var root) = {} /\ op_taint tn delta = {} /\
  FLOOKUP G root = SOME site ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (out,site))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (x-n2w i) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all pointer_sub_counted_edge >>
  disch_then (qspecl_then [`D`, `PG`, `G`] mp_tac) >>
  simp[uint_pointer_binop_ghost, op_prov_def, first_prov_def, set_prov_def]
QED

Theorem u2s_address_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 2 /\
  lookup_var p s = SOME (n2w b) /\ lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  op_taint tn (Var (u2s_var a 1)) = {} /\ i <= n ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (G |+ (u2s_var a 7,(b,sz)) |+ (u2s_var a 8,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}) |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n-i))
      (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (u2s_var a 7,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}))
    (OK (update_var (u2s_var a 7) (n2w b + n2w n) s with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+10`, `Var p`, `Lit (n2w n)`] >>
     simp[get_instruction_def, u2s_body_def, u2s_inst_def, eval_operand_def,
          op_taint_def, op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 8,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    (irule uint_pointer_sub_site_edge >>
     simp[Abbr `mid`, Abbr `g`, Abbr `t`, update_var_def] >>
     qexistsl_tac [`Var (u2s_var a 1)`, `a.cs_next_id+11`, `u2s_var a 7`] >>
     simp[get_instruction_def, u2s_body_def, u2s_inst_def, eval_operand_def,
          op_taint_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def] >>
     gvs[op_taint_def, lookup_var_def, GSYM word_add_n2w]) >>
  `~(update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx).vs_halted` by
    simp[update_var_def, Abbr `mid`] >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 8,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[Abbr `g`, Abbr `t`, Abbr `mid`, update_var_def,
      GSYM word_add_n2w, GSYM n2w_sub] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_address_covers:
  i <= n /\ n+32 <= sz /\ b+sz < dimword(:256) ==>
  ptr_covers (G |+ (u2s_var a 7,(b,sz)) |+ (u2s_var a 8,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}) |+ (u2s_var a 8,{}))
    (u2s_var a 8)
    (update_var (u2s_var a 8) (n2w (b+n-i))
      (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4) 32
Proof
  strip_tac >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w] >>
  `b+n-i < dimword(:256)` by decide_tac >> simp[] >> decide_tac
QED

Theorem u2s_address_ptr_state:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (G |+ (u2s_var a 7,(b,sz)) |+ (u2s_var a 8,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}) |+ (u2s_var a 8,{}))
    (update_var (u2s_var a 8) (n2w (b+n-i))
      (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4)
Proof
  strip_tac >>
  drule (Q.INST [`k` |-> `7`] u2s_ptr_state_pointer_update) >> simp[] >>
  disch_then (qspecl_then [`n2w (b+n)`, `(b,sz)`] assume_tac) >>
  irule u2s_ptr_state_update >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[FLOOKUP_UPDATE, op_taint_def] >>
  qexistsl_tac [`G |+ (u2s_var a 7,(b,sz))`,
    `tn with t_var := tn.t_var |+ (u2s_var a 7,{})`] >>
  simp[FLOOKUP_UPDATE, op_taint_def]
QED

Theorem u2s_digit_prepare_ptr_state:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (DRESTRICT (DRESTRICT G (COMPL {u2s_var a 5})) (COMPL {u2s_var a 6}))
    (tn with t_var := tn.t_var |+ (u2s_var a 5,{}) |+ (u2s_var a 6,{}))
    (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
      (update_var (u2s_var a 5) (safe_mod xw 10w) s) with vs_inst_idx := 2)
Proof
  strip_tac >>
  drule_all u2s_ptr_state_scalar_update >>
  disch_then (qspecl_then [`safe_mod xw 10w`, `5`, `s.vs_inst_idx`] mp_tac) >>
  simp[update_var_def] >> strip_tac >>
  drule_all u2s_ptr_state_scalar_update >>
  disch_then (qspecl_then [`48w + safe_mod xw 10w`, `6`, `2`] mp_tac) >>
  simp[update_var_def]
QED

Theorem u2s_address_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 2 /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  n+32 <= sz /\ b+sz < dimword(:256) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (update_var (u2s_var a 8) (n2w (b+n-i))
        (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4)) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (update_var (u2s_var a 8) (n2w (b+n-i))
        (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4) /\
    ptr_covers G' tn' (u2s_var a 8)
      (update_var (u2s_var a 8) (n2w (b+n-i))
        (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4) 32
Proof
  strip_tac >>
  drule u2s_ptr_state_buffer >> strip_tac >>
  drule u2s_ptr_state_scalar >> disch_then (qspec_then `1` mp_tac) >> simp[] >>
  strip_tac >> drule u2s_ptr_state_suffix >> strip_tac >>
  qexistsl_tac [`G |+ (u2s_var a 7,(b,sz)) |+ (u2s_var a 8,(b,sz))`,
    `tn with t_var := tn.t_var |+ (u2s_var a 7,{}) |+ (u2s_var a 8,{})`] >>
  conj_tac >- (irule u2s_address_counted_ptr >> simp[] >> qexists_tac `p` >> simp[]) >>
  conj_tac >- (irule u2s_address_ptr_state >> simp[]) >>
  irule (SRULE[] u2s_address_covers) >> simp[]
QED

Theorem u2s_digit_prepare_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME xw ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
      (update_var (u2s_var a 5) (safe_mod xw 10w) s) with vs_inst_idx := 2)) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
        (update_var (u2s_var a 5) (safe_mod xw 10w) s) with vs_inst_idx := 2)
Proof
  strip_tac >>
  drule u2s_ptr_state_scalar >> disch_then (qspec_then `0` mp_tac) >> simp[] >>
  strip_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {u2s_var a 5}))
    (COMPL {u2s_var a 6})`,
    `tn with t_var := tn.t_var |+ (u2s_var a 5,{}) |+ (u2s_var a 6,{})`] >>
  conj_tac >- (irule u2s_digit_prepare_counted_ptr >> simp[] >>
    qexistsl_tac [`buf`, `n`] >> simp[]) >>
  drule_all u2s_digit_prepare_ptr_state >>
  disch_then (qspec_then `xw` mp_tac) >> simp[]
QED

Theorem u2s_ptr_state_index[simp]:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn
    (s with vs_inst_idx := idx) <=>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s
Proof
  simp[u2s_ptr_state_def, ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, lookup_var_def] >>
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem u2s_body_store_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\ i < n /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 4 /\
  lookup_var (u2s_var a 8) s = SOME (n2w (b+n-i)) /\
  lookup_var (u2s_var a 6) s = SOME (n2w (48+x MOD 10)) /\
  op_taint tn (Var (u2s_var a 6)) = {} /\
  ptr_covers G tn (u2s_var a 8) s 32 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
    (OK (mstore (b+n-i) (n2w (48+x MOD 10)) s with vs_inst_idx := 5)) /\
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n (i+1) G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
    (mstore (b+n-i) (n2w (48+x MOD 10)) s with vs_inst_idx := 5)
Proof
  strip_tac >>
  `b <= b+n-i /\ b+n-i+32 <= b+sz /\ b+n-i < dimword(:256)` by decide_tac >>
  conj_tac >- (irule u2s_body_store_counted_ptr >> simp[] >>
    qexistsl_tac [`a`, `buf`] >> simp[arithmeticTheory.ADD_COMM]) >>
  pure_rewrite_tac[u2s_ptr_state_index] >> irule u2s_ptr_state_store >> simp[] >>
  conj_tac >- (qexists_tac `Var (u2s_var a 6)` >>
    simp[eval_operand_def, arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (qexists_tac `u2s_var a 8` >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `fn` >> simp[]
QED
