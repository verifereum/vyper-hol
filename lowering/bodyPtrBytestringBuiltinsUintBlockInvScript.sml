Theory bodyPtrBytestringBuiltinsUintBlockInv
Ancestors
  bodyPtrBytestringBuiltinsUintInvariant bodyPtrBytestringBuiltinsUintBlocks
  bodyPtrBytestringBuiltinsUintGhost
  exprSimUint2Str ptrDiscipline venomState finite_map words
  venomExecSemantics codegenRel contextCodegenRel venomInst list rich_list

Theorem u2s_ptr_state_scalar_update:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (update_var (u2s_var a k) w s with vs_inst_idx := idx)
Proof
  strip_tac >> irule u2s_ptr_state_update >>
  simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`G`, `tn`] >> simp[]
QED

Theorem u2s_check_state_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (jump_to (u2s_label a (if x = 0 then 3 else 1))
      (update_var (u2s_var a 3) (bool_to_word (x = 0)) s))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (jump_to (u2s_label a (if x = 0 then 3 else 1))
        (update_var (u2s_var a 3) (bool_to_word (x = 0)) s))
Proof
  strip_tac >>
  `FLOOKUP G (u2s_var a 0) = NONE /\ op_taint tn (Var (u2s_var a 0)) = {}` by
    (drule u2s_ptr_state_scalar >> simp[] >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {u2s_var a 3})`,
    `tn with t_var := tn.t_var |+ (u2s_var a 3,{})`] >>
  conj_tac >- (irule u2s_check_counted_ptr >> simp[]) >>
  drule_all u2s_ptr_state_scalar_update >>
  disch_then (qspecl_then [`bool_to_word (x = 0)`, `3`, `s.vs_inst_idx`] mp_tac) >>
  simp[update_var_def] >> strip_tac >>
  irule u2s_ptr_state_jump >> gvs[update_var_def]
QED

Theorem u2s_cond_state_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (jump_to (u2s_label a (if x = 0 then 4 else 2))
      (update_var (u2s_var a 4) (bool_to_word (x = 0)) s))) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
      (jump_to (u2s_label a (if x = 0 then 4 else 2))
        (update_var (u2s_var a 4) (bool_to_word (x = 0)) s))
Proof
  strip_tac >>
  `FLOOKUP G (u2s_var a 0) = NONE /\ op_taint tn (Var (u2s_var a 0)) = {}` by
    (drule u2s_ptr_state_scalar >> simp[] >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {u2s_var a 4})`,
    `tn with t_var := tn.t_var |+ (u2s_var a 4,{})`] >>
  conj_tac >- (irule u2s_cond_counted_ptr >> simp[]) >>
  drule_all u2s_ptr_state_scalar_update >>
  disch_then (qspecl_then [`bool_to_word (x = 0)`, `4`, `s.vs_inst_idx`] mp_tac) >>
  simp[update_var_def] >> strip_tac >>
  irule u2s_ptr_state_jump >> gvs[update_var_def]
QED

Theorem uint_assign_prov:
  step_prov PG G (mk_inst id ASSIGN [op] [out]) s =
    set_prov G [out] (op_prov G op)
Proof
  simp[step_prov_def, out_prov_def, first_prov_def, mk_inst_def] >>
  Cases_on `op_prov G op` >> simp[]
QED

Theorem uint_assign_taint:
  op_taint tn op = {} /\ s'.vs_allocas = s.vs_allocas /\
  s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id ASSIGN [op] [out]) s s' tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem u2s_setup_exact_ghosts:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op (Var p) /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand op s = SOME (n2w x) /\ lookup_var p s = SOME (n2w b) /\
  (!k. op <> Var (u2s_var a k) /\ p <> u2s_var a k) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    ((DRESTRICT (DRESTRICT G (COMPL {u2s_var a 0}))
       (COMPL {u2s_var a 1})) |+ (u2s_var a 2,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 0,{}) |+
       (u2s_var a 1,{}) |+ (u2s_var a 2,{}))
    (OK (jump_to (u2s_label a 0)
      (update_var (u2s_var a 2) (n2w b)
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w x) s)))))
Proof
  strip_tac >> irule uint_assign_counted_prefix >>
  simp[u2s_setup_def, get_instruction_def, EL_APPEND_EQN, u2s_inst_def] >>
  simp[mk_inst_def] >> simp[GSYM mk_inst_def] >>
  simp[uint_assign_prov, uint_assign_taint, set_prov_def, update_var_def] >>
  irule uint_assign_counted_prefix >>
  simp[update_var_def, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def, eval_operand_def] >>
  simp[GSYM mk_inst_def] >>
  simp[uint_assign_prov, uint_assign_taint, set_prov_def, op_prov_def, op_taint_def] >>
  irule uint_assign_counted_prefix >>
  simp[update_var_def, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[GSYM mk_inst_def] >>
  simp[arithmeticTheory.ADD1, mk_inst_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE] >> simp[GSYM mk_inst_def] >>
  simp[uint_assign_prov, uint_assign_taint, set_prov_def, op_prov_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gvs[lookup_var_def, op_taint_def] >>
  simp[uint_assign_taint, op_taint_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `gas_path_ptr _ _ _ _ _ gg tt mid` >>
  qmatch_goalsub_abbrev_tac `OK dest` >>
  `dest = jump_to (u2s_label a 0) mid` by
    simp[Abbr `dest`, Abbr `mid`, jump_to_def] >>
  pop_assum SUBST1_TAC >> irule uint_jump_counted_path >>
  simp[Abbr `mid`, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def, arithmeticTheory.ADD1]
QED

Theorem u2s_clean_update_ambient:
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (update_var (u2s_var a k) w s) /\
  ghost_kept cenv es a G0 tn0 s0 (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
Proof
  strip_tac >> reverse conj_tac >- (irule u2s_scalar_ghost_kept >> simp[]) >>
  drule_all u2s_scalar_ghost_inv >>
  disch_then (qspecl_then [`w`, `k`, `s.vs_inst_idx`] mp_tac) >>
  simp[update_var_def]
QED

Theorem u2s_scalar_initialize:
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {} /\ not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n 0
    (DRESTRICT (DRESTRICT G (COMPL {u2s_var a 0})) (COMPL {u2s_var a 1}))
    (tn with t_var := tn.t_var |+ (u2s_var a 0,{}) |+ (u2s_var a 1,{}))
    (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s))
Proof
  strip_tac >>
  `!k. p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  drule_all u2s_clean_update_ambient >>
  disch_then (qspecl_then [`w`, `0`] strip_assume_tac) >>
  drule_all u2s_clean_update_ambient >>
  disch_then (qspecl_then [`0w`, `1`] strip_assume_tac) >>
  simp[u2s_ptr_state_def] >>
  simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def] >>
  gvs[op_taint_def, lookup_var_def, update_var_def] >> rpt strip_tac >>
  `k = 0 \/ k = 1` by decide_tac >> gvs[]
QED

Theorem u2s_ptr_state_pointer_update:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\ 2 <= k /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (G |+ (u2s_var a k,site))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (update_var (u2s_var a k) w s)
Proof
  strip_tac >>
  `u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i
    (G |+ (u2s_var a k,site))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (update_var (u2s_var a k) w s with vs_inst_idx := s.vs_inst_idx)` by
    (irule u2s_ptr_state_update >> simp[] >>
     qexistsl_tac [`G`, `tn`] >>
     simp[FLOOKUP_UPDATE, op_taint_def]) >>
  gvs[update_var_def]
QED

Theorem u2s_setup_ptr_state:
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {} /\ not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n 0
    ((DRESTRICT (DRESTRICT G (COMPL {u2s_var a 0}))
      (COMPL {u2s_var a 1})) |+ (u2s_var a 2,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 0,{}) |+
      (u2s_var a 1,{}) |+ (u2s_var a 2,{}))
    (jump_to (u2s_label a 0) (update_var (u2s_var a 2) (n2w b)
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s))))
Proof
  strip_tac >> drule_all u2s_scalar_initialize >>
  disch_then (qspecl_then [`w`, `n`] assume_tac) >>
  drule (Q.INST [`k` |-> `2`] u2s_ptr_state_pointer_update) >> simp[] >>
  disch_then (qspecl_then [`n2w b`, `(b,sz)`] assume_tac) >>
  irule u2s_ptr_state_jump >> simp[]
QED

Theorem u2s_setup_invariant_ptr:
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr s /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {} /\ not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op (Var p) /\
  s.vs_inst_idx = LENGTH pre /\ eval_operand op s = SOME (n2w x) /\
  (!k. op <> Var (u2s_var a k)) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\ x < dimword(:256) /\
  t = jump_to (u2s_label a 0) (update_var (u2s_var a 2) (n2w b)
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w x) s))) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n 0 G' tn' t /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr t /\
    (0 < x ==> u2s_digits a b n x x [] t)
Proof
  strip_tac >>
  `!k. p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  qexistsl_tac
    [`(DRESTRICT (DRESTRICT G (COMPL {u2s_var a 0}))
        (COMPL {u2s_var a 1})) |+ (u2s_var a 2,(b,sz))`,
     `tn with t_var := tn.t_var |+ (u2s_var a 0,{}) |+
        (u2s_var a 1,{}) |+ (u2s_var a 2,{})`] >>
  gvs[] >> conj_tac
  >- (irule (SRULE [] u2s_setup_exact_ghosts) >> simp[] >>
      qexistsl_tac [`op`, `p`, `pre`] >> simp[]) >>
  conj_tac >- (irule (SRULE [] u2s_setup_ptr_state) >> simp[]) >>
  conj_tac
  >- (irule u2s_safe_jump >> irule u2s_setup_safe >> simp[]) >>
  strip_tac >> irule u2s_digits_initial >>
  simp[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE]
QED

Theorem u2s_check_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  t = jump_to (u2s_label a (if x = 0 then 3 else 1))
        (update_var (u2s_var a 3) (bool_to_word (x = 0)) s) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn' t /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr t /\
    (!X str. u2s_digits a b n X x str s ==> u2s_digits a b n X x str t)
Proof
  strip_tac >> drule_all u2s_check_state_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[] >> conj_tac
  >- (irule u2s_safe_jump >> irule u2s_safe_update >> simp[]) >>
  simp[u2s_digits_jump, u2s_digits_update]
QED

Theorem u2s_cond_invariant_ptr:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  t = jump_to (u2s_label a (if x = 0 then 4 else 2))
        (update_var (u2s_var a 4) (bool_to_word (x = 0)) s) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn' t /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr t /\
    (!X str. u2s_digits a b n X x str s ==> u2s_digits a b n X x str t)
Proof
  strip_tac >> drule_all u2s_cond_state_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[] >> conj_tac
  >- (irule u2s_safe_jump >> irule u2s_safe_update >> simp[]) >>
  simp[u2s_digits_jump, u2s_digits_update]
QED
