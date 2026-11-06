(* Checked finite entry paths, before the array rounds induction. *)
Theory forPtrArrayEntry
Ancestors forPtrRangeEntry forPtrAdmin forPtrAllocationGhost forPtrArrayInvariant
  fragGasPathPtr venomState venomInst ptrDiscipline finite_map
  stmtSimForArrayFrag stmtSimForArrayLoop stmtSimProps bodyPtrDefs
  exprLoweringProps forPtrRangePrepare loweringPosts compileEnv stmtFragPtr

Theorem for_array_counter_entry_ptr:
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst i ASSIGN [Lit 0w] [idx]; mk_inst j JMP [Label cond] []]|> /\
  s.vs_current_bb = entry /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {idx})) (tn with t_var := tn.t_var |+ (idx,{}))
    (OK (jump_to cond (update_var idx 0w s)))
Proof
  strip_tac >>
  qpat_x_assum `s.vs_current_bb = entry` (SUBST_ALL_TAC o SYM) >>
  `get_instruction <|bb_label := s.vs_current_bb; bb_instructions :=
    [mk_inst i ASSIGN [Lit 0w] [idx]; mk_inst j JMP [Label cond] []]|>
    s.vs_inst_idx = SOME (mk_inst i ASSIGN [Lit 0w] [idx])` by
    simp[get_instruction_def] >>
  drule_all assign_literal_zero_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >>
  simp[assign_literal_scalar_ghost] >> strip_tac >>
  `gas_path_ptr D 0 ctx func PG
    (DRESTRICT G (COMPL {idx})) (tn with t_var := tn.t_var |+ (idx,{}))
    ((update_var idx 0w s) with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {idx})) (tn with t_var := tn.t_var |+ (idx,{}))
    (OK (jump_to cond ((update_var idx 0w s) with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule for_range_jump_path_ptr >>
     simp[update_var_def, get_instruction_def] >> qexists_tac `j` >> simp[]) >>
  gvs[] >> drule_all gas_path_ptr_then >> simp[jump_to_def, update_var_def]
QED

Theorem for_array_alloca_prefix_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  sz < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions := pre ++
      [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|> /\
  s.vs_inst_idx = LENGTH pre /\
  step_inst_base (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s = OK u /\
  u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
    (OK (jump_to entry u)) /\
  ptr_covers
    (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
    p (jump_to entry u) sz
Proof
  strip_tac >>
  `get_instruction <|bb_label := lbl; bb_instructions := pre ++
    [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|>
    s.vs_inst_idx = SOME (mk_inst aid ALLOCA [Lit (n2w sz)] [p])` by
    simp[get_instruction_def, rich_listTheory.EL_APPEND2] >>
  drule_all alloca_zero_path_ptr_covered >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG
    (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
    (u with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
    (OK (jump_to entry (u with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule for_range_jump_path_ptr >>
     simp[get_instruction_def, rich_listTheory.EL_APPEND2] >>
     qexists_tac `j` >> simp[]) >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[jump_to_def]) >>
  fs[ptr_covers_def, lookup_var_def, jump_to_def]
QED

Theorem for_array_counter_zero_inv_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ lookup_scopes name es.scopes = SOME snapshot /\
  lookup_scopes id es.scopes = NONE /\
  lookup_var bp s = SOME arr_base /\ lookup_var p s = SOME dst /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s /\ not_local_ptr cenv es.scopes idx /\ idx <> p /\ idx <> bp /\
  (!q. cenv.ce_return_buf <> SOME (PtrVar (Var idx) q)) /\
  ptr_covers G tn p s sz /\ ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  (!nm lo z. local_region cenv es.scopes s nm lo z ==>
    regions_disjoint (w2n dst) sz lo z) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> x <> idx /\ FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond st s0 G0 tn0 d name snapshot 0 es
    (DRESTRICT G (COMPL {idx})) (tn with t_var := tn.t_var |+ (idx,{}))
    (jump_to cond (update_var idx 0w s))
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (update_var idx 0w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (idx,{})) (update_var idx 0w s)` by
    (irule for_scalar_overwrite_ghost >> simp[]) >>
  `ret_pc_ok cenv st (update_var idx 0w s)` by
    (fs[ret_pc_ok_def] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
     `x <> idx` by metis_tac[] >> fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[for_array_inv_ptr_def, array_loop_inv_def,
    stmt_state_rel_jump_to, ghost_inv_jump_to,
    ret_pc_ok_jump_to, jump_to_def] >>
  simp[update_var_def, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (gvs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (gvs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (gvs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (gvs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[local_region_def, not_local_ptr_def, lookup_var_def] >>
      `p' <> idx` by metis_tac[] >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >> `x <> idx` by metis_tac[] >>
  fs[lookup_var_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED
