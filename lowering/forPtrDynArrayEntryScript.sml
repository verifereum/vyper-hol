(* Finite dynamic-array entry, with a clean saved runtime length. *)
Theory forPtrDynArrayEntry
Ancestors
  forPtrArrayEntry augAssignPtrLoad whitelistForIterDynFrag
  bodyPtrSignedConvertHeaderLoad
  abiDecodePtrScalarReplay bodyPtrBopScalarSeq forPtrArrayInvariant
  forPtrRangeEntry forPtrAdmin forPtrAllocationGhost allocationPtr
  fragGasPathPtr venomState venomInst ptrDiscipline finite_map
  stmtSimForArrayFrag stmtSimForArrayLoop stmtSimProps bodyPtrDefs
  exprLoweringProps forPtrRangePrepare loweringPosts compileEnv
  loweringStateRelDefs stmtFragPtr list rich_list

Theorem dynarray_entry_scalar_certificate[local]:
  idx NOTIN R /\ g NOTIN R /\ vld NOTIN R ==>
  bop_scalar_seq R {Var lv; Lit 0w; Lit (n2w c)}
    [mk_inst i1 ASSIGN [Lit 0w] [idx];
     mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst i3 ISZERO [Var g] [vld];
     mk_inst i4 ASSERT [Var vld] []]
    (Var vld INSERT Var g INSERT Var idx INSERT {Var lv; Lit 0w; Lit (n2w c)})
Proof
  strip_tac >>
  simp[Once bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`i1`, `ASSIGN`, `[Lit 0w]`, `idx`] >> simp[] >>
  simp[Once bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`i2`, `GT`, `[Var lv; Lit (n2w c)]`, `g`] >> simp[] >>
  simp[Once bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`i3`, `ISZERO`, `[Var g]`, `vld`] >> simp[] >>
  irule bop_scalar_seq_assert >> simp[]
QED

Theorem dynarray_entry_scalar_path_ptr[local]:
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit 0w] [idx];
       mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst i3 ISZERO [Var g] [vld];
       mk_inst i4 ASSERT [Var vld] [];
       mk_inst i5 JMP [Label cond] []]|> /\
  s.vs_current_bb = entry /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var lv s = SOME (n2w L) /\ L <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv; idx; g; vld] /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?H un.
    gas_path_ptr D 0 ctx func PG G tn s 0 H un
      (OK (jump_to cond (update_var vld 1w (update_var g 0w (update_var idx 0w s))))) /\
    FLOOKUP H idx = NONE /\ op_taint un (Var idx) = {} /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. x <> idx /\ x <> g /\ x <> vld ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `run_inst_seq
    [mk_inst i1 ASSIGN [Lit 0w] [idx];
     mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst i3 ISZERO [Var g] [vld];
     mk_inst i4 ASSERT [Var vld] []] s =
    OK (update_var vld 1w (update_var g 0w (update_var idx 0w s)))` by
    (irule dynarray_entry_block_run >> simp[] >> qexists_tac `L` >> simp[]) >>
  `bop_scalar_seq (COMPL {idx;g;vld}) {Var lv; Lit 0w; Lit (n2w c)}
    [mk_inst i1 ASSIGN [Lit 0w] [idx];
     mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst i3 ISZERO [Var g] [vld];
     mk_inst i4 ASSERT [Var vld] []]
    (Var vld INSERT Var g INSERT Var idx INSERT {Var lv; Lit 0w; Lit (n2w c)})` by
    (irule dynarray_entry_scalar_certificate >> simp[]) >>
  `!op. op IN {Var lv; Lit 0w; Lit (n2w c)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def] >> simp[op_taint_def]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK u` >>
  qmatch_asmsub_abbrev_tac `lookup_block entry func.fn_blocks = SOME bb` >>
  drule scalar_seq_success_replay_ptr >>
  disch_then (qspecl_then [`u`, `tn`, `s`, `func`, `ctx`, `bb`, `PG`, `G`, `D`] mp_tac) >>
  simp[Abbr `bb`, Abbr `code`] >> strip_tac >>
  unabbrev_all_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  reverse conj_tac
  >- (qpat_assum `!op. op = Var vld \/ op = Var g \/ op = Var idx \/ op = Var lv \/ _ ==> _`
        (qspec_then `Var idx` (strip_assume_tac o SRULE [op_prov_def])) >>
      qpat_assum `!op. op = Var vld \/ op = Var g \/ op = Var idx \/ op = Var lv \/ _ ==> _`
        (qspec_then `Var lv` (strip_assume_tac o SRULE [op_prov_def])) >>
      simp[] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx func PG G' tn'
    ((update_var vld 1w (update_var g 0w (update_var idx 0w s))) with vs_inst_idx := 4)
    0 G' tn'
    (OK (jump_to cond
      ((update_var vld 1w (update_var g 0w (update_var idx 0w s))) with vs_inst_idx := 4)))` by
    (irule for_range_jump_path_ptr >>
     simp[update_var_def, get_instruction_def] >> qexists_tac `i5` >> simp[]) >>
  drule_all gas_path_ptr_then >> simp[jump_to_def, update_var_def]
QED

Theorem dynarray_entry_resources_ptr[local]:
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit 0w] [idx];
       mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst i3 ISZERO [Var g] [vld];
       mk_inst i4 ASSERT [Var vld] [];
       mk_inst i5 JMP [Label cond] []]|> ==>
  s.vs_current_bb = entry /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\ LENGTH vs <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv; p; idx; g; vld; bp] /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st s /\
  (!x q. cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> x <> idx /\ x <> g /\ x <> vld) /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  lookup_scopes name es.scopes = SOME snapshot /\ lookup_scopes id es.scopes = NONE /\
  lookup_var bp s = SOME arr_base /\ lookup_var p s = SOME dst /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ptr_covers G tn p s sz /\ ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  (!nm lo z. local_region cenv es.scopes s nm lo z ==>
    regions_disjoint (w2n dst) sz lo z) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?t H un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
      cond st s0 G0 tn0 d name snapshot 0 es H un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK t)
Proof
  strip_tac >> strip_tac >>
  `ALL_DISTINCT [lv;idx;g;vld]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_entry_scalar_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `t = jump_to cond
    (update_var vld 1w (update_var g 0w (update_var idx 0w s)))` >>
  `!x. x <> idx /\ x <> g /\ x <> vld ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     simp[Abbr `t`, jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[op_taint_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (simp[Abbr `t`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv d cenv cx es H un t` by
    (irule ghost_inv_load_frame >>
     qexistsl_tac [`G`, `s`, `st`, `tn`] >>
     simp[Abbr `t`, jump_to_def, update_var_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >>
  simp[for_array_inv_ptr_def, array_loop_inv_def] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[ALL_DISTINCT, Abbr `t`, jump_to_def, update_var_def,
     lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    ptr_covers_def, ret_pc_ok_def, local_region_def, not_local_ptr_def] >>
  metis_tac[]
QED

Theorem dynarray_allocate_initialize_ptr[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions := pre ++
      [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|> ==>
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit 0w] [idx];
       mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst i3 ISZERO [Var g] [vld];
       mk_inst i4 ASSERT [Var vld] [];
       mk_inst i5 JMP [Label cond] []]|> ==>
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv st /\
  (!x q. cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> ~MEM x [p;idx;g;vld]) /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\ LENGTH vs <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv;p;idx;g;vld;bp] /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  lookup_var bp s = SOME arr_base /\
  ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\ ret_pc_ok cenv st s /\
  lookup_scopes name es.scopes = SOME snapshot /\ lookup_scopes id es.scopes = NONE /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  s.vs_inst_idx = LENGTH pre ==>
  ?dst t H un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz
      (mk_inst aid ALLOCA [Lit (n2w sz)] [p])
      cond st s0 G0 tn0 d name snapshot 0 es H un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK t)
Proof
  strip_tac >> strip_tac >> strip_tac >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var p) q)` by metis_tac[MEM] >>
  `bp <> p /\ (!x. not_fresh_at st x ==> x <> p)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_all for_array_alloca_resources_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. x <> p ==> lookup_var x u = lookup_var x s` by
    (rev_drule_all for_range_alloca_state >> strip_tac >> gvs[]) >>
  `FLOOKUP (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u) lv = NONE /\
   op_taint (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
     (Var lv) = {}` by
    (`FLOOKUP (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u) lv = FLOOKUP G lv /\
      op_taint (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s u tn)
        (Var lv) = op_taint tn (Var lv)` suffices_by simp[] >>
     irule alloca_old_variable_ghost_frame >>
     simp[] >> reverse conj_tac
     >- (qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >> simp[]) >>
     fs[ALL_DISTINCT]) >>
  qmatch_asmsub_abbrev_tac `ghost_inv d cenv cx es Ga ta u` >>
  `!nm lo z. local_region cenv es.scopes (jump_to entry u) nm lo z =
     local_region cenv es.scopes u nm lo z` by
    simp[local_region_def, jump_to_def, lookup_var_def] >>
  `!r z. ptr_covers Ga ta r (jump_to entry u) z = ptr_covers Ga ta r u z` by
    simp[ptr_covers_def, jump_to_def, lookup_var_def] >>
  `?t H un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz
      (mk_inst aid ALLOCA [Lit (n2w sz)] [p])
      cond st s0 G0 tn0 d name snapshot 0 es H un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr D 0 ctx func PG Ga ta (jump_to entry u) 0 H un (OK t)` by
    (drule dynarray_entry_resources_ptr >> disch_then irule >>
     simp[stmt_state_rel_jump_to, ghost_inv_jump_to, ret_pc_ok_jump_to] >>
     simp[jump_to_def, lookup_var_def, ghost_inv_jump_to, mk_inst_def] >>
     fs[ALL_DISTINCT, MEM, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`dst`, `t`, `H`, `un`] >> simp[] >>
  drule_all for_array_alloca_prefix_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >>
  strip_tac >> unabbrev_all_tac >> drule_all gas_path_ptr_then >> simp[]
QED

Theorem for_dynarray_code_initialize_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv st /\
  (!x q. cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv;p;idx;g;vld]) /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv;p;idx;g;vld;bp] /\
  lookup_var bp s = SOME arr_base /\
  ptr_covers G tn bp s 32 /\
  ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  (!i. w2n arr_base <= i /\ i < w2n arr_base + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n arr_base) s = n2w (LENGTH vs) /\ ret_pc_ok cenv st s /\
  lookup_scopes name es.scopes = SOME snapshot /\ lookup_scopes id es.scopes = NONE /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions := pre ++
      [mk_inst mi MLOAD [Var bp] [lv];
       mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|> /\
  s.vs_inst_idx = LENGTH pre /\
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit 0w] [idx];
       mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst i3 ISZERO [Var g] [vld];
       mk_inst i4 ASSERT [Var vld] [];
       mk_inst i5 JMP [Label cond] []]|> ==>
  ?dst t H un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz
      (mk_inst aid ALLOCA [Lit (n2w sz)] [p])
      cond st s G tn d name snapshot 0 es H un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H un (OK t)
Proof
  strip_tac >>
  `bp <> lv /\ (!x. not_fresh_at st x ==> x <> lv)` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst mi MLOAD [Var bp] [lv])` by
    (simp[get_instruction_def, EL_APPEND_EQN]) >>
  drule_all mload_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `ghost_inv d cenv cx es H th u` >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_x_assum `u = _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions :=
      (pre ++ [mk_inst mi MLOAD [Var bp] [lv]]) ++
      [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|>` by
    (gvs[update_var_def, APPEND_ASSOC]) >>
  `?dst t K un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz
      (mk_inst aid ALLOCA [Lit (n2w sz)] [p])
      cond st s G tn d name snapshot 0 es K un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP K lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr D 0 ctx func PG H th u 0 K un (OK t)` by
    (drule dynarray_allocate_initialize_ptr >> disch_then drule >>
     disch_then irule >> simp[op_prov_def, update_var_def] >>
     fs[MEM, op_prov_def] >>
     fs[ret_pc_ok_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  rename1 `FLOOKUP gf lv = NONE` >>
  qexistsl_tac [`dst`, `t`, `gf`, `un`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED
