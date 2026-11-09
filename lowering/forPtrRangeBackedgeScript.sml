(* Concrete signed backedge and invariant transport. *)
Theory forPtrRangeBackedge
Ancestors forPtrRangeControl forPtrRangePrepare forPtrRangeLanding
  stmtSimForLoop fragExec venomState venomInst finite_map ptrDiscipline
  exprLoweringProps loweringPosts compileEnv localPtrsProps stmtFragPtr bodyPtrDefs

Theorem for_increment_block_path_ptr:
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
      bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [cv];
        mk_inst i3 JMP [Label cond_lbl] []] |> /\
  s.vs_current_bb = incr_lbl /\ s.vs_inst_idx = 0 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var cv s = SOME (i2w (n1 + &k)) /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (OK (jump_to cond_lbl (update_var cv (i2w (n1 + &(k+1)))
      (update_var nv (i2w (n1 + &(k+1))) s))))
Proof
  strip_tac >> irule for_range_counter_backedge_path_ptr >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`i1`, `i2`] >> simp[get_instruction_def]) >>
  qexistsl_tac [`(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := incr_lbl;
      cs_current_insts := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [cv]]; cs_next_id := i3 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := incr_lbl;
      cs_current_insts := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [cv];
        mk_inst i3 JMP [Label cond_lbl] []] |>`] >>
  simp[fn_has_code_def, emitted_blocks_def]
QED

Theorem for_backedge_state_ghost_transport:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes nv /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var cv) sz)) /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var nv) sz)) ==>
  stmt_state_rel ctx func cenv cx es
    (jump_to lbl (update_var cv w (update_var nv w s))) /\
  ghost_inv d cenv cx es
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (jump_to lbl (update_var cv w (update_var nv w s)))
Proof
  strip_tac >> conj_tac
  >- (rewrite_tac[stmt_state_rel_jump_to] >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  rewrite_tac[jump_to_def, ghost_inv_jump_to] >>
  irule (SRULE [] (Q.INST
    [`tn` |-> `tn with t_var := tn.t_var |+ (nv,{})`]
    for_scalar_overwrite_ghost)) >> simp[] >>
  irule for_scalar_overwrite_ghost >> simp[]
QED

Theorem for_backedge_reserved_frame:
  sf = jump_to lbl (update_var cv w (update_var nv w s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}) /\
  tf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{})) /\
  p <> cv /\ p <> nv /\ ptr_covers G tn p s sz /\
  not_local_ptr cenv scopes cv /\ not_local_ptr cenv scopes nv ==>
  ptr_covers Gf tf p sf sz /\ sf.vs_allocas = s.vs_allocas /\
  sf.vs_inst_idx = 0 /\ sf.vs_current_bb = lbl /\
  sf.vs_halted = s.vs_halted /\
  (!name lo z. local_region cenv scopes sf name lo z <=>
    local_region cenv scopes s name lo z) /\
  (!x. x <> cv /\ x <> nv ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> gvs[] >>
  simp[ptr_covers_def, update_var_def, jump_to_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  conj_tac >- gvs[ptr_covers_def, op_taint_def, lookup_var_def] >>
  fs[local_region_def, not_local_ptr_def, lookup_var_def] >>
  rpt gen_tac >> eq_tac >> strip_tac >>
  `p' <> cv /\ p' <> nv` by metis_tac[] >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem for_code_increment_layout:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj ==>
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
      bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [cv];
        mk_inst i3 JMP [Label cond_lbl] []] |> /\
  (!scs. not_local_ptr cenv scs cv /\ not_local_ptr cenv scs nv) /\
  nv <> cv /\ nv <> ev /\ nv <> p /\ cv <> ev /\ cv <> p
Proof
  simp[for_code_def] >> metis_tac[]
QED

Theorem for_backedge_old_frame:
  sf = jump_to lbl (update_var cv w (update_var nv w s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}) /\
  tf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{})) /\
  (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x sf = SOME v) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> gvs[] >> conj_tac >> rpt strip_tac >>
  `x <> cv /\ x <> nv` by metis_tac[] >>
  simp[lookup_var_def, jump_to_def, update_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  fs[lookup_var_def, op_taint_def] >> metis_tac[]
QED

Theorem for_range_backedge_restore_ptr:
  !P es ctx func cenv bc cx d ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj
    st s0 G0 tn0 s G tn n1 n2 k a sf Gf tf.
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  s.vs_current_bb = incr_lbl /\ s.vs_inst_idx = 0 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  P es /\ lookup_scopes id es.scopes = NONE /\ SUC k <= Num (n2 - n1) /\
  lookup_var cv s = SOME (i2w (n1 + &k)) /\
  lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME a /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  ptr_covers G tn p s sz /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  (!name lo z. local_region cenv es.scopes s name lo z ==>
    regions_disjoint (w2n a) sz lo z) /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  sf = jump_to cond_lbl (update_var cv (i2w (n1 + &(k+1)))
    (update_var nv (i2w (n1 + &(k+1))) s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}) /\
  tf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{})) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf) /\
  P es /\ lookup_scopes id es.scopes = NONE /\ SUC k <= Num (n2 - n1) /\
  sf.vs_current_bb = cond_lbl /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
  stmt_state_rel ctx func cenv cx es sf /\ ghost_inv d cenv cx es Gf tf sf /\
  lookup_var cv sf = SOME (i2w (n1 + &(SUC k))) /\
  lookup_var ev sf = SOME (i2w n2) /\ lookup_var p sf = SOME a /\
  FLOOKUP Gf cv = NONE /\ FLOOKUP Gf ev = NONE /\
  op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {} /\
  ptr_covers Gf tf p sf sz /\
  FLOOKUP sf.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  (!name lo z. local_region cenv es.scopes sf name lo z ==>
    regions_disjoint (w2n a) sz lo z) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x sf = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule for_code_increment_layout >> strip_tac >>
  `(!q. cenv.ce_return_buf <> SOME (PtrVar (Var cv) q)) /\
   (!q. cenv.ce_return_buf <> SOME (PtrVar (Var nv) q))` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf)` by
    (gvs[] >> irule (SRULE [] for_increment_block_path_ptr) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es sf /\
   ghost_inv d cenv cx es Gf tf sf` by
    (gvs[] >> irule (SRULE [] for_backedge_state_ghost_transport) >> simp[]) >>
  `ptr_covers Gf tf p sf sz /\ sf.vs_allocas = s.vs_allocas /\
   sf.vs_inst_idx = 0 /\ sf.vs_current_bb = cond_lbl /\
   sf.vs_halted = s.vs_halted /\
   (!name lo z. local_region cenv es.scopes sf name lo z <=>
     local_region cenv es.scopes s name lo z) /\
   (!x. x <> cv /\ x <> nv ==> lookup_var x sf = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))` by
    (irule for_backedge_reserved_frame >> simp[] >> metis_tac[]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sf = SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))` by
    (irule for_backedge_old_frame >> simp[] >>
     qexistsl_tac [`G`, `cv`, `cond_lbl`, `nv`, `s`, `tn`, `i2w (n1 + &(k + 1))`] >>
     simp[]) >>
  simp[] >>
  `lookup_var cv sf = SOME (i2w (n1 + &(SUC k))) /\
   FLOOKUP Gf cv = NONE /\ op_taint tf (Var cv) = {}` by
    gvs[lookup_var_def, update_var_def, jump_to_def,
        FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, arithmeticTheory.ADD1] >>
  gvs[lookup_var_def, update_var_def, jump_to_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, arithmeticTheory.ADD1] >>
  first_assum ACCEPT_TAC
QED
