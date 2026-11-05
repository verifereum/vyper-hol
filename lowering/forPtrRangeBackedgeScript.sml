(* Concrete signed backedge and invariant transport. *)
Theory forPtrRangeBackedge
Ancestors forPtrRangeControl forPtrRangePrepare forPtrRangeLanding
  stmtSimForLoop fragExec venomState venomInst finite_map ptrDiscipline
  exprLoweringProps loweringPosts compileEnv localPtrsProps

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
  qexistsl_tac [`<| bb_label := incr_lbl;
      bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [cv];
        mk_inst i3 JMP [Label cond_lbl] []] |>`, `i1`, `i2`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := incr_lbl;
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
  irule (SRULE [] for_scalar_overwrite_ghost) >> simp[] >>
  irule for_scalar_overwrite_ghost >> simp[]
QED
