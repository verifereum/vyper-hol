(* Checked array-round control boundaries. The header transports the shared
   invariant to the element-installation block without erasing the path. *)
Theory forPtrArrayAssemble
Ancestors forPtrArrayTerminal forPtrArrayInvariant forPtrArrayPrepare
  forPtrRangePrepare stmtSimForArrayLoop bodyPtrDefs venomState
  ptrDiscipline finite_map exprLoweringProps ghostPcTransportPtr stmtFragPtr compileEnv stmtSimProps loweringPosts

Theorem for_array_unequal_header_ptr:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  n = LENGTH vs /\ n < dimword (:256) /\ k < LENGTH vs /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  idx <> dv /\ p <> dv /\ bp <> dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to stmts_lbl (update_var dv 0w s))) /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    stmts_lbl st s0 G0 tn0 d name snapshot k es
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to stmts_lbl (update_var dv 0w s))
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `(n2w k : bytes32) <> n2w n` by
    (simp[wordsTheory.n2w_11] >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  conj_tac
  >- (drule_all (SRULE [op_prov_def] for_array_header_test_path_ptr) >> simp[]) >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{})) (update_var dv 0w s)` by
    (irule for_scalar_overwrite_ghost >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var dv 0w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to stmts_lbl (update_var dv 0w s))` by
    simp[jump_to_def, ghost_inv_jump_to] >>
  fs[for_array_inv_ptr_def, array_loop_inv_def] >>
  simp[for_array_inv_ptr_def, array_loop_inv_def, stmt_state_rel_jump_to,
       ret_pc_ok_jump_to] >>
  fs[lookup_var_def, eval_operand_def, op_taint_def] >>
  simp[jump_to_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (fs[ret_pc_ok_def, lookup_var_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      `x <> dv` by metis_tac[] >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac
  >- (fs[local_region_def, not_local_ptr_def, lookup_var_def] >>
      rpt strip_tac >> `p' <> dv` by metis_tac[] >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >> `x <> dv` by metis_tac[] >>
  simp[] >> metis_tac[]
QED
