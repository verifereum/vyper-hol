(* Checked scalar condition boundary for immutable array iteration. *)
Theory bodyImmConditionPtr
Ancestors
  forPtrControl forPtrRangePrepare stmtSimForArrayLoop bodyPtrDefs
  ghostPcTransportPtr stmtSimProps stmtFragPtr
  venomState venomInst venomExecSemantics fragExec ptrDiscipline finite_map words list arithmetic
  loweringStateRelDefs loweringPosts compileEnv exprLoweringProps

Theorem immutable_condition_ptr:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  ~ctx_has_dalloca ctx /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. lvo = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\
  (!z. cenv.ce_return_buf <> SOME (PtrVar (Var dv) z)) /\
  array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst cond caller k es s /\
  ghost_inv d cenv cx es G tn s /\ ptr_covers G tn p s sz /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
  op_prov G lvo = NONE /\ op_taint tn lvo = {} /\
  (!x v. not_fresh_at caller x /\ lookup_var x orig = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at caller x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
    gas_path_ptr D 0 ctx func PG G tn s 0 (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{})) (OK (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s))) /\
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst (if k = LENGTH vs then exit else bod) caller k es (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s)) /\
    ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{})) (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s)) /\ ptr_covers (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{})) p (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s)) sz /\
    FLOOKUP (DRESTRICT G (COMPL {dv})) idx = NONE /\ op_taint (tn with t_var := tn.t_var |+ (dv,{})) (Var idx) = {} /\
    eval_operand lvo (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s)) = SOME (n2w (LENGTH vs)) /\
    op_prov (DRESTRICT G (COMPL {dv})) lvo = NONE /\ op_taint (tn with t_var := tn.t_var |+ (dv,{})) lvo = {} /\
    (!x v. not_fresh_at caller x /\ lookup_var x orig = SOME v ==>
      lookup_var x (jump_to (if k = LENGTH vs then exit else bod) (update_var dv (bool_to_word (k = LENGTH vs)) s)) = SOME v) /\
    (!x. not_fresh_at caller x ==> FLOOKUP (DRESTRICT G (COMPL {dv})) x = FLOOKUP G0 x /\
      op_taint (tn with t_var := tn.t_var |+ (dv,{})) (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> simp[] >>
  `k <= LENGTH vs /\ lookup_var idx s = SOME (n2w k) /\
   ~s.vs_halted /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
   stmt_state_rel ctx func cenv cx es s` by fs[array_loop_inv_def] >>
  `k < dimword (:256)` by decide_tac >>
  `((n2w k : bytes32) = n2w (LENGTH vs)) = (k = LENGTH vs)` by simp[n2w_11] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "semantic" >>
  conj_tac >- (drule_all for_scalar_overwrite_ghost >>
    simp[jump_to_def, ghost_inv_jump_to]) >>
  conj_tac >- (gvs[ptr_covers_def, op_taint_def, lookup_var_def,
    jump_to_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  fs[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `lvo` >>
    gvs[eval_operand_def, lookup_var_def, jump_to_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- (Cases_on `lvo` >> gvs[op_prov_def, FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases_on `lvo` >> gvs[op_taint_def, FLOOKUP_UPDATE]) >>
  conj_tac >- (rpt strip_tac >>
    `x <> dv` by metis_tac[] >>
    simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    fs[lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >> `x <> dv` by metis_tac[] >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Resume immutable_condition_ptr[path]:
  `bool_to_word (k = LENGTH vs) =
    (if k = LENGTH vs then 1w else 0w)` by
    (Cases_on `k = LENGTH vs` >> simp[bool_to_word_def]) >>
  asm_rewrite_tac[] >>
  qpat_assum `(n2w k:bytes32) = n2w (LENGTH vs) <=> _` (fn th =>
    irule (REWRITE_RULE [th] (Q.INST
      [`w` |-> `(n2w k:bytes32)`, `z` |-> `(n2w (LENGTH vs):bytes32)`]
      for_counter_test_path_ptr))) >> simp[op_prov_def] >>
  qexistsl_tac [`lvo`, `idx`, `j1`,
    `(ARB:compile_state) with <|cs_blocks := []; cs_current_bb := cond;
      cs_current_insts := []; cs_next_id := j1|>`,
    `(ARB:compile_state) with <|cs_blocks := []; cs_current_bb := cond;
      cs_current_insts := [mk_inst j1 EQ [Var idx;lvo] [dv];
        mk_inst j2 JNZ [Var dv;Label exit;Label bod] []]|>`,
    `(ARB:compile_state) with <|cs_blocks := []; cs_current_bb := cond;
      cs_current_insts := [mk_inst j1 EQ [Var idx;lvo] [dv]];
      cs_next_id := j2|>`] >>
  fs[fn_has_code_def, emitted_blocks_def, bool_to_word_def, op_prov_def]
QED

Resume immutable_condition_ptr[semantic]:
  `stmt_state_rel ctx func cenv cx es
    (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  fs[array_loop_inv_def] >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to,
    eval_operand_def, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[ret_pc_ok_def, lookup_var_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `x <> dv` by metis_tac[] >> simp[FLOOKUP_UPDATE] >> metis_tac[]
QED
Finalise immutable_condition_ptr
