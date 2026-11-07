Theory bodyPtrStructLitCountedAdd
Ancestors bodyPtrStructLitAddConsumer bodyPtrStructLitFieldStore
  bodyPtrStructLitPostAdd emitHelperProps fragExec context compileEnv
  emitHelper freshWrites bodyPtrDefs venomState finite_map ptrDiscipline

Theorem emitted_add_instruction:
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  fn_has_code sc sm fn /\ not_fresh_at sc p ==>
  p <> dst /\ ?bb.
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sc.cs_current_insts) =
      SOME (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sm.cs_current_bb = sc.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_return_def, fresh_var_def,
        fresh_id_def, comp_ignore_bind_def, emit_def] >>
  `p <> dst` by (gvs[not_fresh_at_def] >> metis_tac[]) >>
  drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> gvs[]
QED

Theorem raw_child_emitted_add_counted:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  not_fresh_at sb p /\ ptr_covers G0 tn0 p t N /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  fn_has_code sc sm fn /\ not_fresh_at sc p /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?a s1 G1 tn1.
    lookup_var p s = SOME a /\
    s1 = (update_var dst (a+off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])
      (update_var dst (a+off) s) /\
    tn1 = step_taint (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst]) s
      (update_var dst (a+off) s) tn /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
    ptr_covers G1 tn1 p s1 N /\ ~s1.vs_halted
Proof
  strip_tac >> drule_all vv_post_ghost_kept_covers >> strip_tac >>
  drule_all emitted_add_instruction >> strip_tac >>
  `?a. lookup_var p s = SOME a` by fs[ptr_covers_def] >>
  `op_taint tn (Var p) = {}` by fs[ptr_covers_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sc.cs_next_id ADD [Var p; Lit off] [dst])` by simp[] >>
  `eval_operand (Var p) s = SOME a /\ eval_operand (Lit off) s = SOME off /\
   op_taint tn (Lit off) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all clean_add_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`] assume_tac) >>
  qexists `a` >> simp[] >>
  reverse conj_tac >- simp[update_var_def] >>
  `!G' tn' u k. ptr_covers G' tn' p (u with vs_inst_idx := k) N =
                 ptr_covers G' tn' p u N` by
    simp[ptr_covers_def, lookup_var_def] >>
  asm_rewrite_tac[] >> irule ptr_covers_fresh_add >> simp[]
QED
