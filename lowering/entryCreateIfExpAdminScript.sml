(* Selected control transfers in ternary compilation. *)
Theory entryCreateIfExpAdmin
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  entryCreateCompositeFocus bodyFullIfExpShadow fragGasEmitCtrl
  createMarkedPath dftGasFromListTraceDefs fragGasPath
  createSizePrefixReplay fragGasOrigin gasEvents memSafeRun instMemFrontier
  venomExecProofs venomExecSemantics venomInst venomState emitHelperProps
  fragExec context list relation pair
  loweringPosts exprSimMemDefs exprSimDefs vyperAST vyperValue valueEncoding
  compileEnv abiEncoderProps slotCopyExecution entryCreatePathScope

Theorem ifexp_jump_edge:
  create_operand_fetch a b f s i /\ ~s.vs_halted /\
  (i.inst_opcode = JNZ \/ i.inst_opcode = JMP) /\
  step_inst_base i s = OK (jump_to lbl s) ==>
  create_prefix_step a b E C f s [] (jump_to lbl s)
Proof
  strip_tac >> gvs[create_operand_fetch_def, create_operand_at_def] >>
  simp[create_prefix_step_def, gas_origin_edge_def] >>
  qexists_tac `0` >>
  gvs[step_inst_non_invoke, gas_events_step_def, is_terminator_def] >>
  metis_tac[]
QED

Theorem ifexp_jump_native_endpoint:
  create_operand_fetch a b f s i /\
  (i.inst_opcode = JNZ \/ i.inst_opcode = JMP) /\
  step_inst_base i s = OK (jump_to lbl s) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,right) ==>
  v = jump_to lbl s
Proof
  strip_tac >>
  fs[create_operand_native_step_def, LET_THM, create_operand_fetch_def,
     create_prefix_step_def, gas_origin_edge_def] >>
  gvs[step_inst_non_invoke, is_terminator_def, exit_result_def, jump_to_def] >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  gvs[eval_phis_no_phi]
QED

Theorem ifexp_admin_jump_scope:
  create_operand_fetch a b f s i /\ ~s.vs_halted /\
  (i.inst_opcode = JNZ \/ i.inst_opcode = JMP) /\
  step_inst_base i s = OK (jump_to lbl s) /\
  create_operand_at b (jump_to lbl s) ==>
  create_operand_full_scope a b E C f s [] (OK (jump_to lbl s))
Proof
  strip_tac >> simp[create_operand_full_scope_def, GSYM create_operand_at_def] >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def] >> metis_tac[ifexp_jump_edge]
QED

Theorem ifexp_admin_jump_visit:
  create_operand_at a s /\ create_operand_fetch a b f s i /\
  (i.inst_opcode = JNZ \/ i.inst_opcode = JMP) /\
  step_inst_base i s = OK (jump_to lbl s) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_at b (jump_to lbl s) /\
  create_interior_visit a b E C f (p,d,k) s (before,hit,after) ==>
  before = [] /\ hit = ((p,d,i.inst_id),f,i,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `create_interior_visit _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_interior_visit_def]) >>
  qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
  >- (gvs[create_operand_fetch_def, trace_step_noninvoke] >> metis_tac[]) >>
  qmatch_asmsub_rename_tac `create_operand_native_step a b E C f p (d,k,s,[]) z` >>
  PairCases_on `z` >> drule_all ifexp_jump_native_endpoint >> strip_tac >>
  `!w. ~create_operand_native_step a b E C f p (z0,z1,z2,z3) w` by
    (simp[FORALL_PROD, create_operand_native_step_def, create_operand_fetch_def] >>
     metis_tac[]) >>
  qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  gvs[create_operand_fetch_def]
QED

(* Locate the actual test's administrative transfer. Its endpoint is the
   selected label's entry (not the next index in the test's block). *)
Theorem ifexp_selected_jnz_fetch:
  expr_post H ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\ create_operand_at sc u ==>
  ?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb u.vs_inst_idx =
         SOME (mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] []) /\
       step_inst_base (mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] []) u =
         OK (jump_to (if sel then tl else el) u)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `eval_operand cop u = SOME (if sel then 1w else 0w)` by
    fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  qexists_tac `bb` >> gvs[create_operand_at_def] >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`tl`,`el`,`sj.cs_next_id`] mp_tac) >>
  Cases_on `sel` >> simp[mk_inst_def]
QED

Theorem ifexp_assign_edge:
  create_operand_fetch a b f s (mk_inst id ASSIGN [op] [rv]) /\
  ~s.vs_halted /\ eval_operand op s = SOME w ==>
  create_prefix_step a b E C f s []
    ((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> fs[create_operand_fetch_def, create_operand_at_def] >>
  simp[create_prefix_step_def, gas_origin_edge_def] >>
  qexists_tac `0` >>
  drule_then (assume_tac o REWRITE_RULE [mk_inst_def])
    slotCopyExecutionTheory.slot_copy_step_assign >>
  simp[step_inst_non_invoke, gas_events_step_def, is_terminator_def,
       mk_inst_def, update_var_def]
QED

(* The join is entered by JMP after ASSIGN, with neither instruction
   making an explicit GAS observation. *)
Theorem ifexp_finish_scope:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy f /\ fn_has_code sy sz f /\
  z.cs_current_bb = xl /\ z.cs_current_insts = [] /\
  sx.cs_current_bb <> xl /\ sz.cs_next_id <= z.cs_next_id /\
  create_operand_at sx s /\ ~s.vs_halted /\ eval_operand op s = SOME w ==>
  create_operand_full_scope sx z E C f s []
    (OK (jump_to xl ((update_var rv w s) with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >>
  qpat_assum `emit_inst ASSIGN _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_inst_extends) >>
  qpat_assum `emit_inst JMP _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_inst_extends) >>
  `?bb. lookup_block sx.cs_current_bb f.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH sx.cs_current_insts) =
          SOME (mk_inst sx.cs_next_id ASSIGN [op] [rv]) /\
        get_instruction bb (LENGTH sy.cs_current_insts) =
          SOME (mk_inst sy.cs_next_id JMP [Label xl] [])` by
    (mp_tac (Q.SPECL [`sx`,`sy`,`f`,`[mk_inst sx.cs_next_id ASSIGN [op] [rv]]`]
       fn_has_code_same_block) >> simp[] >> strip_tac >>
     mp_tac (Q.SPECL [`sy`,`sz`,`f`,`[mk_inst sy.cs_next_id JMP [Label xl] []]`]
       fn_has_code_same_block) >> simp[] >> metis_tac[]) >>
  qabbrev_tac `u = (update_var rv w s) with vs_inst_idx := LENGTH sy.cs_current_insts` >>
  `create_operand_at sy u /\ ~u.vs_halted` by
    fs[Abbr `u`, create_operand_at_def, update_var_def] >>
  `create_operand_fetch sx z f s (mk_inst sx.cs_next_id ASSIGN [op] [rv]) /\
   create_operand_fetch sx z f u (mk_inst sy.cs_next_id JMP [Label xl] [])` by
    (pure_rewrite_tac[create_operand_fetch_def] >> fs[create_operand_at_def] >>
     gvs[frag_ids_def, mk_inst_def]) >>
  `u = (update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx` by
    fs[Abbr `u`, create_operand_at_def, arithmeticTheory.ADD1] >>
  `create_prefix_step sx z E C f s [] u` by metis_tac[ifexp_assign_edge] >>
  qpat_x_assum `u = _` kall_tac >>
  `create_prefix_step sx z E C f u [] (jump_to xl u)` by
    (irule ifexp_jump_edge >> simp[] >>
     qexists_tac `mk_inst sy.cs_next_id JMP [Label xl] []` >> simp[] >>
     simp[mk_inst_def, step_jmp_behavior]) >>
  `create_operand_at z (jump_to xl u)` by simp[create_operand_at_def, jump_to_def] >>
  simp[create_operand_full_scope_def, GSYM create_operand_at_def] >>
  `create_expr_prefix sx z E C f s [] u /\
   create_expr_prefix sx z E C f u [] (jump_to xl u)` by
    (simp[create_expr_prefix_marked] >> conj_tac >> irule RTC_SINGLE >>
     simp[create_marked_edge_def]) >>
  drule_all create_expr_prefix_append >> simp[]
QED
