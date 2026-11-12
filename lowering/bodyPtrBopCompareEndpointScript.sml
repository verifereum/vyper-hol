Theory bodyPtrBopCompareEndpoint
Ancestors
  bodyPtrBopCompareSuffix bodyPtrBopCompareCompile bodyPtrBopCompare bodyPtrBopHashFrame
  bodyPtrBopHashSuffix exprLowering fragExec finite_map
  bodyPtrHashBuiltinsGhostFrame bodyPtrBopOperandContract exprSimWordArgs
  exprSimHashBoundary exprPtrUnwrapCopyEdges wordArgsPtr freshWrites
  loweringPosts loweringStateRelDefs compileEnv exprLoweringProps emitHelperProps
  emitHelper venomState venomInst venomExecSemantics ptrDiscipline
  fragGasPathPtr arithmetic rich_list localPtrsProps

Theorem bop_compare_emit_endpoint:
  ((opc = EQ /\ ops = [left;right] /\
       op_prov G left = NONE /\ op_prov G right = NONE) \/
   (opc = ISZERO /\ ops = [left])) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  emit_op opc ops sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    ghost_inv d cenv cx es H un (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    ghost_kept cenv es sc G tn s H un /\
    wb_frame cenv es es sc s (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    op_prov H op = NONE /\ op_taint un op = {} /\
    un.t_imm = tn.t_imm /\ un.t_mem = tn.t_mem /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_compare_emit_placement >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sc.cs_next_id opc ops
    [STRING #"%" (toString sc.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK t` >>
  `((opc = EQ /\ ops = [left;right]) \/ (opc = ISZERO /\ ops = [left]))` by
    metis_tac[] >>
  `(t with vs_vars := s.vs_vars) = s` by
    (irule bop_compare_state_frame >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `?H un. H = step_prov PG G inst t /\ un = step_taint inst s t tn` by simp[] >>
  `un.t_imm = tn.t_imm` by
    (gvs[] >> irule copy_step_immutable_taint >>
     gvs[Abbr `inst`, mk_inst_def]) >>
  `op_prov H (Var (STRING #"%" (toString sc.cs_next_var))) = NONE /\
   op_taint un (Var (STRING #"%" (toString sc.cs_next_var))) = {} /\
   un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
   (!x. x <> STRING #"%" (toString sc.cs_next_var) ==>
     FLOOKUP H x = FLOOKUP G x /\ FLOOKUP un.t_var x = FLOOKUP tn.t_var x)` by
    (gvs[Abbr `inst`] >> irule bop_compare_ghost_frame >> metis_tac[]) >>
  suspend "finish"
QED

Resume bop_compare_emit_endpoint[finish]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at sc x ==> x <> STRING #"%" (toString sc.cs_next_var)` by
    gvs[not_fresh_at_def] >>
  `!x. not_fresh_at sc x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    FLOOKUP un.t_var x = FLOOKUP tn.t_var x` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sc.cs_next_var)` by metis_tac[] >>
     simp[] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     gvs[Abbr `inst`] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, exec_pure1_def,
       AllCaseEqs()] >> rpt strip_tac >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ghost_inv d cenv cx es H un t` by
    (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sc`, `tn`] >>
     simp[op_taint_def]) >>
  `ghost_kept cenv es sc G tn s H un` by
    (irule hash_ghost_kept_frame >> simp[op_taint_def]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s`, `sc`] >> simp[]) >>
  drule bop_compare_emit_layout >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 H un
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `H = _` SUBST1_TAC >>
     qpat_x_assum `un = _` SUBST1_TAC >>
     qunabbrev_tac `inst` >> irule bop_compare_counted_edge >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H un
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
     qexistsl_tac [`H`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `un`] >>
     simp[gas_path_ptr_rules]) >>
  `LENGTH sd.cs_current_insts = SUC s.vs_inst_idx` by decide_tac >>
  `wb_frame cenv es es sc s (t with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (`t.vs_memory = s.vs_memory` by
       (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
        simp[venom_state_component_equality] >> metis_tac[]) >>
     irule wb_frame_readonly_tail >>
     qexistsl_tac [`sc`, `s`] >> simp[wb_frame_refl, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  qexistsl_tac [`H`, `un`] >>
  asm_rewrite_tac[hash_ghost_inv_inst_idx, stmt_state_rel_inst_idx] >>
  metis_tac[]
QED
Finalise bop_compare_emit_endpoint

Theorem bop_compile_compare_endpoint:
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop left right ty sc = (op,sd) /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := LENGTH sd.cs_current_insts)) /\
    ghost_inv d cenv cx es H un (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    ghost_kept cenv es sc G tn s H un /\
    wb_frame cenv es es sc s (t with vs_inst_idx := LENGTH sd.cs_current_insts) /\
    op_prov H op = NONE /\ op_taint un op = {}
Proof
  strip_tac >> gvs[compile_compare_def, comp_bind_def, AllCaseEqs()]
  >- (drule_all (SRULE [] (Q.INST [`opc` |-> `EQ`, `ops` |-> `[left;right]`]
        bop_compare_emit_endpoint)) >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `~is_terminator ISZERO` by simp[is_terminator_def] >>
  drule_all bop_compare_pair_run_split >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `EQ`, `ops` |-> `[left;right]`]
    bop_compare_emit_endpoint)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  imp_res_tac emitted_insts_emit_op >>
  `local_ptrs_reserved cenv cs' /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs' x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs' x)` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >>
       qexists_tac `sc` >> simp[]) >>
     conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
  `~(u with vs_inst_idx := LENGTH cs'.cs_current_insts).vs_halted /\
   (u with vs_inst_idx := LENGTH cs'.cs_current_insts).vs_current_bb = cs'.cs_current_bb /\
   (u with vs_inst_idx := LENGTH cs'.cs_current_insts).vs_inst_idx = LENGTH cs'.cs_current_insts` by simp[] >>
  drule_all (GEN_ALL (SRULE [] (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[eq_res]`,
    `sc` |-> `cs'`, `left` |-> `eq_res`, `right` |-> `eq_res`,
    `s` |-> `v with vs_inst_idx := LENGTH cs'.cs_current_insts`,
    `t` |-> `w with vs_inst_idx := LENGTH cs'.cs_current_insts`]
    bop_compare_emit_endpoint))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `wb_frame cenv es es sc s (t with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (metis_tac[exprSimWordArgsTheory.wb_frame_trans, DECIDE ``n <= n + 1``]) >>
  `ghost_kept cenv es sc G tn s H' un'` by
    (metis_tac[wordArgsPtrTheory.ghost_kept_wb_trans, DECIDE ``n <= n + 1``]) >>
  qexistsl_tac [`H'`, `un'`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`H`, `u with vs_inst_idx := LENGTH cs'.cs_current_insts`, `un`] >> gvs[]
QED

(* The parent frame is accumulated over both operand evaluations. *)
Theorem bop_bool_parent_post:
  expr_type e = BaseT BoolT /\
  stmt_state_rel ctx func cenv cx ee t /\
  ghost_inv d cenv cx ee H un t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand op t = SOME (bool_to_word b) /\
  op_prov H op = NONE /\ op_taint un op = {} /\
  wb_frame cenv es ee sa s0 t /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
  ghost_kept cenv es sa G0 tn0 s0 H un ==>
  bop_operand_post d ctx func cenv cx e es sa sb op s0 G0 tn0
    (BoolV b) ee t H un
Proof
  strip_tac >>
  `expr_post ctx func cenv cx e es sa sb s0 ee (BoolV b) op t` by
    (irule expr_post_word_intro >> Cases_on `b` >>
     simp[is_word_type_def, loweringSliceTheory.word_value_def,
       valueEncodingTheory.val_to_w256_def, bool_to_word_def]) >>
  simp[bop_operand_post_def, is_word_type_def] >>
  irule bodyPtrDefsTheory.ptr_val_ok_word >> simp[is_word_type_def]
QED
