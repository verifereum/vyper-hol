(* Joint literal-32 ADD link for the Concat prefix. *)
Theory bodyFullBuiltinConcatAdd
Ancestors
  bodyFullBuiltinBytestringBuffer
  bodyFullAllocaFresh bodyFullGhostFrame bodyFullUnwrapRun
  concatArmSeqPtr bodyPtrBytestringBuiltinsWindowGhost ptrSafetyTransport
  wordArgsPtr fragGasSeqPtr fragExec
  loweringHalt emitHelperProps exprLoweringProps venomMemProps finite_map pred_set

Theorem concat_data_add_full:
  emit_op ADD [Var bv; Lit 32w] sc = (data_operand,sc') /\
  fn_has_code sc sc' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  alloca_history func s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  lookup_var bv s = SOME bw /\ ptr_covers G tn bv s bsz /\
  32 < bsz /\ w2n bw+32 < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) ==>
  ?dp t G' tn'.
    data_operand = Var dp /\ not_fresh_at sc' dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sc'.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc'.cs_current_insts /\ ~t.vs_halted /\
    lookup_var dp t = SOME (n2w (w2n bw+32)) /\
    ptr_covers G' tn' dp t (bsz-32) /\ alloca_history func t /\ allocas_from lo t /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!(H:(bool # bytes32 # type_value) list # num list).
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' t)
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> pure_rewrite_tac[same_blocks_def] >> strip_tac >>
  `32+(bsz-32) <= bsz` by decide_tac >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\ op_taint tn (Lit 32w) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all concat_offset_seq_ptr >>
  disch_then (qspecl_then [`STRING #"%" (toString sc.cs_next_var)`,
    `sc.cs_next_id`, `func`, `PG`, `ARB`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG G tn _ s G1 tn1` >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr ARB 0 ctx func PG G tn code s G1 tn1` >>
  rename1 `run_inst_seq _ s = OK raw` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn code s G1 tn1` by
    (gen_tac >> drule_all concat_offset_seq_ptr >>
     disch_then (qspecl_then [`STRING #"%" (toString sc.cs_next_var)`,
       `sc.cs_next_id`, `func`, `PG`, `D`] strip_assume_tac) >>
     gvs[Abbr `code`, inst_seq_ptr_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s G1 tn1` by
    (gen_tac >> gvs[Abbr `code`, inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists `0` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH sc'.cs_current_insts),G1,tn1)` by
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`code`, `sc`] >>
     simp[Abbr `code`, venomInstTheory.is_terminator_def,
       fragExecMemTheory.run_inst_seq_mem_ok_last,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sc.cs_next_var)` >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sc'.cs_current_insts` >>
  `!x. not_fresh_at sc x ==> x <> out` by
    (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >>
     first_x_assum (qspec_then `sc.cs_next_var` mp_tac) >> simp[]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >> qexists `sc` >> simp[]) >>
  `!(H:(bool # bytes32 # type_value) list # num list).
    stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t` by
    (rpt strip_tac >> simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     qpat_assum `raw = update_var _ _ s` SUBST1_TAC >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (qunabbrev_tac `t` >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`code`, `s`, `sc`] >>
     simp[Abbr `code`, venomInstTheory.is_terminator_def]) >>
  `!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     qpat_assum `raw = update_var _ _ s` SUBST1_TAC >>
     simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    (simp[Abbr `t`] >> qpat_assum `raw = update_var _ _ s` SUBST1_TAC >>
     simp[venomStateTheory.update_var_def, venomStateTheory.venom_state_component_equality]) >>
  `!D. ghost_inv_at D lo d cenv cx es G tn s ==>
       ghost_inv_at D lo d cenv cx es G1 tn1 t` by
    (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl [`G`, `es`, `s`, `sc`, `tn`] >> simp[] >>
     simp[Abbr `t`] >> qpat_assum `raw = update_var _ _ s` SUBST1_TAC >>
     simp[venomStateTheory.update_var_def]) >>
  qexistsl [`out`, `t`, `G1`, `tn1`] >>
  simp[] >>
  simp[Abbr `t`, Abbr `out`, loweringStateRelDefsTheory.not_fresh_at_def] >>
  qpat_assum `raw = update_var _ _ s` SUBST1_TAC >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       ptrDisciplineTheory.allocas_from_def, finite_mapTheory.FLOOKUP_UPDATE,
       GSYM wordsTheory.word_add_n2w] >>
  fs[ptrDisciplineTheory.allocas_from_def]
QED

Theorem concat_data_add_fresh_full:
  emit_op ADD [Var bv; Lit 32w] sc = (data_operand,sc') /\
  fn_has_code sc sc' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  alloca_history func s /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  lookup_var bv s = SOME bw /\ ptr_covers G tn bv s bsz /\
  not_fresh_at sc bv /\
  32 <= bsz /\ w2n bw+32 < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) ==>
  ?dp t G' tn'.
    data_operand = Var dp /\ not_fresh_at sc' dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sc'.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc'.cs_current_insts /\ ~t.vs_halted /\
    lookup_var dp t = SOME (n2w (w2n bw+32)) /\
    lookup_var bv t = SOME bw /\ ptr_covers G' tn' bv t bsz /\
    ptr_covers G' tn' dp t (bsz-32) /\ alloca_history func t /\ allocas_from lo t /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!(H:(bool # bytes32 # type_value) list # num list).
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' t)
Proof
  strip_tac >>
  `data_operand = Var (STRING #"%" (toString sc.cs_next_var))` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sc.cs_next_var)` >>
  `bv <> out` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >>
     first_x_assum (qspec_then `sc.cs_next_var` mp_tac) >> simp[]) >>
  qpat_x_assum `data_operand = Var out` SUBST_ALL_TAC >>
  drule_all bytestring_data_offset_full_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >> qexists `sc` >> simp[]) >>
  `!(H:(bool # bytes32 # type_value) list # num list).
    stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t` by
    (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> pure_rewrite_tac[same_blocks_def] >> strip_tac >>
  `alloca_history func t` by
    (qpat_assum `t = _` SUBST1_TAC >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`[mk_inst sc.cs_next_id ADD [Var bv; Lit 32w] [out]]`, `s`, `sc`] >>
     simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.exec_pure2_def, venomStateTheory.eval_operand_def,
       Abbr `out`]) >>
  `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    simp[venomStateTheory.update_var_def, venomStateTheory.venom_state_component_equality] >>
  `!D. ghost_inv_at D lo d cenv cx es G tn s ==>
       ghost_inv_at D lo d cenv cx es G' tn' t` by
    (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl [`G`, `es`, `s`, `sc`, `tn`] >> simp[] >>
     simp[venomStateTheory.update_var_def]) >>
  qexistsl [`out`, `t`, `G'`, `tn'`] >> simp[] >>
  simp[ptrDisciplineTheory.allocas_from_def, venomStateTheory.update_var_def,
       GSYM wordsTheory.word_add_n2w, Abbr `out`,
       loweringStateRelDefsTheory.not_fresh_at_def] >>
  gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
  fs[ptrDisciplineTheory.allocas_from_def]
QED
