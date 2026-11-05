(* Actual non-memory word loads, with raw prefix safety and normalized history. *)
Theory bodyUnwrapMemory
Ancestors
  loweringPosts
  bodyFieldMemory bodyEnvMemory exprSimUnwrap bodyMemoryDefs exprLoweringProps
  exprLowering exprSimDefs
  fragExecMem instMemFrontier allocaHistoryFragment emitHelperProps emitHelper
  compileEnv fragExec valueEncoding valueEncodingProofs vyperValue vyperAST
  venomExecSemantics venomInst venomState words list rich_list context

Theorem body_read1_frag_mem:
  emit_op opc args sm = (dst,sn) /\ ~is_terminator opc /\ opc <> INVOKE /\
  (!s. inst_mem_below_frontier
    (mk_inst sm.cs_next_id opc args [STRING #"%" (toString sm.cs_next_var)]) s) /\
  step_inst_base (mk_inst sm.cs_next_id opc args
    [STRING #"%" (toString sm.cs_next_var)]) entry =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) w entry) /\
  stmt_state_rel ctx func cenv cx es entry /\ alloca_history func entry /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn (\s. s = entry)
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand dst s = SOME w /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand dst s = SOME w /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def] >>
  disj1_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `run_inst_seq (emitted_insts sm sn) entry = OK (update_var out w entry)` by
    simp[run_inst_seq_def, Abbr `out`] >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w entry)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  `(?bb rest. lookup_block entry.vs_current_bb func.fn_blocks = SOME bb /\
      DROP entry.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    entry.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def]) >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qexists_tac `update_var out w entry` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  gvs[Abbr `out`, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem unwrap_storage_word_sim_mem:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
            (LocatedValue t p) s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >>
  gvs[unwrap_value_def, compile_ptr_load_def] >> (
  irule frag_exec_mem_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ entry` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand entry = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
         (Value v) w es' /\
       stmt_state_rel ctx func cenv cx es' entry` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
    (if p.ptr_location = LocTransient then tload w entry else sload w entry) =
      typed_val_to_w256 tvt v` by
    (rpt strip_tac >> drule_then drule storage_holds_load >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. stmt_state_rel ctx func cenv cx es' s /\
         eval_operand op s = SOME
           (if p.ptr_location = LocTransient then tload w entry else sload w entry) /\
         (!z u. not_fresh_at sm z /\ lookup_var z entry = SOME u ==>
                lookup_var z s = SOME u) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R` by
    (irule body_read1_frag_mem >> simp[] >> goal_assum (drule_at Any) >>
     simp[is_terminator_def] >> conj_tac
     >- (rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[step_inst_base_def, exec_read1_def]) >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule expr_post_of_vv_post_load >> simp[] >>
  conj_tac >- gvs[] >>
  qexistsl [`p`, `entry`, `sm`, `expr_type e`] >> simp[] >> metis_tac[])
QED

Theorem unwrap_runtime_immutable_word_sim_mem:
  emit_op DLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
            (LocatedValue t p) s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> irule frag_exec_mem_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ entry` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand entry = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' entry /\
       stmt_state_rel ctx func cenv cx es' entry` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  qmatch_asmsub_abbrev_tac `loaded = typed_val_to_w256 tvt v` >>
  `frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. stmt_state_rel ctx func cenv cx es' s /\
         eval_operand op s = SOME loaded /\
         (!z u. not_fresh_at sm z /\ lookup_var z entry = SOME u ==>
                lookup_var z s = SOME u) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R` by
    (irule body_read1_frag_mem >> simp[] >> goal_assum (drule_at Any) >>
     simp[is_terminator_def] >> conj_tac
     >- (rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     gvs[Abbr `loaded`, step_inst_base_def, exec_read1_def]) >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule expr_post_of_vv_post_load >> simp[] >>
  qexistsl [`p`, `entry`, `sm`, `expr_type e`] >> simp[] >> metis_tac[]
QED

