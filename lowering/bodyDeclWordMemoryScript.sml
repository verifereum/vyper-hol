(* Counted memory simulation of a declaration of a word type: the local's
   ALLOCA, the right-hand side, and one MSTORE into the local.  The memory
   twin of stmtSimDecl's compile_annassign_stmt_frag. *)
Theory bodyDeclWordMemory
Ancestors
  bodyDeclMemoryCompose bodyDeclMemoryCounted bodyDeclMemoryCore
  stmtSimDeclCompose stmtSimDeclSource stmtSimDeclStore stmtSimDeclMem
  stmtSimDecl exprSimMemDefs bodyMemoryDefs instMemFrontier fragExecMem
  fragGasMode fragGasPathMem fragGasPath gasSummary gasOutcome
  loweringPosts exprSimDefs stmtSimDefs stmtSimProps loweringSlice
  exprLoweringProps localPtrsProps freshWrites emitHelper emitHelperProps
  fragExec venomInst venomState venomExecSemantics stmtLowering compileEnv
  vyperInterpreter vyperState list rich_list finite_map
Libs monadsyntax

(* The MSTORE that binds a word local after its right-hand side: a
   memory-checked path of no gas readings. *)
Theorem annassign_word_mstore_path_mem:
  emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd /\
  w2n w + 32 <= s.vs_alloca_next /\ alloca_history func s /\ alloca_inv s /\
  fn_inst_ids_distinct func ==>
  gas_path_mem ctx func s 0
    (OK (mstore (w2n w) wd s with vs_inst_idx := LENGTH sf.cs_current_insts)) /\
  alloca_history func
    (mstore (w2n w) wd s with vs_inst_idx := LENGTH sf.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks sb sf` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def, same_blocks_def] >>
     strip_tac >> gvs[]) >>
  `run_inst_seq (emitted_insts sb sf) s = OK (mstore (w2n w) wd s)` by
    (simp[run_inst_seq_def] >>
     `step_inst_base (mk_inst sb.cs_next_id MSTORE [Var p; op] []) s =
        OK (mstore (w2n w) wd s)` by
       (irule step_MSTORE >> simp[eval_operand_def]) >>
     simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sb sf)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sb sf) s` by
    (simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
     simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
          eval_operand_def]) >>
  conj_tac
  >- (drule_at (Pat `run_inst_seq _ _ = _`) body_decl_zero_gas_path >>
      simp[]) >>
  irule body_store_memory_history >> simp[] >>
  qexistsl_tac [`s`, `sb`] >> fs[EVERY_MEM]
QED

(* x: T = e for a word type T: the ALLOCA's path (bodyDeclMemoryCounted),
   the right-hand side's counted memory simulation, then the MSTORE. *)
Theorem compile_annassign_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id vtyp e es etv.
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs tyv v es1. evaluate_type (get_tenv cx) vtyp = SOME tyv /\
      (do result <- eval_expr cx e; read_result cx result od)
        (es with gas_obs := gs) = (INL v, es1) ==>
      store_lays_out etv tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
      expr_sim_mem ctx func c cx (expr_type e) e es /\
      !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
        cs_extends sa sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all compile_annassign_word_parts >>
  disch_then (qx_choosel_then [`sA`, `sB`, `op`] strip_assume_tac) >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sA func /\ fn_has_code sA sb func` by
    (qspecl_then [`st`, `sA`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sB sb func` by
    (qspecl_then [`sA`, `sB`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sa sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    metis_tac[] >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by
    simp[] >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  drule annassign_admissible_type >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,salloc)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func c cx e es sA sB salloc ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts /\
      alloca_history func t /\ salloc.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_mem_def] >> disch_then irule >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sB.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         mk_inst_def, is_terminator_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sA x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     drule emit_inst_extends >> simp[]) >>
  irule annassign_rhs_outcome_mem >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  qexists_tac `tyv` >> simp[PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `store_lays_out etv tyv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `FLOOKUP t.vs_allocas st.cs_next_id =
     SOME (w2n w, type_memory_bytes cenv vtyp)` by metis_tac[] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `w2n w + 32 <= t.vs_alloca_next` by decide_tac >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 etv v) t
                  with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `ee' = ee with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` >>
  `not_local_ptr c ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `val_in_memory tyv v (w2n w)
     (mstore (w2n w) (typed_val_to_w256 etv v) t).vs_memory /\
   val_wf tyv v /\ type_memory_size tyv = 32` by fs[store_lays_out_def] >>
  `memory_value_rel tyv v (w2n w)
     (mstore (w2n w) (typed_val_to_w256 etv v) t).vs_memory` by
    (`word_memory_type tyv` by fs[store_lays_out_def] >>
     metis_tac[loweringSliceTheory.word_memory_type_memory_value_rel]) >>
  `stmt_state_rel ctx func c cx ee' u` by
    (simp[Abbr `u`, Abbr `ee'`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_declare_store >> simp[] >>
     qexists_tac `mk_inst st.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv vtyp))] [p]` >>
     gvs[mk_inst_def]) >>
  `!x. lookup_var x u = lookup_var x t` by
    simp[Abbr `u`, lookup_var_def, mstore_def, LET_THM] >>
  `sb.cs_current_bb = sB.cs_current_bb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    gvs[Abbr `u`, mstore_def, LET_THM] >>
  qexistsl_tac [`ee'`, `u`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      simp[Abbr `ee'`]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `lower_value _ _ _ _ sA = _`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     qpat_x_assum `emit_void MSTORE _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     qpat_x_assum `emit_inst ALLOCA _ _ _ = _`
       (strip_assume_tac o MATCH_MP emit_inst_extends) >>
     gvs[]) >>
  `!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
          lookup_var x u = SOME w'` by
    metis_tac[] >>
  `cenv_top_ext cenv c ee'.scopes` by
    (simp[Abbr `ee'`] >> irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa`, `st`, `vtyp`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d c sb u` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  simp[stmt_lands_def]
QED
