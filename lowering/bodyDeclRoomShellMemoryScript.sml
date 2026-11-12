(* Room-aware declaration shell, independent of the store implementation. *)
Theory bodyDeclRoomShellMemory
Ancestors
  bodyDeclCopyMemory bodyRhsRoomMemory bodyDeclMemoryCompose bodyDeclMemoryCounted
  externalEntryShape exprOpenCopies
  stmtSimDeclCompose stmtSimDeclSource stmtSimDeclStore stmtSimDeclMem
  stmtSimDecl exprSimMemDefs exprSimProps bodyMemoryDefs fragGasMode
  fragGasPathMem fragGasPath gasSummary gasOutcome loweringPosts exprSimDefs stmtSimDefs
  stmtSimProps loweringSlice exprLoweringProps exprOperandVar localPtrsProps
  freshWrites valueTypingMemoryProps emitHelper emitHelperProps fragExec
  venomInst venomState exprLowering stmtLowering context compileEnv vyperInterpreter
  vyperState list rich_list finite_map
Libs monadsyntax

Theorem compile_annassign_room_rel_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id dt e es dtv stv.
    cenv.ce_alloca_locals /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dt /\ ~is_bytestring_type dt /\
    ~is_word_type (expr_type e) /\
    ~(has_length_word dt /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) dt = SOME dtv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    type_memory_size stv < 2 ** 64 /\
    (!gs v es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL v, es1) ==> value_has_type dtv v /\ value_has_type stv v) /\
    (!st0 c st1. declare_local cenv id dt st0 = (c, st1) ==>
       post_value_type c e = expr_type e /\
       expr_vv_sim_mem ctx func c cx (expr_type e) e es /\
       (!gs v ee sA op sB.
          bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
          lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
          ~block_is_terminated sA /\ storage_vars_rel c cx /\
          transient_vars_rel c cx ==> ~block_is_terminated sB)) /\
    (!c sa st sA sB sf op vv salloc ee v s p w inst sc rest info bytes.
       declare_local cenv id dt sa = (c,st) /\
       expr_post ctx func c cx e es sA sB salloc ee v op s /\
       expr_store_bound cx (expr_type e) v op s /\
       (vv_location vv = SOME LocMemory ==>
         !sw. eval_operand op s = SOME sw ==>
           type_memory_size stv = 0 \/
           w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
       lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
       local_ptrs_reserved c sA /\
       value_has_type dtv v /\ value_has_type stv v /\
       compile_assign_value c (Var p) LocMemory op F (vv_location vv)
         dt (expr_type e) info bytes sB = ((),sf) /\
       fn_has_code sB sf func /\ fn_inst_ids_distinct func /\
       alloca_history func s /\ return_buf_frame d c sB s /\
       ~s.vs_halted /\ s.vs_current_bb = sB.cs_current_bb /\
       s.vs_inst_idx = LENGTH sB.cs_current_insts /\
       ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
       FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv dt)) /\
       not_local_ptr c ee.scopes p /\ not_fresh_at sA p /\
       lookup_var p s = SOME w /\
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [p] /\ inst.inst_id < sA.cs_next_id /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,type_memory_bytes cenv dt) /\
       w2n w + type_memory_size dtv <= s.vs_alloca_next ==>
       ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
         t.vs_current_bb = sf.cs_current_bb /\
         t.vs_inst_idx = LENGTH sf.cs_current_insts /\
         stmt_state_rel ctx func c cx
           (ee with scopes :=
             (sc |+ (id, <|assignable := T; type := dtv; value := v; popped := []|>)) :: rest) t /\
         alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
         return_buf_frame d c sf t /\
         (!x. not_fresh_at sB x ==> lookup_var x t = lookup_var x s) /\
         (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                  FLOOKUP t.vs_allocas aid = SOME b)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id dt e))
      (eval_stmt cx (AnnAssign id dt e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id dt sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ expr_vv_sim_mem _ _ _ _ _ _ _ /\ _` drule >>
  strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  drule_all annassign_copy_parts_mem >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `!ty. type_memory_bytes c ty = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!e. lowered_value_type c e = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `lowered_value_type cenv e = _` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `cs_extends sA sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`c`, `Var (STRING #"%" (toString sa.cs_next_var))`, `LocMemory`,
       `op`, `F`, `vv_location vv`, `dt`, `expr_type e`,
       `case dt of ArrayT elem_ty (Dynamic _) =>
          SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                type_memory_bytes cenv elem_ty) | _ => NONE`,
       `type_memory_bytes cenv dt`, `sB`] mp_tac compile_assign_value_labels >>
     simp[]) >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sb func` by
    (qspecl_then [`sA`, `sB`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sa sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    metis_tac[] >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by
    simp[] >>
  `type_memory_bytes cenv dt < dimword (:256)` by decide_tac >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  drule annassign_admissible_type >> strip_tac >>
  `tyv = dtv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv = dtv` SUBST_ALL_TAC >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,salloc)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func c cx e es sA sB salloc ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      (vv_location vv = SOME LocMemory ==>
       !sw tvt. eval_operand op t = SOME sw /\
         evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME tvt ==>
         type_memory_size tvt = 0 \/
         w2n sw + type_memory_size tvt <= t.vs_alloca_next) /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts /\
      alloca_history func t /\ salloc.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)` by
    (irule expr_sim_mem_room >> simp[] >>
     conj_tac >- fs[] >>
     qexistsl_tac [`sV`, `expr_type e`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sA x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     drule emit_inst_extends >> simp[]) >>
  irule annassign_rhs_outcome_mem >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  qexists_tac `dtv` >>
  qpat_assum `evaluate_type (get_tenv cx) dt = SOME dtv`
    (fn th => simp[PULL_EXISTS, th]) >>
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `~block_is_terminated sA` by
    (drule exprOpenTerminalsTheory.emit_inst_nonterminator_open >>
     simp[is_terminator_def]) >>
  `storage_vars_rel c cx /\ transient_vars_rel c cx` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [expr_post_def, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `~block_is_terminated sB` by
    (qpat_x_assum `!gs v ee sA op sB. _` irule >>
     metis_tac[]) >>
  `acyclic_struct_metadata c.ce_struct_fields` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  `~block_is_terminated sb` by
    (Cases_on `vv_location vv = SOME LocMemory`
     >- (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
         `~block_is_terminated cs'` by
           metis_tac[exprOpenPrimitivesTheory.compile_alloc_buffer_open] >>
         `~block_is_terminated cs''` by
           (qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
            Cases_on `type_memory_size stv` >>
            simp[compile_copy_memory_def, comp_return_def] >> strip_tac >> gvs[] >>
            drule emit_void_nonterminator_open >>
            simp[is_terminator_def]) >>
         drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) compile_store_memory_open >>
         simp[])
     >> qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def] >> strip_tac >>
     drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) compile_store_memory_open >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `value_has_type dtv v /\ value_has_type stv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas st.cs_next_id =
     SOME (w2n w, type_memory_bytes cenv dt) /\
   salloc.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> metis_tac[]) >>
  `return_buf_frame d c sB t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`c`, `salloc`, `sA`] >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >> simp[] >>
     metis_tac[cj 2 compile_expr_grows]) >>
  `not_local_ptr c ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  qabbrev_tac `ai = mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv dt))] [p]` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   ai.inst_id = st.cs_next_id` by simp[Abbr `ai`, mk_inst_def] >>
  `ai.inst_id < sA.cs_next_id` by
    (drule emit_inst_extends >> simp[]) >>
  `vv_location vv = SOME LocMemory ==>
    !sw. eval_operand op t = SOME sw ==>
      type_memory_size stv = 0 \/
      w2n sw + type_memory_size stv <= t.vs_alloca_next` by
    (rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!c sa st sA sB sf op vv salloc ee v s p w inst sc rest info bytes. _`
    (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts func)`)) >>
  (impl_tac >-
    (qpat_assum `ee.scopes = sc::rest`
       (fn th => rewrite_tac[GSYM th]) >> simp[] >>
     qpat_x_assum `FLOOKUP t.vs_allocas st.cs_next_id = _` mp_tac >> simp[])) >>
  disch_then (qx_choose_then `tf` strip_assume_tac) >>
  qabbrev_tac `ee' = ee with scopes :=
    (sc |+ (id, <|assignable := T; type := dtv; value := v; popped := []|>)) :: rest` >>
  qexistsl_tac [`ee'`, `tf`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      simp[Abbr `ee'`]) >>
  `sA.cs_next_var <= sB.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
          lookup_var x tf = SOME w'` by
    (rpt strip_tac >>
     `not_fresh_at sA x` by metis_tac[] >>
     `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP tf.vs_allocas aid = SOME b` by metis_tac[] >>
  `s0.vs_alloca_next <= tf.vs_alloca_next` by decide_tac >>
  `cenv_top_ext cenv c ee'.scopes` by
    (simp[Abbr `ee'`] >> irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa`, `sa with cs_next_var := sa.cs_next_var + 1`, `dt`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `stmt_state_rel ctx func c cx ee' tf` by
    (qunabbrev_tac `ee'` >>
     qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (ee with scopes := scs) _` >>
     `ee with <|scopes := scs; gas_obs := []|> =
      (ee with scopes := scs) with gas_obs := []`
       by simp[evaluation_state_component_equality] >>
     metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  simp[stmt_lands_def]
QED

(* The original, stronger static interface is retained as a corollary. *)
Theorem compile_annassign_room_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id dt e es dtv stv.
    cenv.ce_alloca_locals /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dt /\ ~is_bytestring_type dt /\
    ~is_word_type (expr_type e) /\
    ~(has_length_word dt /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) dt = SOME dtv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    type_memory_size stv < 2 ** 64 /\
    (!gs v es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL v, es1) ==> value_has_type dtv v /\ value_has_type stv v) /\
    (!st0 c st1. declare_local cenv id dt st0 = (c, st1) ==>
       post_value_type c e = expr_type e /\
       expr_vv_sim_mem ctx func c cx (expr_type e) e es /\
       (!gs v ee sA op sB.
          bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
          lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
          ~block_is_terminated sA ==> ~block_is_terminated sB)) /\
    (!c sa st sA sB sf op vv salloc ee v s p w inst sc rest info bytes.
       declare_local cenv id dt sa = (c,st) /\
       expr_post ctx func c cx e es sA sB salloc ee v op s /\
       expr_store_bound cx (expr_type e) v op s /\
       (vv_location vv = SOME LocMemory ==>
         !sw. eval_operand op s = SOME sw ==>
           type_memory_size stv = 0 \/
           w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
       lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
       local_ptrs_reserved c sA /\
       value_has_type dtv v /\ value_has_type stv v /\
       compile_assign_value c (Var p) LocMemory op F (vv_location vv)
         dt (expr_type e) info bytes sB = ((),sf) /\
       fn_has_code sB sf func /\ fn_inst_ids_distinct func /\
       alloca_history func s /\ return_buf_frame d c sB s /\
       ~s.vs_halted /\ s.vs_current_bb = sB.cs_current_bb /\
       s.vs_inst_idx = LENGTH sB.cs_current_insts /\
       ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
       FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv dt)) /\
       not_local_ptr c ee.scopes p /\ not_fresh_at sA p /\
       lookup_var p s = SOME w /\
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [p] /\ inst.inst_id < sA.cs_next_id /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,type_memory_bytes cenv dt) /\
       w2n w + type_memory_size dtv <= s.vs_alloca_next ==>
       ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
         t.vs_current_bb = sf.cs_current_bb /\
         t.vs_inst_idx = LENGTH sf.cs_current_insts /\
         stmt_state_rel ctx func c cx
           (ee with scopes :=
             (sc |+ (id, <|assignable := T; type := dtv; value := v; popped := []|>)) :: rest) t /\
         alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
         return_buf_frame d c sf t /\
         (!x. not_fresh_at sB x ==> lookup_var x t = lookup_var x s) /\
         (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                  FLOOKUP t.vs_allocas aid = SOME b)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id dt e))
      (eval_stmt cx (AnnAssign id dt e)) es
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_annassign_room_rel_stmt_frag_mem >>
  simp[PULL_EXISTS] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!st0 c st1. declare_local _ _ _ _ = _ ==> _` drule >>
      strip_tac >> simp[] >> rpt gen_tac >> strip_tac >>
      first_x_assum irule >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `!c sa st sA sB sf op vv salloc ee v s p w inst sc rest info bytes. _`
    mp_tac >> simp[arithmeticTheory.ADD_COMM] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
      conj_tac >- (goal_assum (drule_at Any)) >>
      qexistsl_tac [`bytes`, `info`, `inst`, `op`, `sA`, `salloc`, `vv`] >> simp[] >>
      qpat_x_assum `ee.scopes = _` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >> fs[]
QED
