(* Counted memory simulation of a declaration of a memory-backed type that
   is not a bytestring, from a value of that type: the local's ALLOCA, the
   right-hand side, and the copy of its value into the local, staged
   through a buffer of its own when the value is in memory.  The memory
   twin of stmtSimDeclMem's compile_annassign_memory_stmt_frag. *)
Theory bodyDeclCopyMemory
Ancestors
  bodyDeclMemoryCompose bodyDeclMemoryCounted bodyDeclMemoryCore
  stmtSimDeclCompose stmtSimDeclSource stmtSimDeclStore stmtSimDeclMem
  stmtSimDecl exprSimMemDefs exprSimProps bodyMemoryDefs fragGasMode
  fragGasPathMem fragGasPath gasSummary gasOutcome loweringPosts exprSimDefs stmtSimDefs
  stmtSimProps loweringSlice exprLoweringProps exprOperandVar localPtrsProps
  freshWrites valueTypingMemoryProps emitHelper emitHelperProps fragExec
  venomInst venomState exprLowering stmtLowering context compileEnv vyperInterpreter
  vyperState list rich_list finite_map
Libs monadsyntax

Theorem declare_local_memory_types_mem:
  !cenv id vtyp sa c st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals ==>
    (!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
    (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  conj_tac
  >- (`!env ty. env.ce_struct_fields = cenv.ce_struct_fields ==>
          type_memory_bytes env ty = type_memory_bytes cenv ty` suffices_by
        metis_tac[] >>
      ho_match_mp_tac type_memory_bytes_ind >>
      rw[type_memory_bytes_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[]) >>
  gen_tac >> gvs[oneline lowered_value_type_def]
QED

Theorem annassign_copy_parts_mem:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sA = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >>
  gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem val_store_size_type_size[local]:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_store_size tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      is_bytestring_type_def]
QED

(* A value of a type that takes memory has a footprint. *)
Theorem val_store_size_pos:
  !tv v. 0 < type_memory_size tv ==> 0 < val_store_size tv v
Proof
  rw[val_store_size_def] >> BasicProvers.every_case_tac >> simp[]
QED

(* The copy into a declared local after its right-hand side, from the
   state t that the right-hand side's fragment ends in.  A value staged
   through its own buffer is read at its type's size, which the premise on
   a memory-located value bounds. *)
Theorem annassign_copy_post_path_mem:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v tyv vtyp
   sc rest a loc bytes d.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    post_value_type cenv e = expr_type e /\
    expr_store_bound cx vtyp v op s /\
    (loc = SOME LocMemory ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size tyv <= s.vs_alloca_next) /\
    lower_value compile_expr cenv vtyp e sa = (op,sb) /\
    local_ptrs_reserved cenv sa /\
    ~is_word_type vtyp /\ expr_type e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    value_has_type tyv v /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    compile_assign_value cenv (Var p) LocMemory op F loc vtyp vtyp bytes sb =
      ((),sf) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv sb s /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es1 with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v;
                        popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sf t /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> drule_all (GEN_ALL compile_lower_value_var) >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `val_wf tyv v` by simp[value_has_type_memory_wf] >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory tyv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `w2n sw + val_store_size tyv v <= s.vs_alloca_next` by
    (`0 < val_store_size tyv v` by simp[val_store_size_pos] >>
     qpat_x_assum `expr_store_bound _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     disch_then (qspecl_then [`tyv`, `sw`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  Cases_on `loc = SOME LocMemory`
  >- (gvs[] >>
      drule annassign_memory_assign_body_path >>
      disch_then (qspecl_then [`ctx`, `func`, `cx`, `es1`, `s`, `id`, `sz`,
        `w`, `inst`, `v`, `tyv`, `sc`, `rest`, `a`, `sw`, `d`] mp_tac) >>
      simp[]) >>
  `compile_store_memory cenv op (Var p) vtyp vtyp sb = ((),sf)` by
    gvs[compile_assign_value_def] >>
  drule annassign_memory_store_body_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es1`, `s`, `id`, `sz`,
    `w`, `inst`, `v`, `tyv`, `sc`, `rest`, `a`, `sw`, `d`] mp_tac) >>
  simp[]
QED

(* x: T = e for a memory-backed type T that is not a bytestring, where e
   has type T, is lowered at T and is not the empty-value form, and its
   values (read through read_result when e is a place) have type T.  The
   local's buffer is type_memory_bytes of T, the size val_in_memory lays a
   value of T out in, which is not 0 and leaves the 64 bytes of a copy's
   rounding below 2 ** 256. *)
Theorem compile_annassign_copy_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id vtyp e es tyv.
    cenv.ce_alloca_locals /\
    ~is_word_type vtyp /\ ~is_bytestring_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!gs v es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL v, es1) ==> value_has_type tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim_mem ctx func c cx (expr_type e) e es) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type e = vtyp` (SUBST_ALL_TAC o SYM) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id (expr_type e) sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. _ ==> expr_sim_mem _ _ _ _ _ _ _` drule >>
  strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by metis_tac[] >>
  drule_all annassign_copy_parts_mem >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `!ty. type_memory_bytes c ty = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!e. lowered_value_type c e = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `lowered_value_type cenv e = _` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `cs_extends sA sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[compile_assign_memory_appends, cs_appends_def] >>
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
  `type_memory_bytes cenv (expr_type e) < dimword (:256)` by decide_tac >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  drule annassign_admissible_type >> strip_tac >>
  `tyv' = tyv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv' = tyv` SUBST_ALL_TAC >>
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
    (drule_at (Pos last) compile_assign_value_memory_same_open >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sA x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     drule emit_inst_extends >> simp[]) >>
  irule annassign_rhs_outcome_mem >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  qexists_tac `tyv` >>
  qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME tyv`
    (fn th => simp[PULL_EXISTS, th]) >>
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `value_has_type tyv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `!sw. eval_operand op t = SOME sw ==>
        w2n sw + type_memory_size tyv <= t.vs_alloca_next` by
    (rpt strip_tac >>
     `val_store_size tyv v = type_memory_size tyv` by
       metis_tac[val_store_size_type_size] >>
     qpat_x_assum `expr_store_bound _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     disch_then (qspecl_then [`tyv`, `sw`] mp_tac) >> gvs[]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas st.cs_next_id =
     SOME (w2n w, type_memory_bytes cenv (expr_type e)) /\
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
    [Lit (n2w (type_memory_bytes cenv (expr_type e)))] [p]` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   ai.inst_id = st.cs_next_id` by simp[Abbr `ai`, mk_inst_def] >>
  `lookup_scopes id (sc::rest) = NONE /\ not_local_ptr c (sc::rest) p` by
    metis_tac[] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size tyv)` by
    (qpat_x_assum `FLOOKUP t.vs_allocas st.cs_next_id = _` mp_tac >> simp[]) >>
  `post_value_type c e = expr_type e` by
    (`lowered_value_type c e = expr_type e` by simp[] >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
     Cases_on `e` >> gvs[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
  drule annassign_copy_post_path_mem >>
  disch_then (qspecl_then [`sb`, `id`, `p`,
    `type_memory_bytes cenv (expr_type e)`, `w`, `ai`, `tyv`,
    `expr_type e`, `sc`, `rest`, `T`, `vv_location vv`] mp_tac) >>
  disch_then (qspecl_then [`type_memory_bytes cenv (expr_type e)`, `d`] mp_tac) >>
  impl_tac
  >- (simp[] >> fs[]) >>
  disch_then (qx_choose_then `tf:venom_state` strip_assume_tac) >>
  qabbrev_tac `ee' = ee with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` >>
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
     qexistsl_tac [`id`, `sa`, `sa with cs_next_var := sa.cs_next_var + 1`,
                   `expr_type e`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `return_buf_frame d c sb tf` by simp[] >>
  `stmt_state_rel ctx func c cx ee' tf` by
    (qunabbrev_tac `ee'` >>
     qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (ee with scopes := scs) _` >>
     `ee with <|scopes := scs; gas_obs := []|> =
      (ee with scopes := scs) with gas_obs := []`
       by simp[evaluation_state_component_equality] >>
     metis_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  simp[stmt_lands_def]
QED
