(* Typed widening at a memory-backed declaration. *)
Theory stmtSimDeclTyped
Ancestors
  stmtSimDeclTypedAssign stmtSimDeclSourceSeparation stmtSimDeclTypedCode
  stmtSimDeclMem stmtSimDeclSource stmtSimDeclCompose stmtSimDeclPath stmtSimDecl
  emitHelperProps exprOpenTerminals
  stmtSimProps exprSimProps stmtSimDefs exprSimDefs loweringPosts
  externalNormalizePremises exprLoweringProps exprOperandVar freshWrites
  valueTypingMemoryProps loweringStateRelDefs venomMemDefs
  localPtrsProps compileEnv finite_map vyperInterpreter vyperState
  venomExecSemantics venomInst venomState gasSummary fragGasPath gasContext fragGasMode
Libs monadsyntax

Theorem annassign_typed_store_post_path:
  expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
  post_value_type cenv e = expr_type e /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  cs_extends sa sb /\ local_ptrs_reserved cenv sa /\ (!l. op <> Label l) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ expr_type e <> dty /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
  type_memory_size stv < dimword (:256) /\ type_memory_size dtv <= sz /\
  compile_assign_value cenv (Var p) LocMemory op F loc dty (expr_type e)
    bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
  lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  inst.inst_id < sa.cs_next_id /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx
        (es1 with scopes :=
          (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
        lookup_var x t = SOME u) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid off z. FLOOKUP s.vs_allocas aid = SOME (off,z) /\
         aid <> inst.inst_id /\ aid < sb.cs_next_id ==>
         mem_bytes_at off z t.vs_memory = mem_bytes_at off z s.vs_memory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (drule_then assume_tac) compile_lower_value_var >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[normalize_return_source_kinds] >>
  `val_wf stv v /\ val_wf dtv v` by simp[value_has_type_memory_wf] >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz)` by metis_tac[] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sb p /\ local_ptrs_reserved cenv sb` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (`w2n w + sz <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
        qpat_x_assum `!aid base sz. _ ==> _ <= s.vs_alloca_next` drule >> decide_tac) >>
     `s.vs_alloca_next < dimword (:256)` by
       (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >> decide_tac) >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[normalize_nonbytes_footprint] >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all normalize_source_window >> simp[]) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (drule expr_val_at_alloca_outside_interval_separate >>
     disch_then (drule_at (Pos (el 2))) >> simp[] >>
     disch_then (qspecl_then [`p`, `sz`, `inst`, `w2n w`] mp_tac) >> gvs[]) >>
  (drule compile_assign_value_typed_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`sz`, `sa`, `inst`, `id`, `a`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> gvs[])) >> strip_tac >>
  qexists `t` >> simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >> metis_tac[])
QED

Theorem annassign_typed_normal_continuation:
  declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
  (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  acyclic_struct_metadata c.ce_struct_fields /\
  sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) (expr_type e) typ /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  lowered_value_type c e = expr_type e /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_memory_bytes c (expr_type e) = type_memory_size etv /\
  type_memory_size etv < dimword (:256) /\ type_memory_size tyv <= sz /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) ==>
     value_has_type tyv v /\ value_has_type etv v) /\
  local_ptrs_reserved c sa /\ cs_extends sa sb /\ ~block_is_terminated sb /\
  stmt_state_rel ctx func c cx es salloc /\
  sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
  sa0.cs_next_var <= sa.cs_next_var /\
  (!l. op <> Label l) /\
  lower_value compile_expr c (expr_type e) e sa = (op,sb) /\
  compile_assign_value c (Var p) LocMemory op F loc typ (expr_type e)
    bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
  lookup_var p salloc = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  inst.inst_id < sa.cs_next_id /\
  FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,salloc) marks (INL v) ee (OK s) /\
  expr_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
    (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
    stmt_post ctx func cx lctx old c sa0 sf es salloc (INL ()) ff u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `value_has_type tyv v /\ value_has_type etv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `not_local_ptr c (ee with gas_obs := []).scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `cenv_top_ext old c
    ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)` by
    (irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl [`id`, `sa0`, `st`, `typ`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `~block_is_terminated sf` by
    (irule compile_assign_value_typed_open >> goal_assum (drule_at Any) >>
     fs[cs_extends_def]) >>
  `post_value_type c e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `(ee with gas_obs := []).scopes = sc :: rest /\
   lookup_scopes id (ee with gas_obs := []).scopes = NONE` by gvs[] >>
  drule_all annassign_typed_store_post_path >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame c es sa salloc c (ee with gas_obs := []) s` by
    (irule expr_post_alloca_frame >> metis_tac[]) >>
  `venomMemDefs$allocas_non_overlapping s /\ lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
   (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
            FLOOKUP s.vs_allocas aid = SOME b)` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     metis_tac[]) >>
  `sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `local_ptrs_reserved c sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `!aid off z'. FLOOKUP s.vs_allocas aid = SOME (off, z') /\ aid < sa0.cs_next_id ==>
     mem_bytes_at off z' t.vs_memory = mem_bytes_at off z' s.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!aid off z. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` irule >>
     qexists_tac `aid` >> rpt conj_tac >- decide_tac >- decide_tac >>
     first_assum ACCEPT_TAC) >>
  `((ee with gas_obs := []) with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest).scopes =
   (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` by
    simp[] >>
  `alloca_frame old es sa0 salloc c ((ee with gas_obs := []) with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (mp_tac (Q.INST [`ee` |-> `(ee with gas_obs := []) with scopes :=
         (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`,
       `es1` |-> `ee with gas_obs := []`,
       `s0` |-> `salloc`, `aid0` |-> `inst.inst_id`, `z` |-> `sz`,
       `entry` |-> `<|assignable := T; type := tyv; value := v; popped := []|>`,
       `sa1` |-> `sb`] alloca_frame_declare_local_store) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  `!x u. not_fresh_at sa0 x /\ lookup_var x salloc = SOME u ==>
         lookup_var x t = SOME u` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sa x` by
       (qpat_x_assum `not_fresh_at sa0 x` mp_tac >> rw[not_fresh_at_def] >>
        first_x_assum irule >> simp[]) >>
     metis_tac[]) >>
  qexistsl_tac [`ee with <|gas_obs := []; scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>`, `t`] >>
  conj_tac
  >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ (ee with scopes := scs) _` >>
  `ee with <|scopes := scs; gas_obs := []|> =
   (ee with scopes := scs) with gas_obs := []`
    by simp[evaluation_state_component_equality] >>
  `ee with <|scopes := scs; gas_obs := []|> =
   (ee with gas_obs := []) with scopes := scs`
    by simp[evaluation_state_component_equality] >>
  qpat_x_assum `ee with <|scopes := scs; gas_obs := []|> =
                (ee with scopes := scs) with gas_obs := []`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (REWRITE_RULE [exprSimWordArgsTheory.stmt_state_rel_gas_obs,
                                alloca_frame_gas_obs]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem compile_annassign_typed_widen_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id typ e es etv tyv.
    cenv.ce_alloca_locals /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
    ~(has_length_word typ /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = expr_type e /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) (expr_type e) typ /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    type_memory_bytes cenv typ = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv < dimword (:256) /\
    type_memory_bytes cenv (expr_type e) = type_memory_size etv /\
    type_memory_size etv < dimword (:256) /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==>
       value_has_type tyv v /\ value_has_type etv v) /\
    (!st0 c st1. declare_local cenv id typ st0 = (c,st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       (!sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
          cs_extends sa sb /\ (!l. op <> Label l))) /\
    (!st c st1. declare_local cenv id typ st = (c,st1) ==>
       !gs sa vv sb tv es1.
         storage_vars_rel c cx /\ transient_vars_rel c cx /\
         eval_expr cx e (es with gas_obs := gs) = (INL tv,es1) /\
         compile_expr c (expr_type e) e sa = (vv,sb) /\
         ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `!st0 c st1. declare_local cenv id typ st0 = (c,st1) ==>
     !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
       cs_extends a b` by metis_tac[] >>
  drule_all annassign_typed_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sV`, `sB`, `vv`, `op`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id typ sa = (c,st)` >>
  `expr_sim ctx func c cx (expr_type e) e es /\ (!l. op <> Label l)` by metis_tac[] >>
  drule_all bodyDeclCopyMemoryTheory.declare_local_memory_types_mem >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (drule_all declare_local_ptr >> strip_tac >>
     fs[compile_env_component_equality]) >>
  `stmt_state_rel ctx func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  `type_memory_bytes cenv typ < dimword (:256)` by simp[] >>
  drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,salloc)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func c cx e es sA sB salloc ee v op t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_def] >> disch_then irule >> simp[]) >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w, type_memory_bytes cenv typ)` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
    (`sA.cs_next_var = st.cs_next_var` by
       (drule emit_inst_extends >> simp[]) >>
     drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
  `sa.cs_next_id <= ai.inst_id /\ sa.cs_next_id <= sA.cs_next_id /\
   sa.cs_next_var <= sA.cs_next_var` by
    (drule_all declare_local_ptr >> strip_tac >>
     qpat_x_assum `emit_inst ALLOCA _ _ _ = _` assume_tac >>
     drule emit_inst_extends >>
     simp[Abbr `ai`, venomInstTheory.mk_inst_def]) >>
  irule annassign_outcome_entry_prefix >>
  simp[] >> qexists_tac `salloc` >> simp[] >>
  irule annassign_rhs_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
    (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
    stmt_post ctx func cx lctx cenv c sa sb es salloc (INL ()) ff u` suffices_by
    (strip_tac >> qexistsl_tac [`ff`, `u`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_post_def, stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def,
          alloca_frame_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~block_is_terminated sA` by
    (drule emit_inst_nonterminator_open >> simp[is_terminator_def]) >>
  `?tv es1. eval_expr cx e
      (es with gas_obs := gas_explicit marks salloc.vs_gas_readings) = (INL tv,es1)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `storage_vars_rel c cx /\ transient_vars_rel c cx` by
    (qpat_assum `stmt_state_rel _ _ c _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  `~block_is_terminated sV` by metis_tac[] >>
  `~block_is_terminated sB` by metis_tac[unwrap_value_open] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  irule annassign_typed_normal_continuation >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any o SRULE []) >>
  simp[] >>
  qexistsl_tac [`marks`, `ai`] >> simp[] >>
  `ai.inst_id < sA.cs_next_id` by
    (simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
     drule emit_inst_extends >> simp[]) >>
  metis_tac[]
QED
