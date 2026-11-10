(* Source/gas composition for the typed declaration relayout boundary. *)
Theory annassignRelayoutCompose
Ancestors
  annassignRelayoutContinue stmtSimDeclCompose stmtSimDeclSource
  stmtSimDefs gasOutcome fragGasMode fragGasPath exprSimWordArgs
  gasSummary gasSummaryCompose vyperInterpreter vyperState venomState
  valueEncoding finite_map list exprLoweringProps
  context compileEnv stmtLowering loweringPosts
Libs monadsyntax

Theorem annassign_relayout_normal_continuation:
  !ctx func old c cx lctx id typ tyv e es stv sty sa0 st sa sb sf salloc
   marks v ee s op p sz w inst loc bytes.
    declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
    (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    post_value_type c e = sty /\ sty <> expr_type e /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\ ~is_word_type sty /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type tyv v /\
       val_wf stv v /\ val_wf tyv v /\ val_footprint stv v = type_memory_size stv) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\ local_ptrs_reserved c sa /\
    stmt_state_rel ctx func c cx es salloc /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ typ <> sty /\
    acyclic_struct_metadata c.ce_struct_fields /\
    sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty typ /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    type_memory_bytes c sty = type_memory_size stv /\
    type_memory_bytes c sty < dimword (:256) /\ type_memory_size tyv <= sz /\
    compile_assign_value c (Var p) LocMemory op F loc typ sty bytes sb = ((),sf) /\
    (loc = NONE \/ loc = SOME LocMemory) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id < sa.cs_next_id /\
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,salloc) marks (INL v) ee (OK s) /\
    expr_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      stmt_post ctx func cx lctx old c sa0 sf es salloc (INL ()) ff u
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `value_has_type stv v /\ value_has_type tyv v /\ val_wf stv v /\
   val_wf tyv v /\ val_footprint stv v = type_memory_size stv` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `not_local_ptr c (ee with gas_obs := []).scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `cenv_top_ext old c
    ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)` by
    (irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa0`, `st`, `typ`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `~block_is_terminated sf` by
    (drule_all compile_assign_memory_relayout_open >> simp[]) >>
  `(ee with gas_obs := []).scopes = sc :: rest /\
   lookup_scopes id (ee with gas_obs := []).scopes = NONE` by (simp[] >> metis_tac[]) >>
  drule_all annassign_relayout_store_post_path >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame c es sa salloc c (ee with gas_obs := []) s` by
    (irule expr_post_alloca_frame >> metis_tac[]) >>
  `venomMemDefs$allocas_non_overlapping s /\ lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
   (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
            FLOOKUP s.vs_allocas aid = SOME b)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rpt conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ s`
           (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
         first_assum ACCEPT_TAC)
     >- metis_tac[]
     >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved c sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  qpat_x_assum `FLOOKUP c.ce_vars id = SOME (PtrVar (Var (STRING _ _)) _)` kall_tac >>
  `!aid off z. FLOOKUP s.vs_allocas aid = SOME (off,z) /\ aid < sa0.cs_next_id ==>
     mem_bytes_at off z t.vs_memory = mem_bytes_at off z s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!aid off z. _ ==> mem_bytes_at off z t.vs_memory = _`
       (qspecl_then [`aid`, `off`, `z`] mp_tac) >>
     `aid <> inst.inst_id /\ aid < sb.cs_next_id` by decide_tac >> simp[]) >>
  `alloca_frame old es sa0 salloc c ((ee with gas_obs := []) with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (irule (Q.INST [`aid0` |-> `inst.inst_id`, `sa1` |-> `sb`]
      alloca_frame_declare_local_store) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz)`)) >>
     goal_assum (drule_at (Pat `lookup_var p s = SOME w`)) >>
     simp[] >> qexists_tac `<|assignable := T; type := tyv; value := v; popped := []|>` >> simp[] >> qexistsl_tac [`inst`, `sb`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `!x u. not_fresh_at sa0 x /\ lookup_var x salloc = SOME u ==>
         lookup_var x t = SOME u` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sa x` by
       (qpat_x_assum `not_fresh_at sa0 x` mp_tac >> rw[not_fresh_at_def] >>
        first_x_assum irule >> simp[]) >>
     metis_tac[]) >>
  qexistsl_tac [`ee with <|gas_obs := []; scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>`, `t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
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

Theorem annassign_relayout_rhs_outcome:
  !ctx func old c cx lctx RetQ id typ tyv e es stv sty sa0 st sa sb sf salloc
   op p sz w inst loc bytes.
    declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
    (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    post_value_type c e = sty /\ sty <> expr_type e /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\ ~is_word_type sty /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type tyv v /\
       val_wf stv v /\ val_wf tyv v /\ val_footprint stv v = type_memory_size stv) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\ local_ptrs_reserved c sa /\
    stmt_state_rel ctx func c cx es salloc /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ typ <> sty /\
    acyclic_struct_metadata c.ce_struct_fields /\
    sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty typ /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    type_memory_bytes c sty = type_memory_size stv /\
    type_memory_bytes c sty < dimword (:256) /\ type_memory_size tyv <= sz /\
    compile_assign_value c (Var p) LocMemory op F loc typ sty bytes sb = ((),sf) /\
    (loc = NONE \/ loc = SOME LocMemory) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id < sa.cs_next_id /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,salloc)
      (\res ee t. ?v. res = INL v /\
        expr_post ctx func c cx e es sa sb salloc ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (stmt_post ctx func cx lctx old c sa0 sf es salloc)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule annassign_rhs_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_all annassign_relayout_normal_continuation >> strip_tac >>
  qexistsl_tac [`ff`, `u`] >> simp[stmt_post_end_gas_obs]
QED
