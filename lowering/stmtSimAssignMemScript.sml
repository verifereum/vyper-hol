(*
 * Statement simulation: Assign to a memory-backed local (#637)
 *
 * x = e for a local x already in scope whose type is not a word type (an
 * aggregate, a bytestring), where e is lowered at x's type.
 * compile_assign_value copies e's bytes into x's region, staged through a
 * buffer of its own when e's value is in memory (so x = x and values that
 * overlap x copy correctly), as for a declaration (stmtSimDeclMem).
 *
 * TOP-LEVEL:
 *   stmt_env_assign                        — Assign declares nothing
 *   local_memory_store_run                 — compile_store_memory into a
 *                                            live local
 *   compile_assign_local_memory_stmt_frag  — x = e for a memory-backed
 *                                            local x, every outcome
 *)

Theory stmtSimAssignMem
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclStore
  stmtSimDecl stmtSimDeclMem stmtSimAssignStore stmtSimAssign
  valueCopy valueCopySource valueCopyBytes exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax

Theorem stmt_env_assign:
  !cenv lctx ty g e sa c sf.
    stmt_env cenv lctx ty (Assign g e) sa = (c, sf) ==>
    c = cenv /\ compile_stmt cenv lctx ty (Assign g e) sa = ((), sf)
Proof
  rpt gen_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (Assign g e) sa` >>
  rename1 `(u, _)` >> Cases_on `u` >> simp[]
QED

(* The code of x = e for a memory-backed local x: e's value, then
   compile_assign_value into x's pointer at x's type. *)
Theorem assign_local_memory_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = vtyp /\ fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp vtyp
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op, sB)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sB` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sB sf` by
    metis_tac[compile_assign_memory_appends, cs_appends_def] >>
  `fn_has_code sa sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  gvs[]
QED

(* A write within a live local is disjoint from initialized immutables. *)
Theorem local_copy_immutables[local]:
  stmt_state_rel func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ n <= sz /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a len. a + len <= b \/ b + n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[] >> reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ id b sz ==> _` drule >> simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

(* compile_store_memory at ty of a value of the local's type, held in
   memory at src, into a live local: it reaches its end related at the
   scopes write_place leaves. *)
Theorem local_memory_store_run_framed:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv sty stv.
    compile_store_memory cenv src (Var p) ty sty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!a len. a + len <= w2n dw \/
           w2n dw + MIN (type_memory_size stv) (type_memory_size tyv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  `if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_run_source_bound_with_capacity >> strip_tac >>
  `!a len. a + len <= w2n w \/ w2n w + type_memory_size tyv <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  qpat_x_assum `ty = sty \/ _` kall_tac >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `entry.type = tyv` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel func cenv cx es1` >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`func`, `type_memory_size entry.type`] >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
     decide_tac) >>
  `stmt_state_rel func cenv cx es1 t` by
    (drule_all stmt_state_rel_write_local >> simp[Abbr `es1`]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `frag_exec ctx sa sb (\u. u = s)
     (\u. stmt_state_rel func cenv cx es1 u /\
          (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
          u.vs_allocas = s.vs_allocas /\
          (!a len. a + len <= w2n w \/
             w2n w + MIN (type_memory_size stv) (type_memory_size entry.type) <= a ==>
             mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory))
     (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, lookup_var_def] >> simp[stmt_state_rel_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  drule frag_exec_no_exit_run >>
  disch_then (qspecl_then [`func`, `s`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `u` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem local_memory_store_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (local_memory_store_run_framed |> SPEC_ALL
    |> Q.INST [`sty` |-> `ty`, `stv` |-> `tyv`]
    |> GEN_ALL |> PURE_REWRITE_RULE [REFL_CLAUSE, OR_CLAUSES, AND_CLAUSES]) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> qexists_tac `fuel` >> simp[]
QED

(* compile_assign_value at the local's memory type: staged through a fresh
   buffer when the source is in memory, then compile_store_memory. *)
Theorem local_memory_assign_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv
   loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty ty info bytes sa =
      ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >> Cases_on `loc = SOME LocMemory`
  >- (pop_assum SUBST_ALL_TAC >>
      `0 < type_memory_bytes cenv ty` by simp[] >>
      drule_all annassign_staged_memory_parts >>
      disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
      `MEM (mk_inst sx.cs_next_id ALLOCA
          [Lit (n2w (type_memory_bytes cenv ty))] [tmp]) (fn_insts func)` by
        (drule emit_inst_extends >> strip_tac >>
         `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
                isPREFIX sm.cs_current_insts bb.bb_instructions` by
           metis_tac[fn_has_code_start] >>
         `MEM (mk_inst sx.cs_next_id ALLOCA
           [Lit (n2w (type_memory_bytes cenv ty))] [tmp]) bb.bb_instructions` by
           gvs[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[lookup_block_fn_insts]) >>
      `not_local_ptr cenv es.scopes tmp` by
        (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
      `src <> Var tmp` by metis_tac[] >>
      `type_memory_bytes cenv ty < dimword (:256)` by simp[] >>
      `val_footprint tyv v <= type_memory_bytes cenv ty` by
        metis_tac[val_footprint_le] >>
      `s.vs_current_bb = sx.cs_current_bb /\
       s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
      drule_all alloc_copy_memory_framed_run >>
      disch_then (qspec_then `ctx`
        (qx_choosel_then [`u`, `uw`] strip_assume_tac)) >>
      `local_ptrs_reserved cenv sn` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
      `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
      `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
      drule_all local_memory_store_run >>
      disch_then (qspec_then `ctx` mp_tac) >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sn x` by
            (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          `x <> tmp` by metis_tac[] >> simp[]) >>
      metis_tac[]) >>
  `compile_store_memory cenv src (Var p) ty ty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  drule_all local_memory_store_run >>
  disch_then (qspec_then `ctx` ACCEPT_TAC)
QED

(* On a value: e's fragment ends in expr_post with the value in memory at
   its operand, and the assignment writes it into x. *)
Theorem assign_local_memory_success_run:
  !ctx func cenv cx id e es es' tyv sa sb sf op p sz s0 loc info bytes.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (INL (), es') /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      (expr_type e) (expr_type e) info bytes sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_assign_local >> simp[] >> strip_tac >>
  Cases_on `r` >> gvs[] >>
  rename1 `write_place cx (MemoryPlace id []) v es1 = (INL (), es')` >>
  drule write_place_local >> simp[] >> strip_tac >> gvs[] >>
  `lookup_scopes id es1.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv /\ value_has_type tyv v` by metis_tac[] >>
  drule_then (drule_then assume_tac) compile_lower_value_var >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `val_wf tyv v` by gvs[expr_val_at_def] >>
  `?sw. eval_operand op s1 = SOME sw /\
        val_in_memory tyv v (w2n sw) s1.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all local_memory_assign_run >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

(* x = e for a local x whose type T is not a word type, where e has type T,
   is lowered at T (lowered_value_type, so not a bytestring literal of
   another length) and is not the empty-value form the lowering stores as
   a zero length word, and e's value has the type of x's scope entry.  The
   size conditions are compile_annassign_memory_stmt_frag's: T's buffer is
   type_memory_bytes of T, the size val_in_memory lays a value of T out
   in, not 0, and 64 bytes below 2 ** 256.  expr_type e = T leaves out
   assignments that widen e's value to T. *)
Theorem compile_assign_local_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es res es' p sz vtyp tyv.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type e = vtyp` (SUBST_ALL_TAC o SYM) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_memory_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  Cases_on `res`
  >- (rename1 `eval_stmt _ _ _ = (INL u, _)` >> Cases_on `u` >>
      drule_all assign_local_memory_success_run >> strip_tac >>
      disj1_tac >> qexistsl [`t`, `cenv`] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      `0 < type_memory_bytes cenv (expr_type e)` by simp[] >>
      drule_all compile_assign_value_memory_same_open >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
        (qspec_then `fuel` mp_tac) >> simp[]) >>
  rename1 `eval_stmt _ _ _ = (INR y, _)` >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INR y, es') /\
   expr_res_ok (INR y : value + exception)` by
    (drule eval_assign_local_error >> disch_then drule >> simp[]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED
