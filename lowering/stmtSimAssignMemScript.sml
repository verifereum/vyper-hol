(*
 * Statement simulation: Assign to a memory-backed local (#637)
 *
 * x = e for a local x already in scope whose type is not a word type (an
 * aggregate, a bytestring).  compile_assign_value copies e's bytes into
 * x's region, staged through a buffer of its own when e's value is in
 * memory (so x = x and values that overlap x copy correctly), as for a
 * declaration (stmtSimDeclMem).  When e is the empty value of a type with
 * a length word, the lowering only zeroes x's length word.
 *
 * TOP-LEVEL:
 *   stmt_env_assign                        — Assign declares nothing
 *   local_memory_store_run                 — compile_store_memory into a
 *                                            live local
 *   compile_assign_local_memory_stmt_frag  — x = e for a memory-backed
 *                                            local x, e lowered at x's
 *                                            type, every outcome
 *   compile_assign_local_memory_widen_stmt_frag — the same where x and e
 *                                            are bytestrings and e's
 *                                            bound may be narrower
 *   compile_assign_local_empty_stmt_frag   — x = e for e the empty value
 *                                            of a type with a length word
 *)

Theory stmtSimAssignMem
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  stmtSimAssignSource stmtSimAssignPath stmtSimAssignCompose stmtSimDeclCompose gasSummaryCompose
  gasOutcome gasExemptCert gasSummary fragGasPath valueTypingMemoryProps
  context fragGasMode fragGasSeq
  fragExec localPtrsProps  loweringSlice  stmtSimDeclStore localMemoryStorePath
  stmtSimDecl stmtSimDeclMem stmtSimAssignStore stmtSimAssign
  stmtSimDeclPath
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
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel ctx func cenv cx
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
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx es1` >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `type_memory_size entry.type` >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
     decide_tac) >>
  `stmt_state_rel ctx func cenv cx es1 t` by
    (drule_all stmt_state_rel_write_local >> simp[Abbr `es1`]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `frag_exec ctx sa sb (\u. u = s)
     (\u. stmt_state_rel ctx func cenv cx es1 u /\
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
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
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
  strip_tac >>
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
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
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
      disch_then
        (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
      `local_ptrs_reserved cenv sn` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
      `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
      `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
      drule_all local_memory_store_run >>
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
  disch_then ACCEPT_TAC
QED

Theorem local_memory_assign_path:
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
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        gas_marked_path F ctx func s 0 (OK t)
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
      drule_all alloc_copy_memory_framed_path >>
      disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
      `local_ptrs_reserved cenv sn` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
      `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
      `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
      drule_all (local_memory_store_path |> SPEC_ALL
        |> Q.INST [`sty` |-> `ty`, `stv` |-> `tyv`]
        |> GEN_ALL |> PURE_REWRITE_RULE [REFL_CLAUSE, OR_CLAUSES, AND_CLAUSES]) >>
      disch_then (qx_choosel_then [`dw`, `t`] strip_assume_tac) >>
      `gas_marked_path F ctx func s 0 (OK t)` by
        (drule_all gas_marked_path_then >> simp[]) >>
      qexists_tac `t` >> simp[] >> rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      `x <> tmp` by metis_tac[] >> simp[]) >>
  `compile_store_memory cenv src (Var p) ty ty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  drule_all (local_memory_store_path |> SPEC_ALL
        |> Q.INST [`sty` |-> `ty`, `stv` |-> `tyv`]
        |> GEN_ALL |> PURE_REWRITE_RULE [REFL_CLAUSE, OR_CLAUSES, AND_CLAUSES]) >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem assign_local_memory_normal_continuation:
  !ctx func cenv cx lctx id e es tyv sa sb sf s0 marks v ee s op p sz loc info bytes.
    gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (stmt_res_ok lctx) es /\
    ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      (expr_type e) (expr_type e) info bytes sb = ((), sf) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sb /\ (!x. op = Var x ==> not_fresh_at sb x) /\
    sa.cs_next_var <= sb.cs_next_var /\ ~block_is_terminated sf /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) marks (INL v) ee (OK s) /\
    expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (write_place cx (MemoryPlace id []) v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff u
Proof
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv /\ value_has_type tyv v` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs v es1 entry. _` drule >>
     disch_then (qspec_then `entry` mp_tac) >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory tyv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `val_wf tyv v` by metis_tac[value_has_type_memory_wf] >>
  `stmt_state_rel ctx func cenv cx ee s` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >> metis_tac[]) >>
  drule_all local_memory_assign_path >> strip_tac >>
  qexistsl_tac [`ee with scopes :=
    pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`, `t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def] >>
  simp[cenv_top_ext_refl] >>
  rpt strip_tac >>
  `not_fresh_at sb x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED

Theorem assign_local_memory_rhs_outcome:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  type_memory_bytes cenv (expr_type e) = type_memory_size tyv /\
  0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
  (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,es1) /\
     lookup_scopes id es1.scopes = SOME entry ==>
     entry.type = tyv /\ value_has_type tyv v) /\
  compile_assign_value cenv (Var p) LocMemory op F loc
    (expr_type e) (expr_type e) info bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\ ~block_is_terminated sf /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >> drule_all assign_local_memory_normal_continuation >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[stmt_post_end_gas_obs] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[gas_exempt_cert_unforce_result]
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
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!gs v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type e = vtyp` (SUBST_ALL_TAC o SYM) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_memory_code_parts >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `0 < type_memory_bytes cenv (expr_type e)` by simp[] >>
  drule_all compile_assign_value_memory_same_open >> strip_tac >>
  drule_then (drule_then assume_tac) compile_lower_value_var >>
  `sa.cs_next_var <= sB.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  irule assign_local_memory_rhs_outcome >>
  qpat_assum `post_value_type _ _ = _` (fn th => simp[th]) >>
  (conj_tac >- gvs[SF ETA_ss]) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >> simp[] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then irule >> simp[]
QED

Theorem assign_local_memory_widen_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
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
    metis_tac[compile_assign_memory_widen_appends, cs_appends_def] >>
  `fn_has_code sa sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >> gvs[]
QED

Theorem local_memory_assign_widen_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sty sa sb sw tyv
   loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty sty info bytes sa = ((), sb) /\
    (sty = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv src (Var p) ty ty sa = ((),sb)` by
    (gvs[compile_assign_value_def] >>
     metis_tac[compile_store_memory_bytestring_src]) >>
  drule_all local_memory_store_run >>
  disch_then ACCEPT_TAC
QED

Resume local_memory_assign_widen_run[staged]:
  pop_assum SUBST_ALL_TAC >>
  drule_all annassign_staged_memory_widen_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
    (drule emit_inst_extends >> strip_tac >>
     `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
            isPREFIX sm.cs_current_insts bb.bb_instructions` by
       metis_tac[fn_has_code_start] >>
     `MEM (mk_inst sx.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) bb.bb_instructions` by
       gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[lookup_block_fn_insts]) >>
  `not_local_ptr cenv es.scopes tmp` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `src <> Var tmp` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  drule_all alloc_copy_memory_framed_run >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
  `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
  drule_all local_memory_store_run >>
  disch_then mp_tac >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      `x <> tmp` by metis_tac[] >> simp[]) >>
  metis_tac[]
QED

Finalise local_memory_assign_widen_run

Theorem local_memory_assign_widen_path:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sty sa sb sw tyv
   loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty sty info bytes sa = ((), sb) /\
    (sty = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv src (Var p) ty ty sa = ((),sb)` by
    (gvs[compile_assign_value_def] >>
     metis_tac[compile_store_memory_bytestring_src]) >>
  drule local_memory_store_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[]
QED

Resume local_memory_assign_widen_path[staged]:
  pop_assum SUBST_ALL_TAC >>
  drule_all annassign_staged_memory_widen_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
    (drule emit_inst_extends >> strip_tac >>
     `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
            isPREFIX sm.cs_current_insts bb.bb_instructions` by
       metis_tac[fn_has_code_start] >>
     `MEM (mk_inst sx.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) bb.bb_instructions` by
       gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[lookup_block_fn_insts]) >>
  `not_local_ptr cenv es.scopes tmp` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `src <> Var tmp` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  drule_all alloc_copy_memory_framed_path >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
  `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
  drule local_memory_store_path >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  simp[] >>
  disch_then (qx_choosel_then [`dw`, `t`] strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      `x <> tmp` by metis_tac[] >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

Finalise local_memory_assign_widen_path

Theorem assign_local_memory_widen_normal_continuation:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  ~is_word_type vtyp /\ post_value_type cenv e = expr_type e /\
  (expr_type e = vtyp \/ is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
  (sty = vtyp \/ is_bytestring_type vtyp) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  evaluate_type (get_tenv cx) vtyp = SOME tyv /\
  type_memory_bytes cenv vtyp = type_memory_size tyv /\
  0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
  0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
  (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) /\
    lookup_scopes id es1.scopes = SOME entry ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv sty) /\
  compile_assign_value cenv (Var p) LocMemory op F loc vtyp sty info bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ ~block_is_terminated sf /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?ff u. gas_marked_exec F (ctx,func) (write_place cx (MemoryPlace id []) v)
    (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv /\ value_has_type tyv v /\
   val_footprint tyv v <= type_memory_bytes cenv sty` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl_tac [`ee with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings ++ []`] >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `val_wf tyv v` by simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `~is_word_type (expr_type e)` by
    (qpat_x_assum `expr_type e = _ \/ _` strip_assume_tac >> gvs[is_bytestring_word_type]) >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory etv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `val_in_memory tyv v (w2n sw) s.vs_memory` by
    (qpat_x_assum `expr_type e = _ \/ _` strip_assume_tac >> gvs[] >>
     irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee s` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all local_memory_assign_widen_path >> strip_tac >>
  qexistsl_tac [`ee with scopes :=
    pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`, `t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem assign_local_memory_widen_rhs_outcome:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  ~is_word_type vtyp /\ post_value_type cenv e = expr_type e /\
  (expr_type e = vtyp \/ is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
  (sty = vtyp \/ is_bytestring_type vtyp) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  evaluate_type (get_tenv cx) vtyp = SOME tyv /\
  type_memory_bytes cenv vtyp = type_memory_size tyv /\
  0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
  0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
  (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) /\
    lookup_scopes id es1.scopes = SOME entry ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv sty) /\
  compile_assign_value cenv (Var p) LocMemory op F loc vtyp sty info bytes sb = ((),sf) /\
  fn_has_code sb sf func /\ ~block_is_terminated sf /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
          qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
          qpat_x_assum `_ = INL v` SUBST_ALL_TAC >>
          drule_all assign_local_memory_widen_normal_continuation >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[stmt_post_end_gas_obs] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[gas_exempt_cert_unforce_result]
QED

Theorem compile_assign_local_memory_widen_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp etv tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (expr_type e = vtyp \/ is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
    (!gs v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v /\
       val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_memory_widen_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `0 < type_memory_bytes cenv vtyp` by simp[] >>
  `~block_is_terminated sb` by
    (drule_all compile_assign_value_memory_widen_open >> simp[]) >>
  `sa.cs_next_var <= sB.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    (drule_then (drule_then assume_tac) compile_lower_value_var >> simp[]) >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_lowered, post_value_type_bytestring] >>
  irule assign_local_memory_widen_rhs_outcome >>
  qpat_assum `post_value_type _ _ = _` (fn th => simp[th]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `tyv` >> simp[] >>
  (conj_tac >- (gvs[SF ETA_ss] >> first_assum ACCEPT_TAC)) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then irule >> simp[]
QED

(* A header-sized write into a live local: the value representation may
   occupy a larger buffer, but only the header needs to be overwritten. *)
Theorem local_header_store_state:
  !func cenv cx es s id p sz w pre env entry rest v wd.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
      (mstore (w2n w) wd s)
Proof
  rpt strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `!a len. a + len <= w2n w \/ w2n w + 32 <= a ==>
     mem_bytes_at a len (mstore (w2n w) wd s).vs_memory =
     mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore (w2n w) wd s)` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`ctx`, `func`, `32`] >>
     simp[immutableMemoryFrameTheory.immutable_mstore_capacity] >>
     first_assum ACCEPT_TAC) >>
  irule stmt_state_rel_write_local >>
  goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  simp[] >> qexistsl_tac [`s`, `w`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[mstore_def, LET_THM, lookup_var_def]
QED

Theorem local_header_store_path:
  !ctx func cenv cx es s id p sz w pre env entry rest v wd sa sb.
    emit_void MSTORE [Var p; Lit wd] sa = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes := pre ++
            (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  drule_all local_header_store_state >> strip_tac >>
  `eval_operand (Lit wd) s = SOME wd` by simp[eval_operand_def] >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists_tac `mstore (w2n w) wd s with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, mstore_def, LET_THM]
QED

Theorem assign_local_empty_code_parts:
  !cenv lctx ty id e sa sf c p sz.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    c = cenv /\ emit_void MSTORE [Var p; Lit 0w] sa = ((), sf)
Proof
  rpt strip_tac >> drule stmt_env_assign >> strip_tac >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM, compile_store_at_loc_def]
QED

Theorem local_header_store_frag:
  !ctx func cenv cx es s id p sz w pre env entry rest v wd sa sb R.
    emit_void MSTORE [Var p; Lit wd] sa = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx
         (es with scopes := pre ++
           (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
         (!x. lookup_var x t = lookup_var x s) /\
         (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                  FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >> drule_all local_header_store_state >> strip_tac >>
  irule (SRULE [] (Q.INST [`keep` |-> `\x. T`]
    (SPEC_ALL annassign_mstore_framed_frag))) >>
  simp[] >> metis_tac[eval_operand_lit]
QED

(* A forced, state-preserving RHS makes the whole local assignment a
   zero-observation scope update, under statement admissibility. *)
Theorem assign_local_identity_rhs_all_tails:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  (!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v, es with gas_obs := gs)) ==>
  ?pre env entry rest.
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    entry.assignable /\
    !tail. eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)
      (es with gas_obs := tail) =
      (INL (), (es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := [] ++ tail) = (INL v, es with gas_obs := tail)` by simp[] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  qexistsl [`pre`, `env`, `entry`, `rest`] >> simp[] >> gen_tac >>
  drule assign_local_admissible_run >>
  disch_then (qspec_then `tail` SUBST1_TAC) >> simp[Once bind_def]
QED

Theorem compile_assign_local_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!gs. (do result <- eval_expr cx e; read_result cx result od)
            (es with gas_obs := gs) =
          (INL (default_value tyv), es with gas_obs := gs)) /\
    (!entry. lookup_scopes id es.scopes = SOME entry ==> entry.type = tyv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_empty_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL (default_value tyv), es with gas_obs := gs)` by
    (gen_tac >> first_x_assum (qspec_then `gs` mp_tac) >>
     simp[bind_def]) >>
  drule_all assign_local_identity_rhs_all_tails >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv` by metis_tac[] >>
  `?w. lookup_var p s0 = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s0).vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    (irule memory_length_word_layout >>
     simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
     qexistsl_tac [`get_tenv cx`, `vtyp`] >> simp[]) >>
  gvs[] >> drule_all local_header_store_path >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL ()`,
    `es with scopes := pre ++
      (env |+ (id, entry with <|value := default_value entry.type; popped := []|>)) :: rest`,
    `OK t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  disj1_tac >> simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  drule emit_void_nonterminator_open >> simp[is_terminator_def] >>
  strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (es with scopes := _) t` mp_tac >>
  disch_then (mp_tac o Q.INST
    [`gs` |-> `[]`, `readings` |-> `t.vs_gas_readings`, `k` |-> `t.vs_inst_idx`]
    o MATCH_MP msg_gas_state_frame) >> simp[stmt_state_rel_inst_idx]
QED
