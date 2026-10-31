(*
 * Statement simulation: tuple unpacking into locals (#637)
 *
 * x1, ..., xn = e for locals xi already in scope, each held in memory at
 * its pointer, and e a tuple of word-typed elements.  The source evaluates
 * e, reads its value, a tuple, and writes its elements into x1, ..., xn in
 * order (assign_tuple_target_list).  The lowering evaluates e to a pointer
 * to the tuple, loads every element (compile_tuple_load_all, MLOADs as
 * all elements are words, so nothing is staged), then stores each into its
 * local's pointer (compile_tuple_store_all, one MSTORE each).
 *
 * TOP-LEVEL:
 *   eval_assign_tuple                   — the source run: the forced value
 *                                         of e, then the tuple's writes
 *   assign_tuple_locals_ok              — writing into locals fails only
 *                                         with a type error
 *   eval_assign_tuple_locals_error      — an error of the unpacking into
 *                                         locals is e's
 *   tuple_store_locals_run              — the stores of loaded words into
 *                                         locals, against the writes
 *   assign_tuple_locals_code_decompose  — the code split at its stages,
 *                                         word or memory-backed elements
 *   compile_assign_tuple_locals_stmt_frag — the statement, every outcome
 *)

Theory stmtSimAssignTuple
Ancestors
  list rich_list finite_map pred_set tupleLocalStoreProps tupleLocalStoreRun
  tupleLoadProps
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclMem
  stmtSimAssignStore stmtSimAssign stmtSimReturn exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperLookup vyperTyping
  vyperExprNoControl venomInst venomState
Libs
  monadsyntax

(* ===== Source side ===== *)

(* x1, ..., xn = e: e's forced value r, and on an error that error, on a
   value v the writes of v into the targets. *)
Theorem eval_assign_tuple:
  !cx gs e es res es'.
    eval_stmt cx (Assign (TupleTarget gs) e) es = (res, es') ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1 /\ no_control_exc ex) /\
      (!v. r = INL v ==>
           assign_tuple_targets cx (TupleTarget gs) v es1 = (res, es'))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[]
  >- (rename1 `eval_expr cx e es = (INL pv, es1)` >>
      Cases_on `read_result cx pv es1` >>
      rename1 `read_result cx pv es1 = (r2, es2)` >>
      Cases_on `r2` >> simp[] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[]) >>
  strip_tac >> gvs[] >>
  imp_res_tac (cj 1 eval_expr_no_control) >> simp[]
QED


Theorem assign_tuple_target_list_locals_ok[local]:
  !ids cx vs es res es'.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
      (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    res = INL ()
Proof
  Induct >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >>
  rpt gen_tac >> simp[ignore_bind_def, bind_def] >>
  rename1 `assign_tuple_targets cx (BaseTarget (NameTarget id)) v es` >>
  Cases_on `assign_tuple_targets cx (BaseTarget (NameTarget id)) v es` >>
  rename1 `_ = (r1, es1)` >> Cases_on `r1` >> simp[]
  >- metis_tac[] >>
  strip_tac >> gvs[] >>
  drule assign_tuple_target_local >> simp[]
QED

(* Writing a value into a tuple of locals fails only with a type error. *)
Theorem assign_tuple_locals_ok:
  !cx ids v es res es'.
    assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
      v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    res = INL ()
Proof
  rpt gen_tac >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[raise_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[raise_def] >>
  metis_tac[assign_tuple_target_list_locals_ok]
QED

Theorem eval_assign_tuple_locals_error:
  !cx ids e es ex es' lctx.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (INR ex, es') /\
    stmt_res_ok lctx (INR ex) ==>
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INR ex, es') /\
    expr_res_ok (INR ex : value + exception)
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_assign_tuple >> strip_tac >> Cases_on `r` >> gvs[]
  >- (drule assign_tuple_locals_ok >> gvs[stmt_res_ok_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

(* ===== Code side ===== *)

Theorem compile_load_tuple_elements_vars[local]:
  !tys cenv b off st elems st'.
    compile_load_tuple_elements cenv b tys off st = (elems, st') ==>
    EVERY (\op. ?x. op = Var x) elems
Proof
  Induct >- simp[compile_load_tuple_elements_def, comp_return_def] >>
  rpt gen_tac >> simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  Cases_on `emit_op ADD [b; Lit (n2w off)] st` >> rename1 `_ = (pv, s1)` >>
  Cases_on `emit_op MLOAD [pv] s1` >> rename1 `_ = (v, s2)` >>
  Cases_on `compile_load_tuple_elements cenv b tys
              (off + type_memory_bytes cenv h) s2` >>
  rename1 `_ = (rest, s3)` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
      simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
           fresh_var_def, emit_def, comp_return_def] >>
      strip_tac >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

Theorem tuple_store_word_locals_extends[local]:
  !ids tys ops cenv st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    EVERY is_word_type tys /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids ==>
    cs_extends st st'
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_store_locals_extends >> disch_then irule >>
  rpt strip_tac >>
  `MEM (EL i ids) ids /\ is_word_type (EL i tys)` by
    metis_tac[MEM_EL, EVERY_EL] >>
  gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >> simp[]
QED

(* ===== The stores against the writes ===== *)

(* Stores of the words of v1, ..., vn, held in ops, into word-typed locals
   x1, ..., xn run as the writes of v1, ..., vn into them do, where each
   word is how its local's type lays out its value. *)
Theorem tuple_store_locals_run:
  !ids tys ops tvs vs ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
      (INL (), es') /\
    LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    EVERY is_word_type tys /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids /\
    EVERY (\op. ?x. op = Var x) ops /\
    eval_operands ops s =
      SOME (MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))) /\
    (!i entry. i < LENGTH ids /\
               lookup_scopes (EL i ids) es.scopes = SOME entry ==>
               store_lays_out (EL i tvs) entry.type (EL i vs)) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s ==>
    (ids <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH ids = LENGTH vs` by
    (drule assign_tuple_target_list_length >> simp[]) >>
  `LENGTH ops = LENGTH vs` by
    (drule eval_operands_length >> simp[]) >>
  qspecl_then [`ids`, `F`, `tys`, `tvs`, `vs`, `ops`, `0`, `0`, `0`, `ctx`,
               `func`, `cenv`, `cx`, `es`, `es'`, `s`, `st`, `st'`] mp_tac
    tuple_store_mixed_locals_run >>
  impl_tac >- suspend "premises" >>
  simp[]
QED

Resume tuple_store_locals_run[premises]:
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- (drule_then (qspec_then `i` mp_tac) eval_operands_index >>
      `is_word_type (EL i tys)` by gvs[EVERY_EL] >>
      simp[EL_MAP, EL_ZIP])
  >- (`is_word_type (EL i tys)` by gvs[EVERY_EL] >>
      `MEM (EL i ids) ids` by (irule EL_MEM >> simp[]) >>
      gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >> simp[]) >>
  `is_word_type (EL i tys)` by gvs[EVERY_EL] >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

Finalise tuple_store_locals_run

(* ===== The statement ===== *)

(* The code of x1, ..., xn = e for locals: e's pointer, the optional
   staging copy, the loads of its elements, then one store per local. *)
Theorem assign_tuple_locals_code_decompose:
  !cenv lctx ty ids e tys sa sf c.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) ==>
    c = cenv /\
    ?vv sc op su staged sl elems ss.
      compile_expr cenv (TupleT tys) e sa = (vv, sc) /\
      unwrap_value cenv vv sc = (op, su) /\
      (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
          EXISTS (\t. ~is_word_type t) tys /\
          0 < SUM (MAP (type_memory_bytes cenv) tys) then
         do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
            ptr <- comp_return buf.buf_operand;
            emit_void MCOPY [ptr; op;
              Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
            comp_return ptr od
       else comp_return op) su = (staged, sl) /\
      compile_tuple_load_all cenv staged tys 0 sl = (elems, ss) /\
      compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
        elems ss = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     compile_tuple_unpack_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (TupleT tys) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sc)` >>
  Cases_on `unwrap_value cenv vv sc` >>
  rename1 `unwrap_value _ _ _ = (op, su)` >> simp[] >>
  `~(is_memory_view e /\ vv_location vv = SOME LocMemory /\
      EXISTS (\t. ~is_word_type t) tys /\
      0 < SUM (MAP (type_memory_bytes cenv) tys) /\
      ~cenv.ce_target CapMcopy)` by metis_tac[] >>
  asm_simp_tac (srw_ss()) [GSYM CONJ_ASSOC, arithmeticTheory.GREATER_DEF,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `(if guard then stage else comp_return op) su` >>
  Cases_on `(if guard then stage else comp_return op) su` >>
  rename1 `_ = (staged, sl)` >> simp[] >>
  Cases_on `compile_tuple_load_all cenv staged tys 0 sl` >>
  rename1 `compile_tuple_load_all _ _ _ _ _ = (elems, ss)` >> simp[] >>
  Cases_on `compile_tuple_store_all cenv tys
    (MAP (BaseTarget o NameTarget) ids) elems ss` >>
  rename1 `compile_tuple_store_all _ _ _ _ _ = (u, sf1)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [`staged`, `sl`, `elems`, `ss`] >> simp[]
QED

Theorem tuple_stage_grows:
  !flag sz op su staged sl.
    (if flag then
       do buf <- compile_alloc_buffer sz;
          ptr <- comp_return buf.buf_operand;
          emit_void MCOPY [ptr; op; Lit (n2w sz)];
          comp_return ptr od
     else comp_return op) su = (staged, sl) ==>
    cs_extends su sl /\ su.cs_next_var <= sl.cs_next_var
Proof
  Cases >> simp[comp_return_def, cs_extends_refl] >>
  rpt gen_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w sz)] su` >>
  rename1 `emit_op ALLOCA _ su = (aop, sm)` >> simp[] >>
  Cases_on `emit_void MCOPY [aop; op; Lit (n2w sz)] sm` >>
  rename1 `emit_void MCOPY _ sm = (u, sf)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  `cs_extends su sm /\ su.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sf /\ sm.cs_next_var <= sf.cs_next_var` by
    metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem assign_tuple_locals_code_parts[local]:
  !cenv lctx ty ids e tys sa sf c func.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?op s1 elems s2.
      lower_value compile_expr cenv (TupleT tys) e sa = (op, s1) /\
      compile_load_tuple_elements cenv op tys 0 s1 = (elems, s2) /\
      compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
        elems s2 = ((), sf) /\
      sa.cs_next_var <= s1.cs_next_var /\
      fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
      fn_has_code s2 sf func
Proof
  rpt gen_tac >> strip_tac >>
  `EXISTS (\t. ~is_word_type t) tys = F` by fs[EVERY_MEM, EXISTS_MEM] >>
  drule assign_tuple_locals_code_decompose >> simp[] >> strip_tac >>
  gvs[comp_return_def, compile_tuple_load_all_words] >>
  rename1 `unwrap_value cenv vv sc = (op, s1)` >>
  rename1 `compile_load_tuple_elements cenv op tys 0 s1 = (elems, s2)` >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op, s1)` by
    simp[lower_value_def, comp_bind_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_load_tuple_elements_extends >> strip_tac >>
  drule_all tuple_store_word_locals_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sf func` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

(* On a value: e's fragment leaves the tuple's pointer, its words are
   loaded, then stored into the locals as the writes of its elements. *)
Theorem assign_tuple_locals_success_run[local]:
  !ctx func cenv cx ids e es es' tys tup_tv sa s1 s2 sf op elems s0.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (INL (), es') /\
    ids <> [] /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
               (INL v, es1) ==> value_has_type tup_tv v) /\
    (!tvs vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL (ArrayV (TupleV vs)), es1) /\
       tup_tv = TupleTV tvs /\ i < LENGTH ids /\
       lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       store_lays_out (EL i tvs) entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op, s1) /\
    compile_load_tuple_elements cenv op tys 0 s1 = (elems, s2) /\
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
      elems s2 = ((), sf) /\
    sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
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
  drule eval_assign_tuple >> strip_tac >>
  Cases_on `r` >> gvs[] >>
  rename1 `assign_tuple_targets _ _ v es1 = (INL (), es')` >>
  `value_has_type tup_tv v` by metis_tac[] >>
  drule_all tuple_type_value >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `tup_tv = _` SUBST_ALL_TAC >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `INL (ArrayV (TupleV vs))`,
                           `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ sv` >>
  suspend "value"
QED

Resume assign_tuple_locals_success_run[value]:
  qpat_x_assum `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `expr_type e = TupleT tys`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  `tuple_in_memory vs tvs (w2n w + 0) sv.vs_memory` by
    (first_x_assum (qspec_then `TupleTV tvs` mp_tac) >>
     simp[val_in_memory_def]) >>
  `w2n w + 0 + 32 * LENGTH tys <= dimword (:256)` by
    (drule_all expr_val_at_bound >>
     simp[val_footprint_def, type_memory_size_def] >>
     drule_all word_tuple_size >> simp[]) >>
  `tuple_words cenv w tys 0 sv.vs_memory =
     MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` by
    (irule tuple_words_typed >> metis_tac[]) >>
  drule compile_load_tuple_elements_run >>
  disch_then (qspecl_then [`sv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq _ sv = OK (sv with vs_vars := lvars)` >>
  suspend "loads"
QED

Resume assign_tuple_locals_success_run[loads]:
  qabbrev_tac `sl = sv with <| vs_vars := lvars;
                               vs_inst_idx := LENGTH s2.cs_current_insts |>` >>
  `frag_exec ctx s1 s2 (\x. x = sv) (\x. x = sl) (\r. F)` by
    (irule frag_exec_run_inst_seq >> fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[Abbr `sl`]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `sv`] mp_tac) >> simp[] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!name entry p sz.
     lookup_scopes name es1.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p (sv with vs_vars := lvars) = lookup_var p sv` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at s1 x ==> _` irule >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
     irule environment_var_not_fresh >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es1 sl` by
    (simp[Abbr `sl`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_inst_idx] >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `LENGTH vs = LENGTH tvs /\ LENGTH tvs = LENGTH tys` by
    (drule values_have_types_length >> drule LIST_REL_LENGTH >> simp[]) >>
  `eval_operands elems sl =
     SOME (MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs)))` by
    simp[Abbr `sl`, eval_operands_vars_inst_idx] >>
  drule compile_load_tuple_elements_vars >> strip_tac >>
  qspecl_then [`ids`, `tys`, `elems`, `tvs`, `vs`, `ctx`, `func`, `cenv`,
               `cx`, `es1`, `es'`, `sl`, `s2`, `sf`] mp_tac
    tuple_store_locals_run >>
  impl_tac >- (simp[Abbr `sl`] >> metis_tac[]) >>
  strip_tac >> simp[] >>
  qexists_tac `t` >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      `lookup_var x sv = SOME u` by metis_tac[] >>
      `lookup_var x sl = lookup_var x sv` by
        (simp[Abbr `sl`] >> fs[lookup_var_def] >> metis_tac[]) >>
      metis_tac[])
  >- (rpt strip_tac >> simp[] >> fs[Abbr `sl`] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

Finalise assign_tuple_locals_success_run

(* x1, ..., xn = e for word-typed locals x1, ..., xn (n > 0) and e a tuple
   of words, for every outcome: e's errors exit, and on a value each
   element is stored at its local's pointer.  The value's typing and
   store_lays_out of each element against its local's type are required of
   e's value after read_result, as for x = e. *)
Theorem compile_assign_tuple_locals_stmt_frag:
  !ctx func cx lctx RetQ cenv ty ids e es res es' tys tup_tv.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (res, es') /\
    ids <> [] /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
               (INL v, es1) ==> value_has_type tup_tv v) /\
    (!tvs vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL (ArrayV (TupleV vs)), es1) /\
       tup_tv = TupleTV tvs /\ i < LENGTH ids /\
       lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       store_lays_out (EL i tvs) entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_locals_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  Cases_on `res`
  >- (rename1 `eval_stmt _ _ _ = (INL u, _)` >> Cases_on `u` >>
      drule_all assign_tuple_locals_success_run >> strip_tac >>
      disj1_tac >> qexistsl [`t`, `cenv`] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]) >>
  rename1 `eval_stmt _ _ _ = (INR y, _)` >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INR y, es') /\
   expr_res_ok (INR y : value + exception)` by
    (drule eval_assign_tuple_locals_error >> disch_then drule >> simp[]) >>
  drule_all stmtSimDeclTheory.expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED
