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
  stmtLoweringProps
  stmtSimProps exprSimProps stmtSimDefs exprSimDefs loweringPosts exprSimTypedAlloc tupleAssignCode
  list rich_list finite_map pred_set tupleLocalStoreProps tupleLocalStoreRun
  tupleLoadProps fragGasSeq fragGasMode stmtSimDeclPath gasContext stmtSimForced
  fragExec localPtrsProps  loweringSlice  stmtSimDeclMem
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


Theorem eval_assign_tuple_action:
  eval_stmt cx (Assign (TupleTarget gs) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (assign_tuple_targets cx (TupleTarget gs))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem assign_tuple_target_local_gas[local]:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (res, ee) ==>
  !tail. assign_tuple_targets cx (BaseTarget (NameTarget id)) v
    (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def,
       get_place_def, write_place_def, lift_option_type_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id es.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x` >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      set_scopes_def, AllCaseEqs()]
QED

Theorem assign_tuple_target_list_locals_gas[local]:
  !ids cx vs es res ee.
  assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
    (res, ee) ==>
  !tail. assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs
    (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  Induct >> Cases_on `vs` >> rpt gen_tac >> strip_tac >> gen_tac >>
  gvs[Once evaluate_def, return_def, raise_def] >>
  simp[Once evaluate_def, return_def, raise_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
  drule assign_tuple_target_local_gas >>
  disch_then (qspec_then `tail` assume_tac) >>
  simp[] >> metis_tac[]
QED

Theorem assign_tuple_locals_gas:
  assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
    v es = (res, ee) ==>
  !tail. assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
    v (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  Cases_on `v` >> simp[evaluate_def, raise_def] >>
  Cases_on `a` >> simp[raise_def] >>
  metis_tac[assign_tuple_target_list_locals_gas]
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



Theorem compile_load_tuple_elements_path[local]:
  !tys cenv bop off sa elems sb s w ctx func.
    compile_load_tuple_elements cenv bop tys off sa = (elems, sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t vs. t = s with vs_vars := vs /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      eval_operands elems t = SOME (tuple_words cenv w tys off s.vs_memory) /\
      gas_marked_path F ctx func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  drule compile_load_tuple_elements_no_gas >> strip_tac >>
  qexistsl [`t`, `vs`] >> simp[] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb)
           (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  simp[gas_marked_path_def]
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

Theorem tuple_word_store_path[local]:
  emit_void MSTORE [Var p; op] st = ((), st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  store_lays_out tv entry.type v ==>
  ?t. stmt_state_rel ctx func cenv cx
        (es with scopes := pre ++
          (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists `mstore (w2n w) (typed_val_to_w256 tv v) s with
              vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, mstore_def, LET_THM]
QED

Theorem tuple_store_locals_path[local]:
  !ids tys ops tvs vs ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops
      st = ((), st') /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
      (INL (), es') /\
    LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    EVERY is_word_type tys /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt) ids /\
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
        gas_marked_path F ctx func s 0 (OK t)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `LENGTH vs = 0` by (drule assign_tuple_target_list_length >> simp[]) >>
      `LENGTH ops = 0` by
        (drule eval_operands_length >> simp[] >> metis_tac[LENGTH_MAP, LENGTH_ZIP]) >>
      gvs[compile_tuple_store_all_def, comp_return_def, LENGTH_NIL,
          Once evaluate_def, return_def] >>
      qexists `s` >> simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH (h::ids) = LENGTH vs` by
    metis_tac[assign_tuple_target_list_length, LENGTH_MAP] >>
  `LENGTH ops = LENGTH vs` by (drule eval_operands_length >> simp[]) >>
  Cases_on `tys` >- gvs[] >> Cases_on `tvs` >- gvs[] >>
  Cases_on `vs` >- gvs[] >> Cases_on `ops` >- gvs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `ZIP (tv::tvs1, v::vs1)` >>
  fs[EVERY_DEF] >>
  drule (SRULE [MAP, combinTheory.o_THM] assign_tuple_target_list_local_cons) >> strip_tac >>
  `is_word_type vt = is_word_type ty` by simp[] >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _`
    (assume_tac o SRULE [combinTheory.o_THM]) >>
  drule_all tuple_store_local_step >> strip_tac >> gns[] >>
  suspend "cons"
QED

Resume tuple_store_locals_path[cons]:
  `cs_extends sm st'` by
    (drule_all tuple_store_word_locals_extends >> simp[]) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    (qpat_x_assum `!tys ops tvs vs ctx' func' cenv' cx' es'' es' s' st'' st'. _` kall_tac >>
     `cs_extends st sm` by
       (drule emit_void_extends >> simp[cs_extends_def, same_blocks_def] >> strip_tac >>
        qexists `[]` >> simp[]) >>
     drule_all fn_has_code_split >> simp[]) >>
  `~block_is_terminated sm` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_void_def, comp_bind_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >> strip_tac >>
     gvs[block_is_terminated_def, is_terminator_def, mk_inst_def,
         SNOC_APPEND, LAST_SNOC] >>
     Cases_on `st.cs_current_insts` >> simp[is_terminator_def] >>
     simp[LAST_DEF, LAST_APPEND, is_terminator_def]) >>
  `lookup_scopes h es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out tv entry.type v` by
    (qpat_x_assum `!i entry. _` (qspecl_then [`0`, `entry`] mp_tac) >> simp[]) >>
  `eval_operand (Var x) s = SOME (typed_val_to_w256 tv v) /\
   eval_operands ops1 s =
     SOME (MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs1,vs1)))` by
    gvs[eval_operands_def, AllCaseEqs()] >>
  drule_all tuple_word_store_path >> strip_tac >>
  suspend "tail"
QED

Resume tuple_store_locals_path[tail]:
  `eval_operands ops1 t =
     SOME (MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs1,vs1)))` by
    (`!ops. EVERY (\op. ?x. op = Var x) ops ==>
              eval_operands ops t = eval_operands ops s` by
       (Induct >> simp[eval_operands_def] >> rpt strip_tac >>
        gvs[eval_operand_def]) >> metis_tac[]) >>
  suspend "tail_apply"
QED

Resume tuple_store_locals_path[tail_apply]:
  `!i e'. i < LENGTH vs1 /\
       lookup_scopes (EL i ids)
         (es with scopes := pre ++
            (env |+ (h, entry with <|value := v; popped := []|>)) :: rest).scopes = SOME e' ==>
       store_lays_out (EL i tvs1) e'.type (EL i vs1)` by
    (simp[] >> rpt strip_tac >>
     drule_all lookup_scopes_write_local_type >> strip_tac >>
     qpat_x_assum `!i entry. i < SUC _ /\ _ ==> _`
       (qspecl_then [`SUC i`, `e`] mp_tac) >> simp[EL, TL]) >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspec_then `tvs1` mp_tac) >>
  disch_then (qspecl_then [`ctx`, `func`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "compose"
QED

Resume tuple_store_locals_path[compose]:
  conj_tac >- simp[] >> qexists `t'` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Finalise tuple_store_locals_path

(* ===== The statement ===== *)

(* The code of x1, ..., xn = e for locals: e's pointer, the optional
   staging copy, the loads of its elements, then one store per local. *)
Theorem assign_tuple_locals_code_decompose:
  !cenv lctx ty ids e tys sa sf c.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
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
  drule_all assign_tuple_targets_code_decompose >> simp[]
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
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\ EVERY is_word_type tys /\
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
Theorem assign_tuple_locals_suffix[local]:
  !ctx func cenv cx lctx ids e es ee v tys tup_tv sa s1 s2 sf op elems s0 sv gs.
    expr_post ctx func cenv cx e es sa s1 s0 ee v op sv /\
    sv.vs_current_bb = s1.cs_current_bb /\
    sv.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~sv.vs_halted /\
    ee.gas_obs = [] /\
    (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (INL v, ee) /\
    gas_admissible
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (stmt_res_ok lctx) es /\
    ids <> [] /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt) ids /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv /\
    value_has_type tup_tv v /\
    (!tvs vs i entry. v = ArrayV (TupleV vs) /\ tup_tv = TupleTV tvs /\
       i < LENGTH ids /\ lookup_scopes (EL i ids) ee.scopes = SOME entry ==>
       store_lays_out (EL i tvs) entry.type (EL i vs)) /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op, s1) /\
    compile_load_tuple_elements cenv op tys 0 s1 = (elems, s2) /\
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids)
      elems s2 = ((), sf) /\
    sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code s1 s2 func /\ fn_has_code s2 sf func /\
    local_ptrs_reserved cenv sa ==>
    ?ee' t'.
      (!tail. assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
        v (ee with gas_obs := tail) = (INL (), ee' with gas_obs := tail)) /\
      gas_marked_path F ctx func sv 0 (OK t') /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
        (ee' with gas_obs := []) t'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v ee` >>
  rename1 `_ = (res, ee')` >>
  `eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
     (es with gas_obs := gs) = (res, ee')` by
    (pure_rewrite_tac[eval_assign_tuple_action] >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >> simp[]) >>
  `stmt_res_ok lctx res` by
    (qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `res`, `ee'`] mp_tac) >>
     simp[]) >>
  `res = INL ()` by
    (drule assign_tuple_locals_ok >> disch_then irule >> gvs[stmt_res_ok_def]) >>
  gvs[] >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "value"
QED

Resume assign_tuple_locals_suffix[value]:
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  suspend "memory"
QED

Resume assign_tuple_locals_suffix[memory]:
  `post_value_type cenv e = TupleT tys` by
    metis_tac[post_value_type_lowered] >>
  fs[] >>
  `w2n w + val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) < dimword (:256)` by
    (metis_tac[expr_val_at_bound]) >>
  `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) sv.vs_memory` by
    (first_x_assum (qspec_then `TupleTV tvs` mp_tac) >> simp[]) >>
  `tuple_words cenv w tys 0 sv.vs_memory =
     MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
    (drule_all word_tuple_size >> strip_tac >>
     irule tuple_words_typed >>
     simp[val_in_memory_def, val_footprint_def, type_memory_size_def] >>
     gvs[val_in_memory_def, val_footprint_def, type_memory_size_def] >>
     metis_tac[]) >>
  drule_all compile_load_tuple_elements_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (simp[not_fresh_at_def] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (qpat_assum `t = _` SUBST1_TAC >>
     irule stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
  `EVERY (\op. ?x. op = Var x) elems` by
    metis_tac[compile_load_tuple_elements_vars] >>
  qabbrev_tac `sl = t with vs_inst_idx := LENGTH s2.cs_current_insts` >>
  `stmt_state_rel ctx func cenv cx ee sl /\ ~sl.vs_halted /\
   sl.vs_current_bb = s2.cs_current_bb /\
   sl.vs_inst_idx = LENGTH s2.cs_current_insts /\
   eval_operands elems sl =
     SOME (MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs)))` by
    (drule compile_load_tuple_elements_no_gas >> strip_tac >>
     gvs[Abbr `sl`, stmt_state_rel_inst_idx, instIdxIndepTheory.eval_ops_inst_idx]) >>
  drule_all tuple_store_locals_path >> strip_tac >>
  qexistsl [`ee'`, `t'`] >> conj_tac
  >- (drule assign_tuple_locals_gas >> simp[]) >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[stmt_post_def] >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  `stmt_state_rel ctx func cenv cx (ee' with gas_obs := []) t'` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee' t'` mp_tac >>
     rpt (pop_assum kall_tac) >>
     mp_tac (Q.INST [`es` |-> `ee'`, `s` |-> `t'`,
                     `gs` |-> `[]`, `readings` |-> `t'.vs_gas_readings`,
                     `k` |-> `t'.vs_inst_idx`] msg_gas_state_frame) >>
     simp[] >> metis_tac[]) >>
  gvs[Abbr `sl`] >> rpt strip_tac >>
  `not_fresh_at s1 x` by metis_tac[] >>
  qpat_x_assum `!x. lookup_var x t' = _` (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `x` mp_tac) >>
  simp[lookup_var_def] >> rpt strip_tac >>
  qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _`
    (qspecl_then [`x`, `w'`] mp_tac) >>
  simp[lookup_var_def]
QED

Finalise assign_tuple_locals_suffix

(* x1, ..., xn = e for word-typed locals x1, ..., xn (n > 0) and e a tuple
   of words, for every outcome: e's errors exit, and on a value each
   element is stored at its local's pointer.  The value's typing and
   store_lays_out of each element against its local's type are required of
   e's value after read_result, as for x = e. *)
Theorem compile_assign_tuple_locals_stmt_frag:
  !ctx func cx lctx RetQ cenv ty ids e es tys tup_tv.
    ids <> [] /\
    EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                          cenv.ce_var_type id = SOME vt /\ is_word_type vt)
      ids /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv /\
    (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
               (es with gas_obs := gs) = (INL v, es1) ==>
               value_has_type tup_tv v) /\
    (!gs tvs vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL (ArrayV (TupleV vs)), es1) /\
       tup_tv = TupleTV tvs /\ i < LENGTH ids /\
       lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       store_lays_out (EL i tvs) entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_locals_code_parts >> strip_tac >> gvs[] >>
  irule forced_then_stmt_outcome >>
  qexistsl [
    `\v ee t. expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
              t.vs_current_bb = s1.cs_current_bb /\
              t.vs_inst_idx = LENGTH s1.cs_current_insts`,
    `e`, `assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))`] >>
  reverse conj_tac
  >- (conj_tac >- simp[eval_assign_tuple_action] >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `op`, `s0`] mp_tac) >>
      (impl_tac >- (fs[] >> metis_tac[forced_then_admissible, eval_assign_tuple_action])) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `value_has_type tup_tv v` by metis_tac[] >>
  `!tvs vs i entry. v = ArrayV (TupleV vs) /\ tup_tv = TupleTV tvs /\
     i < LENGTH ids /\ lookup_scopes (EL i ids) ee.scopes = SOME entry ==>
     store_lays_out (EL i tvs) entry.type (EL i vs)` by
    metis_tac[] >>
  `lowered_value_type cenv e = expr_type e` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) assign_tuple_locals_suffix) >>
  strip_tac >> qexistsl [`INL ()`, `ee'`, `OK t'`] >> simp[]
QED
