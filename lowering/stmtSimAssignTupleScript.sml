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
  stmtSimProps exprSimProps stmtSimDefs exprSimDefs loweringPosts tupleAssignCode
  list rich_list finite_map pred_set tupleLocalStoreProps tupleLocalStoreRun
  tupleLoadProps
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
  cheat
QED


Theorem assign_tuple_target_list_locals_ok[local]:
  !ids cx vs es res es'.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
      (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    res = INL ()
Proof
  cheat
QED

(* Writing a value into a tuple of locals fails only with a type error. *)
Theorem assign_tuple_locals_ok:
  !cx ids v es res es'.
    assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
      v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    res = INL ()
Proof
  cheat
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
  cheat
QED

(* ===== Code side ===== *)

Theorem compile_load_tuple_elements_vars[local]:
  !tys cenv b off st elems st'.
    compile_load_tuple_elements cenv b tys off st = (elems, st') ==>
    EVERY (\op. ?x. op = Var x) elems
Proof
  cheat
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
  cheat
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
  cheat
QED



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
  cheat
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
  cheat
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
  cheat
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
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\ EVERY is_word_type tys /\
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
  cheat
QED




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
  cheat
QED
