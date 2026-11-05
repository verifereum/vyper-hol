(*
 * Tuple unpacking into locals with memory-backed elements: the code's
 * stages and the run of a successful assignment (#637).
 *
 * TOP-LEVEL:
 *   assign_tuple_locals_memory_code_parts — the code split at its stages
 *   assign_tuple_locals_memory_success_run — a successful assignment's run
 *)
Theory tupleAssignMemory
Ancestors
  exprSimDefs loweringPosts tupleAssignParts tupleAssignPrefix
  tupleTypedLoad tupleStageProps stmtSimAssignTuple tupleLocalStoreProps
  tupleLocalStoreRun stmtSimReturn stmtSimDeclMem valueCopyBytes
    exprOperandVar exprLoweringProps stmtLowering compileEnv
  exprLowering emitHelperProps fragExec loweringSlice freshWrites
  list rich_list finite_map valueEncoding vyperTyping vyperValue
  vyperInterpreter vyperState venomState venomInst
Libs
  monadsyntax

(* The code of x1, ..., xn = e with memory-backed elements, split at its
   stages, with the growth facts of each. *)
Theorem assign_tuple_locals_memory_code_parts:
  !cenv lctx ty ids e tys sa sf c func.
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa =
      (c, sf) /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (!i. i < LENGTH ids /\ i < LENGTH tys ==>
      ?p sz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
        cenv.ce_var_type (EL i ids) = SOME vt /\
        (is_word_type vt = is_word_type (EL i tys)) /\
        (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)) /\
    fn_has_code sa sf func ==>
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
        elems ss = ((), sf) /\
      cs_extends sa sc /\ cs_extends sc su /\ cs_extends su sl /\
      cs_extends sl ss /\ cs_extends ss sf /\
      fn_has_code sa sc func /\ fn_has_code sc su func /\
      fn_has_code su sl func /\ fn_has_code sl ss func /\
      fn_has_code ss sf func /\
      sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
      sl.cs_next_var <= ss.cs_next_var /\ ss.cs_next_var <= sf.cs_next_var
Proof
  cheat
QED

Theorem assign_tuple_locals_memory_success_run:
  !ctx func cx lctx cenv ty ids e es es' tys tvs sa sf s0.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (INL (), es') /\
    ids <> [] /\ expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
     type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH ids ==> ?p sz vt.
      FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type (EL i ids) = SOME vt /\
      if is_word_type (EL i tys) then is_word_type vt else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
          type_memory_bytes cenv vt = type_memory_size vtv /\
          0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i entry.
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH ids /\
      lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
      if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    stmt_env cenv lctx ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) sa = (cenv,sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  cheat
QED






