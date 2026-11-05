(* The target-independent expression, snapshot and load prefix. *)
Theory tupleAssignPrefix
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  tupleStageProps tupleTypedLoad  exprOperandVar exprLoweringProps
   localPtrsProps compileEnv loweringSlice fragExec valueEncoding
  vyperValue vyperTyping vyperInterpreter freshWrites list rich_list finite_map
  exprLowering vyperTypeABI stmtSimAssignTuple stmtSimReturn
Libs
  monadsyntax

Theorem tuple_assignment_prefix_run:
  !ctx func cenv cx e es es1 tys tvs vs sa su sl ss op staged elems s0 flag.
    expr_type e = TupleT tys /\
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL (ArrayV (TupleV vs)),es1) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    0 < type_memory_size_list tvs /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    cs_extends sa su /\ cs_extends su sl /\ cs_extends sl ss /\
    fn_has_code sa su func /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
    local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    ?t (w:256 word) b sz. stmt_state_rel ctx func cenv cx es1 t /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\
      t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\ b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es1.scopes t name b sz)) /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
         ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  cheat
QED






