(*
 * Staging a tuple for unpacking: where the tuple lies, the sizes of its
 * elements, and the optional MCOPY into a fresh buffer.
 *
 * TOP-LEVEL:
 *   tuple_element_sizes, tuple_memory_size_positive — element sizes
 *   optional_tuple_stage_code, optional_tuple_stage_run — the staging copy
 *   type_memory_bytes_tuple_list — a tuple type's size from its elements'
 *)
Theory tupleStageProps
Ancestors
  loweringPosts
  stmtSimDeclMem valueCopyBytes stmtSimReturn tupleMemoryLayout  valueTypingMemoryProps
  list rich_list finite_map compileEnv valueEncoding vyperTyping
  loweringHalt context emitHelper emitHelperProps exprLoweringProps freshWrites
  loweringSlice fragExec localPtrsProps venomInst venomState venomExecSemantics
Libs
  monadsyntax

Theorem expr_tuple_memory_owned:
  !cenv cx tys tvs vs sa sb es op s w.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) sa sb es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME w /\
    0 < type_memory_size_list tvs ==>
    tuple_in_memory vs tvs (w2n w) s.vs_memory /\
    tuple_val_wf vs tvs /\
    ?b sz. b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es.scopes s name b sz))
Proof
  cheat
QED

Theorem tuple_element_sizes:
  !tys tvs tenv cenv.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
         type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs)) ==>
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs
Proof
  cheat
QED

Theorem compatible_memory_type_positive:
  !tenv t tv vt vtv.
    evaluate_type tenv t = SOME tv /\
    evaluate_type tenv vt = SOME vtv /\ 0 < type_memory_size vtv /\
    (vt = t \/ is_bytestring_type vt /\ is_bytestring_type t) ==>
    0 < type_memory_size tv
Proof
  cheat
QED

Theorem tuple_memory_size_positive:
  !tys tvs tenv.
    tys <> [] /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    (!i. i < LENGTH tys ==> is_word_type (EL i tys) \/
      ?vt vtv. evaluate_type tenv vt = SOME vtv /\
        0 < type_memory_size vtv /\
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys))) ==>
    0 < type_memory_size_list tvs
Proof
  cheat
QED

Theorem tuple_stage_copy_parts:
  !sz op sa staged sb func.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func ==>
    ?sx sm p.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      staged = Var p /\ ~not_fresh_at sa p /\ not_fresh_at sb p /\
      emit_inst ALLOCA [Lit (n2w sz)] [p] sx = ((),sm) /\
      emit_void MCOPY [Var p; op; Lit (n2w sz)] sm = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sb /\
      fn_has_code sx sm func /\ fn_has_code sm sb func
Proof
  cheat
QED

Theorem tuple_stage_copy_run:
  !ctx func cenv cx es sa sb staged op s sw sz tv v.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = SOME sw /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem optional_tuple_stage_run:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz))) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem type_memory_bytes_tuple_list:
  !tys tvs cenv.
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs ==>
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs
Proof
  cheat
QED

Theorem optional_tuple_stage_code:
  !flag cenv tys op.
    (if flag then
       do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
          ptr <- comp_return buf.buf_operand;
          emit_void MCOPY [ptr; op; Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
          comp_return ptr od
     else comp_return op) =
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op)
Proof
  cheat
QED
