(*
 * The loads of a tuple's elements (compile_tuple_load_all) at the
 * elements' types: a word element's value, another element's address.
 *
 * TOP-LEVEL:
 *   compile_tuple_load_all_typed_frag — the loads, as a fragment
 *   tuple_container_bound — a tuple's buffer ends below 2^256
 *)
Theory tupleTypedLoad
Ancestors
  exprSimProps
  tupleLoadProps tupleMemoryLayout tupleStageProps stmtSimReturn exprSimLeaves
  stmtLowering compileEnv valueEncoding vyperTyping
  list rich_list words arithmetic valueEncodingProofs vyperTypeDefaults
  exprLoweringProps venomMemDefs finite_map  venomState fragExec
  emitHelperProps venomExecSemantics

Theorem tuple_prefix_sizes:
  !tys tvs cenv i.
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs ==>
    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
      SUM (MAP type_memory_size (TAKE i tvs))
Proof
  cheat
QED

Theorem tuple_typed_load_value:
  !tys tvs vs tenv cenv (w:256 word) mem i.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vs /\ tuple_in_memory vs tvs (w2n w) mem /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\ i < LENGTH tys ==>
    if is_word_type (EL i tys) then
      mem_word_at (w2n (w + n2w
        (SUM (MAP (type_memory_bytes cenv) (TAKE i tys))))) mem =
          typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n (w + n2w (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) =
      w2n w + SUM (MAP type_memory_size (TAKE i tvs))
Proof
  cheat
QED

(* Every live container lies below the allocation frontier. *)
Theorem tuple_container_bound:
  !func cenv cx es s b sz ctx.
    stmt_state_rel ctx func cenv cx es s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) ==>
    b + sz < dimword (:256)
Proof
  cheat
QED

Theorem tuple_load_vars_frame:
  !func cenv cx es sa sb s V ctx.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==>
      lookup_var x (s with vs_vars := V) = lookup_var x s) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V) /\
    local_ptrs_reserved cenv sb /\
    (!name b sz. local_region cenv es.scopes (s with vs_vars := V) name b sz =
                 local_region cenv es.scopes s name b sz)
Proof
  cheat
QED

Theorem compile_tuple_load_all_typed_run:
  !tys tvs vals tenv cenv bop sa elems sb s w.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    ?t V. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t = s with vs_vars := V /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  cheat
QED

(* Lift a variables-only load run without repeating the compiler induction. *)
Theorem tuple_load_run_lift:
  !ctx func cenv cx es sa sb s t V.
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = s with vs_vars := V /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\x. x = s)
      (\x. x = t with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F) /\
    stmt_state_rel ctx func cenv cx es
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    local_ptrs_reserved cenv sb /\
    (!name b sz. local_region cenv es.scopes
       (t with vs_inst_idx := LENGTH sb.cs_current_insts) name b sz =
       local_region cenv es.scopes s name b sz)
Proof
  cheat
QED

Theorem compile_tuple_load_all_typed_frag:
  !tys tvs vals tenv cenv bop sa elems sb s w ctx func cx es.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel ctx func cenv cx es t /\
      frag_exec ctx sa sb (\x. x = s) (\x. x = t) (\r. F) /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      tuple_in_memory vals tvs (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  cheat
QED
