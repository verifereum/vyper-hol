(* Type-indexed interface to optional tuple staging. *)
Theory assignTupleLayoutStagePtr
Ancestors
  assignTuplePtrStage vyperAST exprLowering bodyPtrDefs

Theorem optional_tuple_stage_layout_run_ptr:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw d D PG G tn.
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
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~ctx_has_dalloca ctx /\
    ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) op G tn s /\
    (!w. eval_operand op s = SOME w /\
       type_memory_bytes cenv (TupleT tys) <> 0 ==>
       ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
         b <= w2n w /\
         w2n w + type_memory_bytes cenv (TupleT tys) <= b+sz) /\
    ghost_inv d cenv cx es G tn s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w G' tn'. eval_operand staged t = SOME w /\
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
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      ghost_inv d cenv cx es G' tn' t /\
      ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) staged G' tn' t /\
      (!w. eval_operand staged t = SOME w /\
         type_memory_bytes cenv (TupleT tys) <> 0 ==>
         ?x b sz. staged = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
           b <= w2n w /\
           w2n w + type_memory_bytes cenv (TupleT tys) <= b+sz) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (flag ==> ?b. FLOOKUP t.vs_allocas sa.cs_next_id =
          SOME (b,type_memory_size_list tvs) /\ w2n w = b /\
        !name entry p sz u. lookup_scopes name es.scopes = SOME entry /\
          FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
          lookup_var p t = SOME u ==>
          w2n u + val_footprint entry.type entry.value <= b \/
          b + type_memory_size_list tvs <= w2n u)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPEC `Name (TupleT tys) ARB`
    (Q.GEN `e` (SPEC_ALL optional_tuple_stage_run_ptr))) >>
  simp[expr_type_def, lowered_value_type_def, ptr_buf_ok_def]
QED
