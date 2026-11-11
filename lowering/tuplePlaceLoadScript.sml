(* Load-all keeps the snapshot at its gas-path endpoint, including zero layouts. *)
Theory tuplePlaceLoad
Ancestors
  tuplePlacePrefixCert tupleAssignPrefix compileEnv loweringPosts
  stmtLowering stmtLoweringMono exprLoweringProps valueEncoding vyperValue fragGasPath

Theorem tuple_place_load_snapshot_path:
  !ltys ltvs vals tenv cenv bop sa elems sb s w ctx func cx es lo tys.
    compile_tuple_load_all cenv bop ltys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ltys ltvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
    values_have_types ltvs vals /\ tuple_in_memory vals ltvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list ltvs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ cs_extends sa sb /\
    tuple_place_snapshot cenv cx es lo sa.cs_next_id tys ltys ltvs w s ==>
    LENGTH elems = LENGTH ltys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel ctx func cenv cx es t /\
      gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      tuple_in_memory vals ltvs (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH ltys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i ltys) then
          v = typed_val_to_w256 (EL i ltvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))) /\
      tuple_place_snapshot cenv cx es lo sb.cs_next_id tys ltys ltvs w t
Proof
  rpt strip_tac >> drule_all compile_tuple_load_all_typed_path >> strip_tac >>
  simp[] >> qexists `t` >> simp[] >>
  conj_tac >- (qpat_x_assum `!i. _` mp_tac >>
    metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule tuple_place_snapshot_transport >>
  qexistsl [`sa.cs_next_id`, `s`] >> simp[] >>
  mp_tac (cj 4 ci_mono_list_helpers) >>
  disch_then (qspecl_then [`cenv`, `bop`, `ltys`, `0`, `sa`] mp_tac) >>
  gvs[ci_mono_def]
QED

Theorem tuple_place_load_zero_path:
  !ltys ltvs vals tenv cenv bop sa elems sb s w ctx func cx es lo tys.
    compile_tuple_load_all cenv bop ltys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ltys ltvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
    values_have_types ltvs vals /\ tuple_in_memory vals ltvs (w2n w) s.vs_memory /\
    type_memory_size_list ltvs = 0 /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ cs_extends sa sb ==>
    LENGTH elems = LENGTH ltys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel ctx func cenv cx es t /\
      gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      tuple_in_memory vals ltvs (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH ltys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i ltys) then
          v = typed_val_to_w256 (EL i ltvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))) /\
      tuple_place_snapshot cenv cx es lo sb.cs_next_id tys ltys ltvs w t
Proof
  rpt gen_tac >> strip_tac >>
  irule tuple_place_load_snapshot_path >>
  simp[wordsTheory.w2n_lt, tuple_place_snapshot_zero] >>
  conj_tac >- (qexists `bop` >> simp[]) >>
  qexists `tenv` >> simp[]
QED
