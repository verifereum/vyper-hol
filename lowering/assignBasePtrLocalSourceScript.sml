Theory assignBasePtrLocalSource
Ancestors compileEnv venomState valueEncoding words finite_map
  exprSimNameValue exprLowering context vyperAST exprSimHyps exprSimHypsDefs

(* Real local allocations supply capacity independently of ghost site sizes. *)
Theorem assign_base_ptr_local_capacity:
  !func cenv scopes s name entry p sz w n.
    local_ptrs_rel func cenv scopes s /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ s.vs_alloca_next < dimword(:256) /\
    n <= type_memory_size entry.type ==>
    w2n w + n < dimword(:256)
Proof
  rpt strip_tac >> fs[local_ptrs_rel_def] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem assign_base_ptr_lower_name_operand:
  !cenv expected ann name p sz sa op sb.
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    ~is_word_type ann /\
    lower_value compile_expr cenv expected (Name ann name) sa = (op,sb) ==>
    op = Var p /\ sb = sa
Proof
  rpt strip_tac >>
  drule compile_name_value_ptr >>
  strip_tac >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_def, mk_ptr_def,
      comp_return_def]
QED

Theorem assign_base_ptr_local_name_buffer_bound:
  !func cenv cx env es s expected ann name entry p sz sa op sb w.
    expr_body_pre cenv cx env (Name ann name) es /\
    local_ptrs_rel func cenv es.scopes s /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    ~is_word_type ann /\ s.vs_alloca_next < dimword(:256) /\
    lower_value compile_expr cenv expected (Name ann name) sa = (op,sb) /\
    eval_operand op s = SOME w ==>
    w2n w + type_memory_bytes cenv (lowered_value_type cenv (Name ann name))
      < dimword(:256)
Proof
  rpt strip_tac >>
  drule_all assign_base_ptr_lower_name_operand >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv ann = type_memory_size entry.type` by
    (irule expr_sim_inv_memory_size >>
     gvs[expr_body_pre_def] >> metis_tac[]) >>
  simp[lowered_value_type_def, expr_type_def] >>
  gvs[eval_operand_def] >>
  metis_tac[assign_base_ptr_local_capacity, arithmeticTheory.ADD_COMM,
            arithmeticTheory.LESS_EQ_REFL]
QED
