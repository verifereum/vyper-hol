(* Value and buffer posts for the explicit ASSIGN/JMP suffix. *)
Theory bodyFullIfExpPosts
Ancestors
  exprSimIfExp bodyPtrIfExpNonwordFinish bodyPtrIfExpLocatedFinish
  bodyPtrIfExpAssignFrame exprSimMemDefs bodyPtrDefs loweringPosts
  exprLowering compileEnv context vyperAST venomState venomInst

Theorem ifexp_suffix_ptr_vv_ok:
  eval_operand op u = SOME w /\
  read_result cx tv ee = (INL v,ee) /\ ptr_val_ok cx t v op G tn u ==>
  ptr_vv_ok cx (post_value_type cenv (IfExp t c a b)) tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory)) ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >> drule_all assign_ptr_val_ok >>
  disch_then (qspecl_then [`rv`, `id`, `PG`] mp_tac) >>
  Cases_on `is_word_type t` >>
  simp[post_value_type_def, expr_type_def, ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
       mk_ptr_def, jump_to_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem ifexp_suffix_ptr_buf_ok:
  eval_operand op u = SOME w /\
  (~is_word_type t ==> !e. lowered_value_type cenv e = t ==>
       ptr_buf_ok cenv e op G u) ==>
  ~is_word_type t ==>
  ptr_buf_ok cenv (IfExp t c a b) (Var rv)
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  rpt strip_tac >>
  `ptr_buf_ok cenv (IfExp t c a b) op G u` by
    (first_x_assum irule >> simp[lowered_value_type_def, expr_type_def]) >>
  drule_all ifexp_assign_ptr_buf_ok >>
  disch_then (qspecl_then [`rv`, `id`, `PG`] mp_tac) >>
  simp[ptr_buf_ok_def, jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem ifexp_suffix_vv_store_bound:
  eval_operand op u = SOME w /\ read_result cx tv ee = (INL v,ee) /\
  expr_store_bound cx t v op u /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/
          w2n w + type_memory_size rt <= u.vs_alloca_next) ==>
  vv_store_bound cx (expr_type (IfExp t c a b))
    (lowered_value_type cenv (IfExp t c a b)) ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >> Cases_on `is_word_type t`
  >- simp[expr_type_def, vv_store_bound_stack_word] >>
  gvs[vv_store_bound_def, expr_type_def, lowered_value_type_def,
      mk_ptr_def, jump_to_def, assign_result_value, update_var_def,
      eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      expr_store_bound_def] >> metis_tac[]
QED
