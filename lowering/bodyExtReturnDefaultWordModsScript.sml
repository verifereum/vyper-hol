(* Physical cut after storing a word-valued external-call default. *)
Theory bodyExtReturnDefaultWordMods
Ancestors
  logStoreDataOriginPtr abiValueEncoding exprBopSimProps
  compileEnv context venomState fragGasOriginPtr bodyPtrDefs
  ptrDiscipline finite_map words arithmetic

Theorem extcall_default_word_payload:
  is_word_type ret_type /\
  type_widens_to (get_tenv cx) default_ty ret_type /\
  evaluate_type (get_tenv cx) ret_type = SOME rtv /\ value_has_type rtv dv /\
  expr_val_rel cx default_ty dv default_op t /\
  eval_operand default_op u = eval_operand default_op t /\
  op_taint tu default_op = {} /\
  compile_store_memory cenv default_op (Var q) ret_type default_ty ds = ((),de) /\
  type_memory_bytes cenv ret_type = type_memory_size rtv /\
  lookup_var q u = SOME dw /\ ptr_covers Gu tu q u (type_memory_bytes cenv ret_type) /\
  w2n dw + type_memory_bytes cenv ret_type < dimword (:256) /\
  w2n dw + type_memory_bytes cenv ret_type <= u.vs_alloca_next /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ fn_has_code ds de func /\
  ~u.vs_halted /\ u.vs_current_bb = ds.cs_current_bb /\
  u.vs_inst_idx = LENGTH ds.cs_current_insts ==>
  ?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u p /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
      val_in_memory rtv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
      FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tp (Var x) = op_taint tu (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
      (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts
Proof
  strip_tac >> drule_all compileEnvTheory.type_widens_to_word >> strip_tac >> gvs[] >>
  drule_all abiValueEncodingTheory.abi_word_type_size >> strip_tac >> gvs[] >>
  drule_all exprBopSimPropsTheory.expr_val_rel_typed >> strip_tac >>
  `eval_operand default_op u = SOME (typed_val_to_w256 rtv dv)` by simp[] >>
  drule_all logStoreDataOriginPtrTheory.compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `p` (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac)))) >>
  qexistsl_tac [`p`, `Gp`, `tp`] >> simp[]
QED
