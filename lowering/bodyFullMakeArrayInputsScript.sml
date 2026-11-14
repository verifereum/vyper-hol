(* MakeArray-specific input boundaries for the joint child/store path. *)
Theory bodyFullMakeArrayInputs
Ancestors
  exprSimVVFrame exprOperandVar exprLowering loweringStateRelDefs
  venomState venomInst bodyPtrDefs abiEncodeMaterialize exprSimHyps
  valueCopyBytes

Theorem make_array_add_original_post:
  !H ctx func ce cx e es sa sm s0 ee tv vv s buf off dst sn w.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    local_ptrs_reserved ce sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    eval_operand buf s = SOME w /\
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv s ==>
    vv_post H ctx func ce cx e es sa sm s0 ee tv vv
      (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s)
Proof
  rpt strip_tac >>
  irule vv_post_update_var >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `sm` >>
  simp[not_fresh_at_def] >>
  metis_tac[compiler_compile_var, not_fresh_at_def]
QED

Theorem make_array_physical_store_input:
  expr_body_pre ce cx env e es /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (post_value_type ce e) /\
  ptr_val_ok cx (post_value_type ce e) v (Var xs) G tn z /\
  ptr_buf_ok ce e (Var xs) G z /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME lt /\
  value_has_type lt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size lt /\
  eval_operand (Var xs) z = SOME sw ==>
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
         val_in_memory lt v (w2n sw) mem) /\
  (type_memory_size lt <> 0 ==> ptr_covers G tn xs z (type_memory_size lt))
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory pt v (w2n sw) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (`arg_type_fits (lowered_value_type ce e) (expr_type e)` by
        metis_tac[expr_body_pre_lowered_fits] >>
      drule_all materialize_post_lowered_classify >> strip_tac
      >- gvs[] >>
      rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`,
                    `get_tenv cx`, `pt`] >> simp[]) >>
  strip_tac >> gvs[ptr_buf_ok_def, ptr_val_ok_def, ptr_covers_def,
                   venomStateTheory.eval_operand_def] >> metis_tac[]
QED
