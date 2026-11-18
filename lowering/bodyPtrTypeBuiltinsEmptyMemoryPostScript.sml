Theory bodyPtrTypeBuiltinsEmptyMemoryPost
Ancestors
  bodyPtrTypeBuiltinsEmptyPost bodyPtrDefs exprSimHyps exprSimProps
  valueEncodingProofs valueEncoding exprLowering vyperState context
  ptrDiscipline compileEnv venomState

Theorem empty_memory_pointer_post:
  !cenv cx env es typ tv p w H th t.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    lookup_var p t = SOME w /\
    ptr_covers H th p t (type_memory_bytes cenv typ) /\
    (if is_bytestring_type typ \/
        (case typ of ArrayT _ (Dynamic _) => T | _ => F)
     then mem_word_at (w2n w) t.vs_memory = 0w /\
          (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN th.t_mem)
     else mem_bytes_at (w2n w) (type_memory_bytes cenv typ) t.vs_memory =
            REPLICATE (type_memory_bytes cenv typ) 0w /\
          (!i. w2n w <= i /\ i < w2n w+type_memory_bytes cenv typ ==>
            i NOTIN th.t_mem)) ==>
    ptr_vv_ok cx typ (Value (default_value tv))
      (LocatedValue typ (base_ptr <|buf_operand := Var p; buf_size := type_memory_bytes cenv typ|>))
      es H th t /\
    ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) (Var p) H t
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside th.t_mem t.vs_memory mem ==>
    val_in_memory tv (default_value tv) (w2n w) mem` by
    (rpt strip_tac >> irule empty_robust_default_memory >>
     goal_assum (drule_at Any) >> qexistsl_tac [`cenv`, `cx`, `env`, `es`, `typ`] >> simp[]) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  fs[ptr_vv_ok_def, base_ptr_def, ptr_covers_def, ptr_buf_ok_def,
     ptr_mem_ok_def, eval_operand_def, read_result_def, return_def,
     lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  rpt strip_tac >> gvs[] >>
  `val_store_size tv (default_value tv) <= type_memory_size tv` by
    simp[val_store_size_le, val_wf_default_value_proof] >>
  decide_tac
QED
