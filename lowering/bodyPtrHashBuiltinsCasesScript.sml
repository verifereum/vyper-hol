(* Operand interface for the hash builtin pointer cases. *)
Theory bodyPtrHashBuiltinsCases
Ancestors
  bodyPtrPreds exprOpenFirstOperand vyperContext list
  representationCleanPtr loweringPosts bodyPtrDefs words
  exprSimHash exprSimHypsDefs vyperTypeSystem

Theorem hash_builtin_operand_ptr:
  !cx ann bt arg args cenv env es d PG tops ctx func ty.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH (arg::args)) ==>
      body_exprs_ptr_ok cx (arg::args)) /\
    builtin_args_length_ok bt (LENGTH (arg::args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann bt (arg::args)) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty arg es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty arg es
Proof
  rpt strip_tac >>
  `body_expr_ptr_ok cx arg` by gvs[body_exprs_ptr_ok_def] >>
  `expr_body_pre cenv cx env arg es` by
    (irule expr_body_pre_builtin_head >>
     qexistsl [`ann`, `args`, `bt`] >> simp[] >> metis_tac[]) >>
  gvs[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem hash_dynamic_bytes_operand:
  !cx ty bs op G tn s cap w.
    ptr_val_ok cx ty (BytesV bs) op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
    eval_operand op s = SOME w ==>
    (?p. op = Var p /\ ptr_covers G tn p s (32 + LENGTH bs)) /\
    (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ptr_val_ok_read_covers >>
      conj_tac >- metis_tac[] >>
      qexistsl [`cx`, `BaseTV (BytesT (Dynamic cap))`, `ty`, `BytesV bs`] >>
      simp[val_footprint_def]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem hash_string_operand:
  !cx ty str op G tn s cap w.
    ptr_val_ok cx ty (StringV str) op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT cap)) /\
    eval_operand op s = SOME w ==>
    (?p. op = Var p /\ ptr_covers G tn p s (32 + LENGTH str)) /\
    (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH str ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ptr_val_ok_read_covers >>
      conj_tac >- metis_tac[] >>
      qexistsl [`cx`, `BaseTV (StringT cap)`, `ty`, `StringV str`] >>
      simp[val_footprint_def]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (StringT cap)) (StringV str) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_val_in_memory_string_clean >> simp[] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

(* Invalid arity is excluded by the body precondition itself, not by IH. *)
Theorem hash_body_pre_arity:
  !cx cenv env ann bt es s.
    (bt = Keccak256 \/ bt = Sha256) /\
    expr_body_pre cenv cx env (Builtin ann bt es) s ==>
    LENGTH es = 1
Proof
  rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule_at Any hash_builtin_types >> simp[] >> strip_tac >>
  gvs[]
QED
