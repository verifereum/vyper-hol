(* The successful bytes operand supplies the complete MLOAD/ADD/REVERT input. *)
Theory bodyFullRawRevertOperand
Ancestors
  bodySimFull representationCleanPtr exprLoweringProps exprSimProps
  loweringPosts bodyPtrDefs exprSimMemDefs vyperValue valueEncodingProofs
  compileEnv venomExecSemantics valueEncodingDefs venomState

Theorem raw_revert_data_boundary:
  expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op s /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn s /\
  ghost_inv_at D lo d cenv cx ee G tn s ==>
  ?x b root sz.
    op = Var x /\ eval_operand op s = SOME (n2w b) /\
    FLOOKUP G x = SOME (root, sz) /\ root <= b /\
    b + 32 + LENGTH bs <= root + sz /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn op = {} /\
    (!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    allocas_from lo s
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `?w. eval_operand op s = SOME w /\
     val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
       (w2n w) s.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def]) >>
  `?x. op = Var x /\ ptr_covers G tn x s (32 + LENGTH bs)` by
    (irule ptr_val_ok_read_covers >>
     conj_tac >- metis_tac[] >>
     qexistsl [`cx`, `BaseTV (BytesT (Dynamic cap))`, `expr_type e`, `BytesV bs`] >>
     simp[evaluate_type_def, is_word_type_def, val_footprint_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, evaluate_type_def, is_word_type_def] >>
     metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  `w2n w + (32 + LENGTH bs) <= s.vs_alloca_next` by
    (mp_tac (Q.SPECL [`BaseTV (BytesT (Dynamic cap))`, `BytesV bs`]
       val_footprint_le_store_size) >>
     gvs[expr_store_bound_def, evaluate_type_def, is_word_type_def,
         val_footprint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> gvs[expr_post_def, stmt_state_rel_def] >> metis_tac[]) >>
  gvs[ptr_covers_def, eval_operand_def, val_in_memory_def, ghost_inv_at_def] >>
  qexists_tac `w2n w` >> simp[] >>
  rpt strip_tac >> Cases_on `i < w2n w + 32` >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED
