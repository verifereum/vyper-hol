(* Frontier boundary for raw_revert's dynamic bytes operand. *)
Theory bodyMemRawRevertBounds
Ancestors
  bodyMemBiKeccakBounds exprLoweringProps loweringPosts valueEncodingProps

Theorem raw_revert_dynamic_post_bounds:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mload b s = n2w (LENGTH bs) /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    b + 32 <= s.vs_alloca_next /\
    b + 32 + LENGTH bs <= s.vs_alloca_next /\
    b + 32 + LENGTH bs < dimword (:256)
Proof
  strip_tac >> drule_all keccak_dynamic_post_bounds >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >>
     qexistsl_tac [`ctx`, `func`] >> fs[expr_post_def, stmt_state_rel_def]) >>
  qexists_tac `b` >> gvs[mem_word_at_eq_mload] >> decide_tac
QED
