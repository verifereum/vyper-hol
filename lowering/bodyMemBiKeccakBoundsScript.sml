(* Frontier interface for the memory reads performed by keccak256. *)
Theory bodyMemBiKeccakBounds
Ancestors
  exprSimMemDefs exprSimHash exprSimProps compileEnv words

Theorem keccak_dynamic_post_bounds:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    b + 32 <= s.vs_alloca_next /\
    (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= s.vs_alloca_next)
Proof
  rpt strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
  simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
  mp_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
  rpt strip_tac >> disj2_tac >> decide_tac
QED

Theorem keccak_string_post_bounds:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (StringT cap)) /\
  expr_store_bound cx (expr_type e) (StringV str) op s ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH str) /\
    mem_bytes_at (b + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
    b + 32 < dimword (:256) /\ LENGTH str < dimword (:256) /\
    b + 32 <= s.vs_alloca_next /\
    (LENGTH str = 0 \/ b + 32 + LENGTH str <= s.vs_alloca_next)
Proof
  rpt strip_tac >> drule_all hash_string_post_view >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
  simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
  mp_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  rpt strip_tac >> disj2_tac >> decide_tac
QED
