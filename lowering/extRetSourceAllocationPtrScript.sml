(* Prospective allocation exclusion from the actual expression footprint. *)
Theory extRetSourceAllocationPtr
Ancestors
  allocationPtr allocaFootprint abiEncoder valueEncoding venomState
  loweringPosts finite_map arithmetic

Theorem prospective_alloca_expr_interval_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es v op s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  eval_operand op s = SOME w /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  n < dimword (:256) /\ 0 < n /\ 0 < val_footprint tv v /\
  FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (b,n) ==>
  b+n <= w2n w \/ w2n w + val_footprint tv v <= b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all step_alloca_site >> disch_then (qspec_then `out` assume_tac) >>
  `FLOOKUP (update_var out (n2w b) (abi_builtin_allocate_state id n s)).vs_allocas id = SOME (b,n)` by
    simp[update_var_def] >>
  spose_not_then assume_tac >>
  `w2n w <= MAX b (w2n w) /\
   MAX b (w2n w) < w2n w + val_footprint tv v` by
    (simp[MAX_DEF] >> decide_tac) >>
  drule_all alloca_step_expr_disjoint >>
  simp[MAX_DEF] >> decide_tac
QED

Theorem prospective_alloca_bytes_interval_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type t /\ eval_operand op s = SOME w /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  n < dimword (:256) /\ 0 < n /\
  FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (b,n) ==>
  b+n <= w2n w \/ w2n w + (32 + LENGTH bs) <= b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs)` by
    simp[val_footprint_def] >>
  drule_all prospective_alloca_expr_interval_disjoint >>
  simp[val_footprint_def]
QED

Theorem prospective_alloca_string_interval_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es (StringV str) op s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT cap)) /\
  ~is_word_type t /\ eval_operand op s = SOME w /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  n < dimword (:256) /\ 0 < n /\
  FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (b,n) ==>
  b+n <= w2n w \/ w2n w + (32 + LENGTH str) <= b
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < val_footprint (BaseTV (StringT cap)) (StringV str)` by
    simp[val_footprint_def] >>
  drule_all prospective_alloca_expr_interval_disjoint >>
  simp[val_footprint_def]
QED
