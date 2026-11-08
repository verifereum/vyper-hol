(* Scalar consumer: unwrap followed by the fetched clean word store. *)
Theory bodyPtrMakeArrayScalarStore
Ancestors
  bodyPtrMakeArrayScalarEndpoint bodyPtrMakeArrayWordStore
  fragGasPathPtr fragGasPath venomState typedCopyPtr

Theorem scalar_unwrap_store_endpoint:
  unwrap_value ce vv sm = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 es' tv vv s /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tv,es') /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx es' G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
               not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  not_fresh_at sm dst /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sb.cs_current_insts) =
    SOME (mk_inst id MSTORE [Var dst; op] []) ==>
  ?ty G1 tn1 s1 Gf tnf sf.
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
    expr_post ctx fn ce cx e es sa sb s0 es' v op s1 /\
    ghost_inv d ce cx es' G1 tn1 s1 /\
    ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
    lookup_var dst sf = SOME a /\ ptr_covers Gf tnf dst sf 32 /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = SUC (LENGTH sb.cs_current_insts) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      mem_word_at (w2n a) m = typed_val_to_w256 ty v) /\
    (!ty' v' p. val_wf ty' v' /\
      (!i. p <= i /\ i < p + val_footprint ty' v' ==>
        ~(w2n a <= i /\ i < w2n a + 32)) /\
      (!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
        val_in_memory ty' v' p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ty' v' p m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_unwrap_ptr_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `expr_post ctx fn ce cx e es sa sb s0 es' v op s1` >>
  `~s1.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `lookup_var dst s1 = SOME a /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst id MSTORE [Var dst; op] [])` by simp[] >>
  drule_all make_array_word_store_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl_tac [`ty`, `Gf`, `tnf`, `s1`, `Gf'`, `tnf'`, `sf`] >>
  simp[] >>
  conj_tac >- gvs[mstore_def, lookup_var_def] >>
  simp[mstore_def] >> metis_tac[]
QED
