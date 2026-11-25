(* Physical source window for a nonzero-capacity Convert operand. *)
Theory bodyConvertSourceWindowMods
Ancestors
  bodyConvertSourceWindowTransport bodyPtrMakeArrayBytesTransport
  assignBasePtrBoundary bodyPtrDefs loweringPosts
  exprSimDefs venomState words

Theorem convert_nonzero_source_window_mods:
  expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  value_has_type rty v /\
  ptr_val_ok cx (expr_type e) v x G tn t /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory rty v (w2n w) mem) /\
  ptr_buf_ok cenv e x G t /\ eval_operand x t = SOME w /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
  64 <= type_memory_size rt /\
  w2n w + type_memory_size rt <= t.vs_alloca_next /\
  t.vs_alloca_next < dimword(:256) /\
  valid_conversion (expr_type e) dst /\ ~is_bytestring_type dst /\
  well_formed_type (get_tenv cx) dst /\
  x = Var z /\ lookup_var z t = SOME a /\ n <= 32 /\
  ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
   (?str. v = StringV str /\ n = LENGTH str)) ==>
  ptr_covers G tn z t (type_memory_size rt) /\
  w2n a + 64 <= t.vs_alloca_next /\
  w2n a + 64 < dimword(:256) /\
  val_in_memory rty v (w2n a) t.vs_memory /\
  mload (w2n a) t = n2w n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a + 32 <= i /\ i < w2n a + 32 + n ==> i NOTIN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `x = Var z` SUBST_ALL_TAC >>
  `op_taint tn (Var z) = {}` by fs[ptr_val_ok_def] >>
  `?p. Var z = Var p /\ ptr_covers G tn p t (type_memory_size rt)` by
    (irule ptr_buf_ok_read_covers >> simp[] >>
     qexistsl [`cenv`,`e`] >> simp[] >> decide_tac) >>
  conj_tac >- fs[] >>
  `w2n a = w2n w` by fs[venomStateTheory.eval_operand_def] >>
  conj_asm1_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  conj_tac >- decide_tac >>
  conj_tac >-
    (asm_rewrite_tac[] >> first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload (w2n w) t = n2w n /\
   (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
   (!i. w2n w + 32 <= i /\ i < w2n w + 32 + n ==> i NOTIN tn.t_mem)` by
    (irule robust_bytestring_source_live >>
     qexistsl [`rty`,`expr_type e`,`get_tenv cx`,`v`] >> asm_rewrite_tac[]) >>
  irule mload_clean_transport >> qexistsl [`w`,`z`] >> simp[]
QED
