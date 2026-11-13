(* A typed scalar place supplies the one-word storage continuation. *)
Theory assignTupleWordStorageTailPtr
Ancestors
  assignTuplePtrStorage placeStore stmtSimAssignStorage vyperPlaceFrames
  loweringPosts bodyPtrDefs stmtLowering exprLowering compileEnv
  valueEncodingDefs vyperState venomState

Theorem word_storage_place_tail_ptr:
  compile_store_at_loc cenv.ce_imm_alloca dst op
    (SOME (if tr then LocTransient else LocStorage)) st = ((),st') /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v es = (INL (),es') /\
  fn_has_code st st' func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  op_taint tn op = {} /\ op_taint tn dst = {} /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t tn'. stmt_state_rel ctx func cenv cx es' t /\
    ghost_inv d cenv cx es' G tn' t /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. lookup_var x t = lookup_var x s) /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\
    (!x. op_taint tn' (Var x) = op_taint tn (Var x)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn' (OK t)
Proof
  strip_tac >>
  `!u mem. storage_dead cx tr (update_storage slot u mem) = storage_dead cx tr mem` by
    (rpt gen_tac >>
     mp_tac (Q.SPECL [`cx`,`tr`,`slot`,`tv`,`ty`,`get_tenv cx`,`u`,`mem`]
       place_store_scalar_storage_dead) >> asm_rewrite_tac[]) >>
  `encode_value tv v = SOME [(0,typed_val_to_w256 tv v)]` by
    (mp_tac (Q.SPECL [`get_tenv cx`,`ty`,`tv`,`v`] encode_value_word_typed) >>
     asm_rewrite_tac[]) >>
  mp_tac (SPEC_ALL tuple_storage_store_head_path_ptr) >>
  (impl_tac >- fs[write_place_def]) >> simp[]
QED
