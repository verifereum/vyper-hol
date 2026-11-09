Theory extRetRawValuePtr
Ancestors
  extRetCountedPtr representationCleanPtr stmtSimReturn stmtLowering
  compileEnv emitHelper loweringHalt contextCodegenRelProps fragExec
  bodyPtrDefs loweringPosts venomState venomInst words arithmetic valueEncodingProps exprSimTypedAlloc

Theorem compile_external_return_raw_indexed_gas_path_ptr[local]:
  !cx ctx fn PG G tn s src prim ei msz nkey ut iv st x st' a n cap.
  compile_external_return (SOME (Var src)) prim T ei msz F nkey ut iv st = (x,st') /\
  not_fresh_at st src /\ fn_has_code st st' fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n /\
  ptr_covers G tn src s cap /\ 32 <= cap /\
  32 + w2n n <= cap /\ w2n a + 32 < dimword(:256) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem) /\
  (!j. w2n (a + 32w) <= j /\ j < w2n (a + 32w) + w2n n ==>
        j NOTIN tn.t_mem) ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  `?len off. ~not_fresh_at st len /\ ~not_fresh_at st off /\ len <> off /\
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id MLOAD [Var src] [len];
       mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off];
       mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] []]` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, optional_unlock_view,
          emit_op_def, emit_void_def, emit_inst_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     qexistsl_tac [`STRING #"%" (toString st.cs_next_var)`,
                   `STRING #"%" (toString (st.cs_next_var + 1))`] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `src <> len /\ src <> off` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
      SOME (mk_inst st.cs_next_id MLOAD [Var src] [len]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (st.cs_next_id + 1) ADD [Var src; Lit 32w] [off]) /\
   get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (st.cs_next_id + 2) RETURN [Var off; Var len] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  irule mload_return_raw_gas_path_ptr >> simp[] >>
  qexistsl_tac [`a`, `cap`, `st.cs_next_id`, `len`, `off`, `src`] >> gvs[]
QED

Theorem compile_external_return_raw_value_gas_path_ptr:
  compile_external_return (SOME op) prim T ei msz F nkey ut iv st = (x,st') /\
  (!p. op = Var p ==> not_fresh_at st p) /\ fn_has_code st st' fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) op s /\
  ptr_val_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  value_has_type tv (BytesV bs) /\ tv <> BaseTV AddressT /\
  (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  eval_operand op s = SOME w /\ stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  strip_tac >>
  `val_footprint tv (BytesV bs) = 32 + LENGTH bs` by
    (Cases_on `tv` >> gvs[val_footprint_def, vyperTypingTheory.value_has_type_def] >>
     Cases_on `b` >> gvs[val_footprint_def, vyperTypingTheory.value_has_type_def] >>
     Cases_on `b'` >> gvs[val_footprint_def, vyperTypingTheory.value_has_type_def]) >>
  drule_all expr_val_at_bound >> strip_tac >>
  `val_footprint tv (BytesV bs) <> 0 /\
   32 + LENGTH bs <= val_footprint tv (BytesV bs)` by simp[] >>
  drule_all ptr_val_ok_read_covers >> strip_tac >> gvs[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  `val_in_memory tv (BytesV bs) (w2n w) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule val_in_memory_bytes_word >> simp[] >>
  rewrite_tac[mem_word_at_eq_mload] >> strip_tac >>
  `LENGTH bs < dimword (:256) /\ w2n w + 32 < dimword (:256)` by decide_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (qspecl_then [`32w:bytes32`, `w`] mp_tac (GEN_ALL w2n_add_2) >> simp[]) >>
  `lookup_var p s = SOME w` by fs[eval_operand_def] >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_raw_indexed_gas_path_ptr >>
  simp[] >> disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
