Theory extRetRawMemoryReturnPtr
Ancestors
  extRetCountedPtr representationCleanPtr stmtSimReturn stmtLowering
  compileEnv loweringStateRelDefs emitHelper loweringHalt contextCodegenRelProps fragExec
  bodyPtrDefs venomState venomInst words arithmetic valueEncodingProps

Theorem compile_external_return_raw_memory_gas_path_ptr:
  compile_external_return (SOME (Var src)) prim T ei msz F nkey ut iv st = (x,st') /\
  not_fresh_at st src /\ fn_has_code st st' fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var src s = SOME (n2w b) /\ ptr_covers G tn src s cap /\
  b + cap < dimword(:256) /\ 32 + LENGTH bs <= cap /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv (BytesV bs) b m) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  strip_tac >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  `val_in_memory tv (BytesV bs) b s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule val_in_memory_bytes_word >> simp[] >>
  rewrite_tac[mem_word_at_eq_mload] >> strip_tac >>
  `b < dimword(:256) /\ LENGTH bs < dimword(:256) /\
   b + 32 < dimword(:256)` by decide_tac >>
  `w2n ((n2w b : bytes32) + 32w) = b + 32` by
    (qspecl_then [`32w:bytes32`, `n2w b : bytes32`] mp_tac
      (GEN_ALL w2n_add_2) >> simp[]) >>
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
  qexistsl_tac [`n2w b : bytes32`, `cap`, `st.cs_next_id`, `len`, `off`, `src`] >>
  gvs[]
QED
