(*
 * Shape of the entry decoder's code: id use and straight-line emission.
 *
 * TOP-LEVEL:
 *   compile_alloc_buffer_straight
 *   compile_decode_arg_straight
 *
 * Helpers: emit_op_next_id, emit_void_next_id, compile_abi_clamp_next_id,
 *   compile_abi_decode_static_next_id, static_dec_next_id.
 *)
Theory entryDecodeStructure
Ancestors
  abiDecodeStaticProps entryDecodeProps abiEncoder context compileEnv
  moduleLowering arithmetic
  emitHelper emitHelperProps exprLoweringProps entryDecodeStaticProps venomInst

Theorem emit_op_next_id:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') ==> st'.cs_next_id = st.cs_next_id + 1
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem emit_void_next_id:
  !opc ops st st'.
    emit_void opc ops st = ((), st') ==> st'.cs_next_id = st.cs_next_id + 1
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem compile_abi_clamp_next_id:
  !cl op st st'.
    compile_abi_clamp_basetype op cl st = ((), st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  Cases >> rpt gen_tac >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  TRY (rename1 `if signed then _ else _` >> Cases_on `signed`) >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_abi_decode_static_next_id:
  !src dst opc clamp st st'.
    (!op sa sb. clamp op sa = ((), sb) ==> sa.cs_next_id <= sb.cs_next_id) /\
    compile_abi_decode_static src dst opc clamp st = ((), st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_next_id >> strip_tac >>
  drule emit_void_next_id >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem static_dec_next_id:
  (!info n. static_dec info n ==>
     !dst src st st'.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
         ((), st') ==> st.cs_next_id <= st'.cs_next_id) /\
  (!elems n. static_decs elems n ==>
     !dst src k st st'.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') ==> st.cs_next_id <= st'.cs_next_id)
Proof
  ho_match_mp_tac static_dec_strongind >> rpt conj_tac
  >- (rpt strip_tac >> fs[compile_abi_decode_to_buf_def] >>
      irule compile_abi_decode_static_next_id >>
      goal_assum (drule_at Any) >> metis_tac[compile_abi_clamp_next_id])
  >- (rpt strip_tac >> fs[compile_abi_decode_to_buf_def] >> metis_tac[])
  >- simp[compile_abi_decode_to_buf_def, comp_return_def] >>
  rpt strip_tac >> rename1 `static_dec ei m` >>
  drule_all decode_elems_cons_phases >> strip_tac >>
  drule getelemptr_static_emit >> strip_tac >>
  `st1.cs_next_id = st.cs_next_id + 1 /\
   st2.cs_next_id = st1.cs_next_id + 1` by metis_tac[emit_op_next_id] >>
  `st2.cs_next_id <= st3.cs_next_id /\
   st3.cs_next_id <= st'.cs_next_id` by metis_tac[] >> decide_tac
QED

Theorem compile_alloc_buffer_straight:
  !sz st buf st'.
    compile_alloc_buffer sz st = (buf, st') ==>
    dec_straight st st' /\ st.cs_next_id <= st'.cs_next_id
Proof
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule dec_straight_emit_op >> simp[is_terminator_def] >> strip_tac >>
  drule emit_op_next_id >> simp[]
QED

Theorem compile_decode_arg_straight:
  !cenv name prim dyn sz info off hi st st' loc dst.
    compile_decode_args cenv [(name,prim,dyn,sz,info)] off
      CALLDATALOAD hi 4 st = ((),st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    (prim \/ (~dyn /\ ?n. static_dec info n)) ==>
    dec_straight st st' /\ st.cs_next_id <= st'.cs_next_id
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `prim`
  >- (qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      gvs[] >>
      rename1 `emit_op ADD _ st = (src,s1)` >>
      rename1 `emit_op CALLDATALOAD _ s1 = (v,s2)` >>
      rename1 `emit_void MSTORE _ s3 = ((),st')` >>
      `dec_straight st s1` by metis_tac[dec_straight_emit_add] >>
      `dec_straight s1 s2` by
        (drule dec_straight_emit_op >> simp[is_terminator_def]) >>
      `dec_straight s2 s3` by metis_tac[dec_straight_clamp] >>
      `dec_straight s3 st'` by
        (drule dec_straight_emit_void >> simp[is_terminator_def]) >>
      `st.cs_next_id <= s1.cs_next_id /\
       s1.cs_next_id <= s2.cs_next_id /\
       s3.cs_next_id <= st'.cs_next_id` by
        metis_tac[emit_op_next_id, emit_void_next_id, LESS_EQ_ADD] >>
      `s2.cs_next_id <= s3.cs_next_id` by
        metis_tac[compile_abi_clamp_next_id] >>
      metis_tac[dec_straight_trans, LESS_EQ_TRANS]) >>
  gvs[] >> drule_all compile_decode_static_arg_phases >> strip_tac >>
  `dec_straight st st1` by metis_tac[dec_straight_emit_add] >>
  `dec_straight st1 st'` by metis_tac[static_dec_straight] >>
  `st.cs_next_id <= st1.cs_next_id` by
    (drule emit_op_next_id >> simp[]) >>
  `st1.cs_next_id <= st'.cs_next_id` by metis_tac[static_dec_next_id] >>
  metis_tac[dec_straight_trans, LESS_EQ_TRANS]
QED
