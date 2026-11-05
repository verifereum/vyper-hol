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
  cheat
QED

Theorem emit_void_next_id:
  !opc ops st st'.
    emit_void opc ops st = ((), st') ==> st'.cs_next_id = st.cs_next_id + 1
Proof
  cheat
QED

Theorem compile_abi_clamp_next_id:
  !cl op st st'.
    compile_abi_clamp_basetype op cl st = ((), st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  cheat
QED

Theorem compile_abi_decode_static_next_id:
  !src dst opc clamp st st'.
    (!op sa sb. clamp op sa = ((), sb) ==> sa.cs_next_id <= sb.cs_next_id) /\
    compile_abi_decode_static src dst opc clamp st = ((), st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  cheat
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
  cheat
QED

Theorem compile_alloc_buffer_straight:
  !sz st buf st'.
    compile_alloc_buffer sz st = (buf, st') ==>
    dec_straight st st' /\ st.cs_next_id <= st'.cs_next_id
Proof
  cheat
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
  cheat
QED
