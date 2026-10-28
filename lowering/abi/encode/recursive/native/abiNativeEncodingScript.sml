(* TOP-LEVEL: every raw recursive ABI memory encoding has an actual native
   execution under the compiler's computed allocation profile. The mutual
   fields assertion supplies recursive encoders at independent source
   strides. No child execution contract or fixed aggregate family is used. *)
Theory abiNativeEncoding
Ancestors
  abiNativeEncodingLeaf abiNativeEncodingComplex abiNativeEncodingStaticArray abiNativeEncodingDynamicArray
  abiNativeEncodingDefs abiNativeFields abiMemoryEncoding abiFieldLayoutDefs compileEnv venomState list words

Theorem abi_native_array:
  !info width stride is_dyn fields source span reference.
    32 <= span /\ LENGTH fields < dimword (:256) /\ mem_word_at source reference = (n2w (LENGTH fields):bytes32) /\
    (~is_dyn ==> width = abi_static_encoder_size info) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,is_dyn)) (source + 32) (span - 32) reference fields /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,is_dyn)) (source + 32) reference fields ==>
    abi_native_encoder (AbiDynArray info width stride is_dyn) source span reference
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_dyn` >> gvs[]
  >- (drule_all abi_native_dynamic_array >> simp_tac bool_ss []) >>
  irule abi_native_static_array >> irule abi_memory_encoding_array >> simp[]
QED

Theorem abi_native_encoding:
  (!info source span reference payload.
    abi_memory_encoding info source span reference payload ==> abi_native_encoder info source span reference payload) /\
  (!entries source span reference fields.
    abi_memory_fields entries source span reference fields ==> abi_native_fields entries source reference fields)
Proof
  ho_match_mp_tac abi_memory_encoding_strongind >> rpt conj_tac
  >- (rpt strip_tac >> irule abi_native_memory_word >> irule abi_memory_encoding_word >> first_assum MATCH_ACCEPT_TAC)
  >- (rpt strip_tac >> irule abi_native_memory_copy >> irule abi_memory_encoding_copy >> first_assum MATCH_ACCEPT_TAC)
  >- (rpt strip_tac >> irule abi_native_memory_bytes >> irule abi_memory_encoding_bytes >> asm_simp_tac bool_ss [])
  >- (rpt strip_tac >> drule_all abi_native_complex >> simp_tac bool_ss [])
  >- (rpt strip_tac >> drule_all abi_native_array >> simp_tac bool_ss [])
  >- simp[abi_native_fields_def] >>
  rpt strip_tac >> asm_simp_tac bool_ss [abi_native_fields_cons]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive native ABI encoding and fields induction: " ^ name)
  end) (DB.thms "abiNativeEncoding")
