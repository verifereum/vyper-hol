(* TOP-LEVEL: the complete complex case of native semantic induction,
   allowing any mixture of static and dynamic recursive field metadata. *)
Theory abiNativeEncodingComplex
Ancestors
  abiNativeDynamicComplex abiNativeStaticComplex abiNativeEncodingDefs abiNativeFields
  abiMemoryEncoding abiFieldLayoutDefs compileEnv list

Theorem abi_native_complex:
  !entries source span reference full.
    abi_memory_fields entries source span reference full /\ abi_native_fields entries source reference full ==>
    abi_native_encoder (AbiComplex entries) source span reference
      (abi_field_bytes (abi_field_head_size full) full)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `EXISTS (\(_,_,_,flag). flag) entries`
  >- (drule_all abi_native_complex_dynamic >> simp_tac bool_ss []) >>
  drule_all abi_native_complex_static >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native arbitrary complex induction case: " ^ name)
  end) (DB.thms "abiNativeEncodingComplex")
