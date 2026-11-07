(* Execution-free recursive well-formedness for aggregate entry values. *)
Theory entryAggregateValuePackaging
Ancestors
  valueEncoding abiDecoderFixedMemory abiStaticDynarrayLayout vyperValue list arithmetic

Theorem entry_fields_tuple_wf:
  !fields names tvs.
    LENGTH names = LENGTH tvs /\ tuple_val_wf (MAP SND fields) tvs ==>
    val_wf (StructTV (ZIP (names,tvs))) (StructV fields)
Proof
  Induct >> simp[val_wf_def] >> Cases_on `h` >>
  Cases_on `names` >> Cases_on `tvs` >> simp[val_wf_def] >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) [val_wf_def]) >> metis_tac[]
QED

Theorem entry_tuple_replicate_wf:
  !vs. tuple_val_wf vs (REPLICATE (LENGTH vs) tv) <=> elems_val_wf vs tv
Proof
  Induct >> simp[val_wf_def]
QED

Theorem entry_enumerate_wf[local]:
  !vs k n. elems_val_wf vs tv /\ k + LENGTH vs <= n ==>
    kvs_val_wf (enumerate_static_array dv k vs) tv n
Proof
  Induct >> simp[enumerate_static_array_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h = dv` >>
  gvs[enumerate_static_array_def, val_wf_def] >>
  first_x_assum irule >> simp[]
QED

Theorem entry_fixed_array_wf:
  LENGTH vs = n /\ tuple_val_wf vs (REPLICATE n tv) ==>
  val_wf (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)))
Proof
  strip_tac >> gvs[entry_tuple_replicate_wf, val_wf_def] >>
  irule entry_enumerate_wf >> simp[]
QED

(* Memory packaging is already exported by static_fields_memory_zip and
   abi_decoder_fixed_array_memory; do not duplicate these interfaces. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM") oracles
     then () else raise Fail "aggregate value packaging unexpected admission"
  end) [entry_fields_tuple_wf, entry_tuple_replicate_wf, entry_fixed_array_wf,
        static_fields_memory_zip, abi_decoder_fixed_array_memory];
