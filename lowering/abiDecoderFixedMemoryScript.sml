(* Convert the shared dense member result to sparse fixed-array memory.
   TOP-LEVEL: abi_decoder_fixed_array_memory.
   Helpers: homogeneous tuple view and enumerated sparse entries. *)
Theory abiDecoderFixedMemory
Ancestors
  valueEncoding valueEncodingProps vyperValue list arithmetic

Theorem tuple_in_memory_replicate:
  !vs off. tuple_in_memory vs (REPLICATE (LENGTH vs) tv) off mem <=>
    elems_in_memory vs off tv mem
Proof
  Induct >> simp[val_in_memory_def]
QED

Theorem elems_in_memory_enumerate:
  !vs k off.
  elems_in_memory vs (off + k * type_memory_size tv) tv mem ==>
  kvs_in_memory (enumerate_static_array dv k vs) off tv mem
Proof
  Induct >> simp[enumerate_static_array_def, val_in_memory_def] >>
  rpt gen_tac >> strip_tac >> rename1 `val_in_memory tv head _ mem` >> Cases_on `head = dv` >>
  gvs[enumerate_static_array_def, val_in_memory_def] >>
  first_x_assum irule >> full_simp_tac bool_ss [MULT_CLAUSES, ADD_COMM]
QED

Theorem abi_decoder_fixed_array_memory:
  LENGTH vs = n /\ tuple_in_memory vs (REPLICATE n tv) d mem ==>
  val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d mem
Proof
  strip_tac >> gvs[tuple_in_memory_replicate, val_in_memory_sarray] >>
  irule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`vs`, `0`, `d`] elems_in_memory_enumerate)) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_FIXED_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI fixed-array memory not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderFixedMemory");
