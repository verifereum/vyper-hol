(* Extend the initialized array prefix using a child's typed result and frame. *)
Theory abiDecoderArrayPrefix
Ancestors
  abiDecoderContract valueEncodingProps valueEncodingProofs valueEncodingTyping
  valueEncoding vyperTyping venomState list arithmetic

Theorem elems_in_memory_append:
  !xs ys off tv mem.
  elems_in_memory (xs ++ ys) off tv mem <=>
  elems_in_memory xs off tv mem /\
  elems_in_memory ys (off + LENGTH xs * type_memory_size tv) tv mem
Proof
  Induct >> asm_simp_tac bool_ss [val_in_memory_def, APPEND, LENGTH,
    MULT_CLAUSES, ADD_CLAUSES, AC ADD_COMM ADD_ASSOC, CONJ_ASSOC]
QED

Theorem abi_decode_frame_preserves_elements:
  elems_in_memory vs off tv before.vs_memory /\ all_have_type tv vs /\
  abi_decode_frame d sz before after /\
  (off + LENGTH vs * type_memory_size tv <= d \/ d + sz <= off) ==>
  elems_in_memory vs off tv after.vs_memory
Proof
  strip_tac >>
  `elems_val_wf vs tv` by (drule_all (cj 4 value_has_type_val_wf) >> simp[]) >>
  `mem_bytes_at off (LENGTH vs * type_memory_size tv) after.vs_memory =
   mem_bytes_at off (LENGTH vs * type_memory_size tv) before.vs_memory` by
    (fs[abi_decode_frame_def] >> first_x_assum irule >> simp[]) >>
  irule (cj 3 val_in_memory_mem_agree_proof) >> simp[] >>
  qexists_tac `before.vs_memory` >> simp[]
QED

Theorem abi_decode_frame_append_element:
  elems_in_memory vs off tv before.vs_memory /\ all_have_type tv vs /\
  val_in_memory tv v (off + LENGTH vs * type_memory_size tv) after.vs_memory /\
  abi_decode_frame (off + LENGTH vs * type_memory_size tv) (type_memory_size tv)
    before after ==>
  elems_in_memory (vs ++ [v]) off tv after.vs_memory
Proof
  strip_tac >>
  `elems_in_memory vs off tv after.vs_memory` by
    (irule abi_decode_frame_preserves_elements >> simp[] >>
     qexistsl_tac [`before`, `off + LENGTH vs * type_memory_size tv`, `type_memory_size tv`] >>
     simp[]) >>
  simp[elems_in_memory_append, val_in_memory_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array prefix extension not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayPrefix");
