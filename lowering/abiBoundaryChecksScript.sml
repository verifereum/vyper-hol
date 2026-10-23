(* Small, kernel-checked representation probes for the changed ABI paths.
   These are layout facts, not execution correctness of the recursive decoder. *)
Theory abiBoundaryChecks
Ancestors
  valueEncoding compileEnv abiEncoder vyperABI

Theorem val_in_memory_singleton_tuple:
  val_in_memory (TupleTV [tv]) (ArrayV (TupleV [v])) off mem <=>
  val_in_memory tv v off mem
Proof
  simp[val_in_memory_def]
QED

Theorem singleton_tuple_memory_sizes:
  type_memory_size (TupleTV [tv]) = type_memory_size tv /\
  type_memory_bytes cenv (TupleT [ty]) = type_memory_bytes cenv ty
Proof
  simp[type_memory_size_def, type_memory_bytes_def]
QED

(* A fixed array of fixed arrays uses the same six consecutive words as
   its ABI static payload. Sparse-array indices are made explicit. *)
Theorem nested_static_array_layout_probe:
  val_in_memory
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (Fixed 3))
    (ArrayV (SArrayV
      [(0, ArrayV (SArrayV [(0, IntV a); (1, IntV b)]));
       (1, ArrayV (SArrayV [(0, IntV c); (1, IntV d)]));
       (2, ArrayV (SArrayV [(0, IntV e); (1, IntV f)]))])) off mem <=>
  mem_word_at off mem = val_to_w256 (IntV a) /\
  mem_word_at (off + 32) mem = val_to_w256 (IntV b) /\
  mem_word_at (off + 64) mem = val_to_w256 (IntV c) /\
  mem_word_at (off + 96) mem = val_to_w256 (IntV d) /\
  mem_word_at (off + 128) mem = val_to_w256 (IntV e) /\
  mem_word_at (off + 160) mem = val_to_w256 (IntV f)
Proof
  simp[val_in_memory_def, type_memory_size_def, CONJ_ASSOC]
QED

Theorem nested_static_array_sizes_probe:
  type_memory_bytes cenv
    (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Fixed 3)) = 192 /\
  type_memory_size
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (Fixed 3)) = 192
Proof
  simp[type_memory_bytes_def, type_memory_size_def]
QED

(* Check the exported probe objects rather than inferring integrity from a
   successful build (definitions imported from disk may carry DISK_THM). *)
val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BOUNDARY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI boundary probe not kernel closed: " ^ n)
  end) (DB.thms "abiBoundaryChecks");
