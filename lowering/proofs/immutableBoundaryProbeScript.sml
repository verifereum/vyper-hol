(* Executable interface probes for the immutable-section design. *)
Theory immutableBoundaryProbe
Ancestors
  valueEncoding compileVyper venomExecSemantics

Theorem immutable_type_capacity_probe:
  type_memory_size (BaseTV (UintT 256)) = 32 /\
  type_memory_size (BaseTV AddressT) = 32 /\
  type_memory_size (BaseTV (BytesT (Fixed 32))) = 32 /\
  type_memory_size (BaseTV (StringT 40)) = 96 /\
  type_memory_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) = 64 /\
  type_memory_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) = 128 /\
  type_memory_size (StructTV [("a", BaseTV (UintT 256));
                             ("b", BaseTV AddressT)]) = 64
Proof
  EVAL_TAC
QED

Theorem immutable_empty_layout_probe:
  compute_immutables_len sft [] = 0
Proof
  simp[compute_immutables_len_def]
QED

(* A String[40] of length zero permits arbitrary capacity bytes, even
   when the two candidate sections both have the exact declared length. *)
Theorem immutable_padding_not_determined_probe:
  let zeros = REPLICATE 96 (0w:word8) in
  let dirty = REPLICATE 32 (0w:word8) ++ REPLICATE 64 (1w:word8) in
    LENGTH zeros = 96 /\ LENGTH dirty = 96 /\ zeros <> dirty /\
    val_in_memory (BaseTV (StringT 40)) (StringV "") 0 zeros /\
    val_in_memory (BaseTV (StringT 40)) (StringV "") 0 dirty
Proof
  EVAL_TAC >> simp[]
QED

Theorem immutable_zero_base_store_probe:
  (istore (w2n ((0w:bytes32) + 32w)) 42w s).vs_memory =
    (mstore 32 42w s).vs_memory /\
  FLOOKUP (istore 32 42w s).vs_immutables 32 = SOME 42w
Proof
  simp[istore_def, wordsTheory.WORD_ADD_0, wordsTheory.w2n_n2w,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

(* The deploy copy reads actual memory, not the immutable bookkeeping. *)
Theorem immutable_copy_source_probe:
  (mcopy dst 0 n s).vs_memory =
  (write_memory_with_expansion dst
     (TAKE n (s.vs_memory ++ REPLICATE n 0w)) s).vs_memory
Proof
  simp[mcopy_def]
QED

Theorem immutable_aggregate_layout_probe:
  compute_immutables_len sft
    [VariableDecl Private Immutable "X" (BaseT (UintT 256)) NONE;
     VariableDecl Private Immutable "S" (BaseT (StringT 40)) NONE;
     VariableDecl Private Immutable "A"
       (ArrayT (BaseT (UintT 256)) (Fixed 2)) NONE] = 192
Proof
  EVAL_TAC
QED

Theorem immutable_return_reads_memory_probe:
  step_inst_base
    (instruction id RETURN [Lit 0w; Lit 96w] []) s =
  Halt (halt_state (set_returndata
    (TAKE 96 (s.vs_memory ++ REPLICATE 96 0w)) s))
Proof
  simp[step_inst_base_def, venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

(* Diagnostic only: every theorem introduced in this probe is kernel closed. *)
val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("IMMUTABLE_PROBE_KERNEL_CLOSED " ^ name ^ "\n")
    else raise Fail ("Unclosed immutable probe: " ^ name)
  end) (DB.thms "immutableBoundaryProbe");
