(* The finite recursive shell instantiated with a checked dynamic-array child.
   Containing code, metadata and the initialized outer invariant remain inputs. *)
Theory abiDecoderNestedArrayLoop
Ancestors
  abiDecoderCorrectPrimitiveArray abiDecoderRecursiveLoopFinite abiDecoderCorrect
  abiDecoderArrayBody compileEnv vyperAST vyperValue

val nested_child_instance = Q.INST
  [`ty` |-> `inner_ty:vyperAST$type`, `tv` |-> `inner_tv:vyperValue$type_value`,
   `maxn` |-> `inner_bound:num`] abi_decoder_correct_primitive_array;
val nested_word_hyp = fst (dest_imp (concl nested_child_instance));
val nested_child_correct = UNDISCH nested_child_instance;

Theorem abi_decoder_nested_array_loop =
  GEN_ALL (DISCH nested_word_hyp
    (SIMP_RULE bool_ss [nested_child_correct]
      (Q.INST [`ty` |-> `ArrayT inner_ty (Dynamic inner_bound)`,
        `tv` |-> `ArrayTV inner_tv (Dynamic inner_bound)`] abi_decoder_recursive_loop_typed)));

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_NESTED_ARRAY_LOOP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI nested array loop not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderNestedArrayLoop");
