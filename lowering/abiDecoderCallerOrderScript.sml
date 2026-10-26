(* Regression: checked forward struct references have the semantic byte size. *)
Theory abiDecoderCallerOrder
Ancestors
  abiDecoderCoherence compileVyper compileEnv valueEncoding vyperValue
  vyperContext vyperTypeContract finite_map
Libs
  vyperCheckContractLib finite_mapLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;

Definition forward_struct_tops_def:
  forward_struct_tops =
    [StructDecl "A" [("b",StructT (NONE,"B"))];
     StructDecl "B" [("x",BaseT (UintT 256))];
     FunctionDecl External Pure F F "f" [("a",StructT (NONE,"A"))] [] NoneT []]
End

Theorem forward_struct_checker_accepts:
  IS_SOME (check_contract F [] (0w:address) [(NONE,forward_struct_tops)])
Proof
  simp[forward_struct_tops_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem forward_struct_semantic_type:
  evaluate_type (type_env forward_struct_tops) (StructT (NONE,"A")) =
    SOME (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])])
Proof
  EVAL_TAC
QED

Theorem forward_struct_compiler_size:
  !vis mut func_name args ret_type (body:stmt list) use_trans.
  type_memory_bytes
    (build_compile_env forward_struct_tops vis mut func_name args ret_type body use_trans)
    (StructT (NONE,"A")) = 32
Proof
  rpt gen_tac >>
  simp[type_memory_bytes_def, build_compile_env_ce_struct_fields] >> EVAL_TAC
QED

(* Historical counterexample, retained with its original proof. Before field
   sizes used the complete semantic environment, A's reference to later B was
   assigned size zero. The checked regression below now requires size 32.
Theorem forward_struct_not_coherent:
  !vis mut func_name args ret_type (body:stmt list) use_trans sf.
  ~abi_decoder_coherent
    (build_compile_env forward_struct_tops vis mut func_name args ret_type body use_trans)
    (type_env forward_struct_tops) sf (StructT (NONE,"A"))
    (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])])
Proof
  rpt gen_tac >> strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, forward_struct_compiler_size, type_memory_size_def]
QED

Theorem forward_struct_checked_layout_disagrees:
  !vis mut func_name args ret_type (body:stmt list) use_trans.
  IS_SOME (check_contract F [] (0w:address) [(NONE,forward_struct_tops)]) /\
  evaluate_type (type_env forward_struct_tops) (StructT (NONE,"A")) =
    SOME (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])]) /\
  type_memory_size (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])]) = 32 /\
  type_memory_bytes
    (build_compile_env forward_struct_tops vis mut func_name args ret_type body use_trans)
    (StructT (NONE,"A")) = 0
Proof
  simp[forward_struct_checker_accepts, forward_struct_semantic_type,
       forward_struct_compiler_size, type_memory_size_def]
QED
*)

Theorem forward_struct_checked_layout_agrees:
  !vis mut func_name args ret_type (body:stmt list) use_trans.
  IS_SOME (check_contract F [] (0w:address) [(NONE,forward_struct_tops)]) /\
  evaluate_type (type_env forward_struct_tops) (StructT (NONE,"A")) =
    SOME (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])]) /\
  type_memory_size (StructTV [("b",StructTV [("x",BaseTV (UintT 256))])]) = 32 /\
  type_memory_bytes
    (build_compile_env forward_struct_tops vis mut func_name args ret_type body use_trans)
    (StructT (NONE,"A")) = 32
Proof
  simp[forward_struct_checker_accepts, forward_struct_semantic_type,
       forward_struct_compiler_size, type_memory_size_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CALLER_ORDER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder order check not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCallerOrder");
