Theory abiDecoderCaller
Ancestors
  abiDecoderCoherence compileVyper compileEnv valueEncoding vyperABI contractABI abiDecodeRanges
  abiDecoderConstructors vyperValue vyperContext vyperTypeContract finite_map
Libs
  vyperCheckContractLib finite_mapLib

(* ===== Checks ===== *)

(* Caller-interface probes: these do not assert recursive execution. *)

Theorem decoder_caller_word:
  abi_decoder_coherent ce env sf (BaseT (UintT 256)) (BaseTV (UintT 256))
Proof
  simp[abi_decoder_uint256_probe]
QED

Theorem decoder_caller_bytes:
  evaluate_type env (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) ==>
  abi_decoder_coherent ce env sf (BaseT (BytesT (Dynamic n)))
    (BaseTV (BytesT (Dynamic n)))
Proof
  strip_tac >>
  simp[abi_decoder_coherent_bytes_iff, abi_decoder_header_def,
       vfmConstantsTheory.word_size_def,
       vyperValueTheory.evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def]
QED

Theorem decoder_caller_singleton:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv]) ==>
  abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv])
Proof
  strip_tac >> irule decoder_caller_tuple >> simp[]
QED

(* A genuinely constructed acyclic declaration, not an assumed root header. *)
Theorem decoder_caller_constructed_struct:
  ce.ce_struct_fields =
    make_struct_fields_map [StructDecl "S" [("a",BaseT (UintT 256))]] ==>
  abi_decoder_coherent ce
    (type_env [StructDecl "S" [("a",BaseT (UintT 256))]])
    ce.ce_struct_fields (StructT (NONE,"S"))
    (StructTV [("a",BaseTV (UintT 256))])
Proof
  strip_tac >> irule abi_decoder_one_field_struct_realizable >>
  simp[vyperContextTheory.type_env_def,
       vyperContextTheory.type_env_for_module_def,
       make_struct_fields_map_def, build_struct_fields_map_def,
       build_struct_fields_one_def, field_mem_bytes_def,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
       nsid_to_string_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The existing environment agreement ignores flags entirely. *)
Theorem decoder_caller_consistency_does_not_supply_flags:
  ce.ce_flag_n_members (nsid_to_string nsid) = 0 ==>
  sfields_tenv_consistent FEMPTY (FEMPTY |+ (nsid,FlagArgs 256)) /\
  ~abi_decoder_coherent ce (FEMPTY |+ (nsid,FlagArgs 256)) FEMPTY
    (FlagT nsid) (FlagTV 256)
Proof
  strip_tac >> conj_tac
  >- simp[sfields_tenv_consistent_def, finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_EMPTY] >>
  irule abi_decoder_flag_inconsistent_excluded >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* ===== Order ===== *)

(* Regression: checked forward struct references have the semantic byte size. *)

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
