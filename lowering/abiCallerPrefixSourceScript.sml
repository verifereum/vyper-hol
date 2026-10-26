(* Checked environment construction establishes the metadata of prefix-consuming
   decoding. Source validity supplies the prefix, with numeric resources separate. *)
Theory abiCallerPrefixSource
Ancestors
  abiCallerCoherence abiBuiltinPrefixSource abiBuiltinPrefixDecode abiBuiltinPrefixInput abiValidPrefixSource
  abiBuiltinSourceInput abiBuiltinDecodeEffect abiDecoderCoherence abiDecoderContract
  abiDecoderLoop abiDecoderReentry compileVyper compileEnv vyperTypeSystem vyperValue
  vyperABI contractABI valueEncoding abiEncoder builtinAbi fragExec venomState words list

Theorem abi_caller_prefix_pre:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type (type_env tops) ty) \/
    ?elem. vyper_to_abi_type (type_env tops) ty = Array NONE elem /\ ~is_dynamic elem) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_prefix_pre ce (type_env tops) ce.ce_struct_fields ty tv bs
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).ce_struct_fields
    ty tv` by
    (irule abi_caller_coherent >> asm_simp_tac bool_ss [] >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_prefix_pre_valid_source >> simp[]
QED

Theorem lower_abi_decode_checked_prefix_source:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type (type_env tops) ty) \/
    ?elem. vyper_to_abi_type (type_env tops) ty = Array NONE elem /\ ~is_dynamic elem) /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_caller_prefix_pre) >> strip_tac >>
  drule_all lower_abi_decode_prefix >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_PREFIX_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller prefix source not kernel closed: " ^ n)
  end) (DB.thms "abiCallerPrefixSource");
