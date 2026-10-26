(* TOP-LEVEL: an actual encoder result is an input for a reused outer buffer.
   Existing allocation rows and alloca_inv establish separation; the execution
   result supplies the bytes and preserves the outer buffer's allocation row. *)
Theory abiBuiltinEncodeReusedInput
Ancestors
  abiBuiltinEncodeProducer abiBuiltinEncodeRun abiBuiltinEncodeResources abiBuiltinEncodeEffect
  abiCallerAllocation abiScratchBuiltinCaller abiTupleEncodeOwnedBytes abiTupleEncodeInput abiDecoderReentry
  abiDecoderContract abiDecoderLoop abiEncoder compileEnv builtinAbi exprLowering
  valueEncoding vyperABI contractABI venomMemDefs venomState venomExecSemantics
  finite_map words list arithmetic

Theorem abi_builtin_allocate_separate:
  alloca_inv s /\ FLOOKUP s.vs_allocas outer_id = SOME (q,outer_size) /\ outer_id <> site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  p+outsz <= q \/ q+outer_size <= p
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_builtin_allocate_buffers >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_caller_allocation_separate >> decide_tac
QED

Theorem lower_abi_encode_reused_tuple_input:
  let n = maxlen+LENGTH (abi_builtin_encode_prefix method_id) in
  let bytes = abi_builtin_encode_prefix method_id ++ enc at av in
  lower_abi_encode ensure method_id src (type_to_abi_enc_info sf ce ty) maxlen st = (out,final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av st method_id src sb source_cap
    p maxlen first last b cap initial /\ alloca_inv initial /\
  FLOOKUP initial.vs_allocas outer_id = SOME (q,outer_size) /\ outer_id <> st.cs_next_id /\
  (outer_id < st.cs_next_id \/ final.cs_next_id <= outer_id) /\
  type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,maxlen+32+LENGTH (abi_builtin_encode_prefix method_id)) /\
    FLOOKUP actual.vs_allocas outer_id = SOME (q,outer_size) /\
    abi_tuple_encode_input consumer_sf ce (BaseT (BytesT (Dynamic n)))
      (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
      out final.cs_next_var q (q+outer_size) actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_next_valid initial` by fs[alloca_inv_def] >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] lower_abi_encode_produced_tuple_input) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule abi_builtin_encode_output_live >> disch_then assume_tac >>
  qpat_assum `abi_builtin_encode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_pre_resources]) >>
  drule_all abi_builtin_encode_output_bounds >> strip_tac >>
  SUBGOAL_THEN ``((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id =
      SOME (p,maxlen+32+LENGTH (abi_builtin_encode_prefix method_id)))`` assume_tac
  >-
    (Cases_on `method_id` >>
     fs[abi_builtin_encode_resources_def, LET_THM, abi_builtin_encode_prefix_def,
        abiBuiltinEncodeMethodReachTheory.abi_builtin_encode_method_bytes_length,
        AC ADD_COMM ADD_ASSOC]) >>
  drule_all abi_builtin_allocate_separate >> disch_then assume_tac >>
  qpat_assum `abi_builtin_encode_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_effect_def]) >>
  `FLOOKUP actual.vs_allocas outer_id = SOME (q,outer_size)` by
    (qpat_x_assum `!id. id < st.cs_next_id \/ final.cs_next_id <= id ==> _`
       (qspec_then `outer_id` mp_tac) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  irule abi_tuple_encode_owned_bytes_source_input >> asm_rewrite_tac[] >>
  qexists_tac `n2w p:bytes32` >> gvs[w2n_n2w, LENGTH_APPEND] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_REUSED_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI reused encoder input not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeReusedInput");
