(* Numeric/address and allocator conditions are independent of source bytes
   and registers, so producers can establish them before materializing input. *)
Theory abiBuiltinEncodeResources
Ancestors
  abiBuiltinEncodeInput abiBuiltinAllocationState abiDecoderAllocation abiDecoderArrayInitExec
  abiDecoderReentry abiDecoderContract abiEncoderInput compileEnv venomState finite_map words list arithmetic

Definition abi_builtin_encode_resources_def:
  abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap s <=>
    let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
    let outsz = maxlen+32+mid_size in
    sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\
    (sb+source_cap <= p \/ p+outsz <= sb) /\
    (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) /\
    (sb+source_cap <= b \/ b+cap <= sb) /\ (p+outsz <= b \/ b+cap <= p) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
    st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
    abi_decoder_budget first last b cap (abi_builtin_allocate_state st.cs_next_id outsz s)
End

Theorem abi_builtin_encode_pre_resources:
  abi_builtin_encode_pre ei at av st method_id_opt src sb source_cap p maxlen first last b cap s <=>
  abi_encoder_input ei at av sb source_cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  LENGTH (enc at av) <= maxlen /\
  abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap s
Proof
  simp[abi_builtin_encode_pre_def, abi_builtin_encode_resources_def, LET_THM] >> metis_tac[]
QED

Theorem abi_builtin_encode_resources_transport:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  ready.cs_next_id = st.cs_next_id ==>
  (abi_builtin_encode_resources ready method_id_opt sb source_cap p maxlen first last b cap t <=>
   abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`site` |-> `st.cs_next_id`,
    `outsz` |-> `maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`]
    abi_builtin_allocate_state_transport) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST
    [`s` |-> `abi_builtin_allocate_state st.cs_next_id
       (maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)) s`,
     `t` |-> `abi_builtin_allocate_state st.cs_next_id
       (maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)) t`]
    abi_decoder_budget_transport) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_RESOURCES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder resources not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeResources");
