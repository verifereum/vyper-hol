(* Discharge the successful-prefix contract in the first-failure theorem. *)
Theory abiDecodeRejectJoint
Ancestors
  abiDecodeRejectFirstFailure abiDecodeValidJoint

Theorem abi_malformed_allocated_joint:
abi_decoder_coherent ce env sf ty tv /\
abi_decode_bytes_widths env ty /\
compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
  (type_to_abi_dec_info sf ce ty) st = ((),en) /\
fn_has_code st en func /\ fn_inst_ids_distinct func /\
(?av. has_type (vyper_to_abi_type env ty) av) /\
assignable_type env ty /\ type_memory_size tv < dimword(:256) /\
abi_size_bound sf ty < dimword(:256) /\
abi_malformed_entry H0 ctx func cenv cx es st
  (abi_malformed_scratch_sites st en func) dstid live
  (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
(case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => p+32 <= L | _ => T) /\
fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
s.vs_inst_idx = LENGTH st.cs_current_insts /\
bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
  else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
abi_decode_ptr_window G tn s source (n2w B) L /\
ptr_covers G tn output s (type_memory_bytes ce ty) /\
op_prov G pos = NONE /\ op_prov G hi = NONE /\
op_taint tn pos = {} /\ op_taint tn hi = {} /\
allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s
==>
?u G' tn'.
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  mp_tac abi_malformed_allocated_joint_from_success >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_valid_allocated_joint)) >>
  disch_then MATCH_ACCEPT_TAC
QED
