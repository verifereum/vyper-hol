(* Remaining heterogeneous members, at arbitrary ABI and destination offsets. *)
Theory abiMalformedMembers
Ancestors
  abiMalformedChildPremises abiMalformedConstructorInduction
  abiDecoderMemberInfos abiValidMembers abiMalformedRecursiveInterface
  abiVyperAdmissible abiEncoder fragExec vyperABI contractABI
  valueEncoding compileEnv words list arithmetic rich_list abiDecodeRanges

Definition abi_malformed_members_contract_def:
  abi_malformed_members_contract ce env sf tys tvs <=>
    !ctx func cenv cx es st en base_op hi src dst outsz ao vo.
      compile_abi_decode_complex_elems dst src MLOAD base_op hi
        (abi_decoder_member_infos sf ce tys) ao vo st = ((),en) /\
      EVERY (assignable_type env) tys /\
      EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys /\
      type_memory_size_list tvs < dimword (:256) /\
      vo + type_memory_size_list tvs <= outsz /\
      fn_inst_ids_distinct func /\ fn_has_code st en func ==>
      !B L xs p d dstid live ceiling incoming.
        en.cs_next_var <= ceiling.cs_next_var /\
        p + ao + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L ==>
        frag_exec ctx st en
          (\v. v = incoming /\
            abi_malformed_entry ctx func cenv cx es st
              (abi_malformed_scratch_sites st en func) dstid live
              base_op hi src dst B L xs p d outsz v /\
            fresh_vars_wrt ceiling v)
          (\u. vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
                 (DROP p xs) (DROP (p+ao) xs) /\
            abi_vyper_admissible_list env tys
              (abi_decode_members (MAP (vyper_to_abi_type env) tys)
                (DROP p xs) (DROP (p+ao) xs)) /\
            abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
              (abi_malformed_scratch_sites st en func) dstid incoming u /\
            fresh_vars_wrt ceiling u)
          (\r. ?v. r = Abort Revert_abort v)
End

Theorem abi_malformed_members_nil:
  abi_malformed_members_contract ce env sf [] []
Proof
  simp_tac (srw_ss()) [abi_malformed_members_contract_def,
    abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def] >> rpt strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  simp[Once vyper_decode_valid_enc_def, abi_decode_members_def,
    abi_vyper_admissible_list_nil] >>
  irule abi_malformed_resource_refl >> fs[abi_malformed_entry_def]
QED

(* Reflection composes at the same arbitrary head offset as the compiler.
   Dynamic child offsets remain relative to the aggregate origin. *)
Theorem abi_malformed_members_reflect_cons:
  LENGTH xs = L /\
  p + ao + abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    is_num_value (dec_number (Uint 256) (TAKE 32 (DROP (p+ao) xs)))) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty)
      (DROP p xs) (DROP (p+ao) xs)) /\
  abi_vyper_admissible env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty)
        (DROP p xs) (DROP (p+ao) xs))) /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
    (DROP p xs)
    (DROP (p + (ao + abi_member_head_size (vyper_to_abi_type env ty))) xs) /\
  abi_vyper_admissible_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs)
      (DROP (p + (ao + abi_member_head_size (vyper_to_abi_type env ty))) xs)) ==>
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (ty::tys))
    (DROP p xs) (DROP (p+ao) xs) /\
  abi_vyper_admissible_list env (ty::tys)
    (abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys))
      (DROP p xs) (DROP (p+ao) xs))
Proof
  strip_tac >> conj_tac
  >- (pure_rewrite_tac [MAP] >>
      pure_once_rewrite_tac [vyper_decode_valid_enc_def] >>
      Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
      full_simp_tac bool_ss [abi_decode_member_bytes_def,
        abi_member_head_size_def, abi_head_word_def, LENGTH_DROP,
        DROP_DROP_T, AC ADD_ASSOC ADD_COMM, LET_THM] >> decide_tac) >>
  simp_tac (srw_ss()) [MAP, abi_decode_members_def,
    abi_vyper_admissible_list_cons, DROP_DROP_T,
    Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED
