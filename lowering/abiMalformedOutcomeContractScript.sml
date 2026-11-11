(* Fixed-function interfaces for recursive arbitrary-byte execution. *)
Theory abiMalformedOutcomeContract
Ancestors
  abiMalformedBoundedContract abiMalformedMembers abiMalformedBytesExecution
  abiMalformedConstructorContract abiMalformedRecursiveInterface fragExec
  abiDecoderCoherence abiVyperAdmissible abiValidMembers exprLowering
  compileEnv venomState venomExecSemantics vyperABI contractABI valueEncoding
  words list arithmetic

Definition abi_malformed_constructor_outcome_def:
  abi_malformed_constructor_outcome env ty di ctx func cenv cx es st en
      base_op hi src dst outsz <=>
    fn_has_code st en func ==>
    !B L xs p d dstid live ceiling incoming.
      en.cs_next_var <= ceiling.cs_next_var /\
      (case di of DecPrimWord clamp => p + 32 <= L | _ => T) /\
      abi_malformed_entry ctx func cenv cx es st
        (abi_malformed_scratch_sites st en func) dstid live
        base_op hi src dst B L xs p d outsz incoming /\
      fresh_vars_wrt ceiling incoming /\
      ~incoming.vs_halted /\ incoming.vs_current_bb = st.cs_current_bb /\
      incoming.vs_inst_idx = LENGTH st.cs_current_insts ==>
      frag_outcome ctx func incoming en
        (\u. abi_malformed_reflected_post env ty
          (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
           else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
          ctx func cenv cx es st.cs_next_var
            (abi_malformed_scratch_sites st en func) dstid incoming u /\
          fresh_vars_wrt ceiling u)
        (\r. ?v. r = Abort Revert_abort v)
End

Definition abi_malformed_bounded_type_outcome_def:
  abi_malformed_bounded_type_outcome ce env sf ty tv <=>
    !di ctx func cenv cx es st en base_op hi src dst outsz.
      type_to_abi_dec_info sf ce ty = di /\
      compile_abi_decode_to_buf dst src MLOAD base_op hi di st = ((),en) /\
      (?av. has_type (vyper_to_abi_type env ty) av) /\
      assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
      abi_size_bound sf ty < dimword (:256) /\
      fn_inst_ids_distinct func /\ fn_has_code st en func /\
      type_memory_bytes ce ty <= outsz ==>
      abi_malformed_constructor_outcome env ty di ctx func cenv cx es st en
        base_op hi src dst outsz
End

Definition abi_malformed_members_outcome_def:
  abi_malformed_members_outcome ce env sf tys tvs <=>
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
        p + ao + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L /\
        abi_malformed_entry ctx func cenv cx es st
          (abi_malformed_scratch_sites st en func) dstid live
          base_op hi src dst B L xs p d outsz incoming /\
        fresh_vars_wrt ceiling incoming /\
        ~incoming.vs_halted /\ incoming.vs_current_bb = st.cs_current_bb /\
        incoming.vs_inst_idx = LENGTH st.cs_current_insts ==>
        frag_outcome ctx func incoming en
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

Theorem abi_malformed_constructor_to_outcome:
  abi_malformed_constructor env ty di ctx func cenv cx es st en
    base_op hi src dst outsz ==>
  abi_malformed_constructor_outcome env ty di ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  rewrite_tac [abi_malformed_constructor_def, abi_malformed_constructor_outcome_def] >>
  rpt strip_tac >> irule frag_outcome_apply >>
  simp[] >> qexists_tac `(\v. v = incoming /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      base_op hi src dst B L xs p d outsz v /\ fresh_vars_wrt ceiling v)` >>
  simp[] >> qexists_tac `st` >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bounded_to_outcome:
  abi_malformed_bounded_type_contract ce env sf ty tv ==>
  abi_malformed_bounded_type_outcome ce env sf ty tv
Proof
  rewrite_tac [abi_malformed_bounded_type_contract_def,
    abi_malformed_bounded_type_outcome_def] >> rpt strip_tac >>
  irule abi_malformed_constructor_to_outcome >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem abi_malformed_members_to_outcome:
  abi_malformed_members_contract ce env sf tys tvs ==>
  abi_malformed_members_outcome ce env sf tys tvs
Proof
  rewrite_tac [abi_malformed_members_contract_def,
    abi_malformed_members_outcome_def] >> rpt strip_tac >>
  irule frag_outcome_apply >> simp[] >>
  qexists_tac `(\v. v = incoming /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      base_op hi src dst B L xs p d outsz v /\ fresh_vars_wrt ceiling v)` >>
  simp[] >> qexists_tac `st` >> simp[] >>
  fs[AC ADD_ASSOC ADD_COMM] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `vo` >> simp[]
QED

Theorem abi_malformed_primitive_outcome:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  fn_inst_ids_distinct func /\ 32 <= outsz ==>
  abi_malformed_constructor_outcome env ty (DecPrimWord clamp)
    ctx func cenv cx es st en base_op hi src dst outsz
Proof
  strip_tac >> irule abi_malformed_constructor_to_outcome >>
  irule abi_malformed_primitive_constructor >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem abi_malformed_bytes_outcome:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  fn_inst_ids_distinct func /\ type_memory_bytes ce ty <= outsz ==>
  abi_malformed_constructor_outcome env ty (DecBytestring n)
    ctx func cenv cx es st en base_op hi src dst outsz
Proof
  strip_tac >> irule abi_malformed_constructor_to_outcome >>
  irule abi_malformed_bytes_constructor >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

(* Application and sequential composition are one boundary: recursive clients
   supply a continuation without reopening either execution definition. *)
Theorem abi_malformed_constructor_outcome_continue:
  abi_malformed_constructor_outcome env ty di ctx func cenv cx es st en
    base_op hi src dst outsz /\ fn_has_code st en func /\
  en.cs_next_var <= ceiling.cs_next_var /\
  (case di of DecPrimWord clamp => p + 32 <= L | _ => T) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d outsz incoming /\
  fresh_vars_wrt ceiling incoming /\
  ~incoming.vs_halted /\ incoming.vs_current_bb = st.cs_current_bb /\
  incoming.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!u. abi_malformed_reflected_post env ty
      (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
       else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
      ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid incoming u /\
    fresh_vars_wrt ceiling u /\ ~u.vs_halted /\
    u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts ==>
    frag_outcome ctx func u final Q (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_outcome ctx func incoming final Q (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> irule frag_outcome_compose >>
  qexists_tac `(\u. abi_malformed_reflected_post env ty
      (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
       else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs))
      ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid incoming u /\
    fresh_vars_wrt ceiling u)` >>
  qexists_tac `en` >> simp[] >>
  fs[abi_malformed_constructor_outcome_def] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`B`, `L`, `d`, `live`] >> simp[]
QED
