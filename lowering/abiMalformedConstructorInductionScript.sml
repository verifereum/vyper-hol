(* Constructor contracts at the conditional traversal boundary. *)
Theory abiMalformedConstructorInduction
Ancestors
  abiMalformedConstructorContract abiMalformedConditionalTraversal
  abiDecoderCoherence abiDecoderWordTyped abiMalformedRecursiveInterface
  abiEncoder compileEnv fragExec list arithmetic vyperTypeSystem valueEncoding words

Theorem abi_malformed_constructor_primitive_metadata:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = di /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) ==>
  (case di of DecPrimWord clamp =>
    ~is_dynamic (vyper_to_abi_type env ty) /\ abi_sz = 32 | _ => T)
Proof
  strip_tac >> Cases_on `di` >> simp[] >>
  drule_all abi_decoder_primitive_cases >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >> gvs[]
QED

Theorem abi_malformed_constructor_traversal_child:
  abi_malformed_constructor env ty di ctx func cenv cx es child child_end
    base_op hi src dst childsz /\
  fn_has_code child child_end func /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  child_sites = abi_malformed_scratch_sites child child_end func ==>
  !B L xs cp cd dstid live ceiling incoming.
    child_end.cs_next_var <= ceiling.cs_next_var /\
    (case di of DecPrimWord clamp => cp+32 <= L | _ => T) ==>
    frag_exec ctx child child_end
      (\v. v = incoming /\
        abi_malformed_entry ctx func cenv cx es child child_sites dstid live
          base_op hi src dst B L xs cp cd childsz v /\
        fresh_vars_wrt ceiling v)
      (\u. abi_malformed_reflected_post env ty
        (if is_dynamic (vyper_to_abi_type env ty) then DROP cp xs
         else TAKE abi_sz (DROP cp xs))
        ctx func cenv cx es child.cs_next_var child_sites dstid incoming u /\
        fresh_vars_wrt ceiling u)
      (\r. ?v. r = Abort Revert_abort v)
Proof
  simp[abi_malformed_constructor_def]
QED

(* One semantic predicate for both type induction and the list fold. All
   operand positions, contexts, capacities and compiler endpoints are bound
   inside it, so list induction never fixes the next child's offsets to zero. *)
Definition abi_malformed_type_contract_def:
  abi_malformed_type_contract ce env (sf : string |-> (string # type # num) list)
      ty (tv : type_value) <=>
    !di ctx func cenv cx es st en base_op hi src dst outsz.
      type_to_abi_dec_info sf ce ty = di /\
      compile_abi_decode_to_buf dst src MLOAD base_op hi di st = ((),en) /\
      (?av. has_type (vyper_to_abi_type env ty) av) /\
      assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
      fn_inst_ids_distinct func /\ fn_has_code st en func /\
      type_memory_bytes ce ty <= outsz ==>
      abi_malformed_constructor env ty di ctx func cenv cx es st en
        base_op hi src dst outsz
End

Theorem abi_malformed_type_contract_list_nil:
  EVERY (\(ty,tv). abi_malformed_type_contract ce env sf ty tv) []
Proof
  simp[]
QED

Theorem abi_malformed_type_contract_list_cons:
  EVERY (\(ty,tv). abi_malformed_type_contract ce env sf ty tv)
    ((ty,tv)::rest) <=>
  abi_malformed_type_contract ce env sf ty tv /\
  EVERY (\(ty,tv). abi_malformed_type_contract ce env sf ty tv) rest
Proof
  simp[]
QED

Theorem abi_malformed_type_contract_induction:
  (!ce env sf bt.
    abi_decoder_scalar_valid bt /\
    abi_decoder_header ce env (BaseT bt) (BaseTV bt) ==>
    abi_malformed_type_contract ce env sf (BaseT bt) (BaseTV bt)) /\
  (!ce env sf nsid n.
    FLOOKUP env nsid = SOME (FlagArgs n) /\ n <= 256 /\
    ce.ce_flag_n_members (nsid_to_string nsid) = n /\
    abi_decoder_header ce env (FlagT nsid) (FlagTV n) ==>
    abi_malformed_type_contract ce env sf (FlagT nsid) (FlagTV n)) /\
  (!ce env sf ty tv bound.
    abi_decoder_coherent ce env sf ty tv /\
    abi_malformed_type_contract ce env sf ty tv /\
    abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) ==>
    abi_malformed_type_contract ce env sf (ArrayT ty bound) (ArrayTV tv bound)) /\
  (!ce env sf tys tvs.
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    EVERY (\(ty,tv). abi_malformed_type_contract ce env sf ty tv) (ZIP (tys,tvs)) /\
    abi_decoder_header ce env (TupleT tys) (TupleTV tvs) ==>
    abi_malformed_type_contract ce env sf (TupleT tys) (TupleTV tvs)) /\
  (!ce env sf nsid args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid)
      (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
    EVERY (\(ty,tv). abi_malformed_type_contract ce (env \\ nsid)
      (sf \\ nsid_to_string nsid) ty tv) (ZIP (MAP SND args,tvs)) /\
    abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) ==>
    abi_malformed_type_contract ce env sf (StructT nsid)
      (StructTV (ZIP (MAP FST args,tvs)))) ==>
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_malformed_type_contract ce env sf ty tv
Proof
  strip_tac >> ho_match_mp_tac abi_decoder_coherent_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  fs[LIST_REL_EL_EQN, EVERY_MEM, MEM_ZIP, EL_ZIP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
