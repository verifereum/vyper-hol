(* Source evaluator inversions for recursive coherence. These constructors
   reuse the existing array/tuple interfaces and the checked metadata header. *)
Theory abiCallerCoherenceNodes
Ancestors
  abiCallerMetadata abiCallerStructMap abiDecoderConstructors abiDecoderCoherence
  abiDecoderPrimitiveCaller compileEnv vyperValue vyperABI vyperTypeABI
  finite_map list pair

Theorem abi_caller_array_coherent:
  evaluate_type env (ArrayT ty bound) = SOME atv /\
  (!tv. evaluate_type env ty = SOME tv ==>
    abi_decoder_coherent ce env sf ty tv) ==>
  abi_decoder_coherent ce env sf (ArrayT ty bound) atv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (ArrayT _ _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all decoder_caller_array >> simp[]
QED

Theorem abi_caller_tuple_coherent:
  evaluate_type env (TupleT tys) = SOME tv /\
  (!tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs) ==>
  abi_decoder_coherent ce env sf (TupleT tys) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (TupleT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  irule decoder_caller_tuple >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem abi_caller_flag_metadata_coherent:
  abi_caller_metadata ce root /\ env SUBMAP root /\
  evaluate_type env (FlagT nsid) = SOME tv ==>
  abi_decoder_coherent ce env sf (FlagT nsid) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (FlagT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (FlagArgs members)` >>
  fs[abi_caller_metadata_def] >>
  `ce.ce_flag_n_members (nsid_to_string nsid) = members` by
    (qpat_x_assum `!env nsid n. _ ==> ce.ce_flag_n_members _ = n` irule >>
     qexists_tac `env` >> simp[]) >>
  `abi_decoder_header ce env (FlagT nsid) (FlagTV members)` by
    (qpat_x_assum `!env ty tv. _ ==> abi_decoder_header ce env ty tv` irule >> simp[]) >>
  simp[abi_decoder_coherent_flag_iff]
QED

Theorem abi_caller_struct_map_namespace:
  abi_caller_struct_map sf env /\
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  FST nsid = NONE
Proof
  simp[abi_caller_struct_map_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_COHERENCE_NODES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller coherence node not kernel closed: " ^ n)
  end) (DB.thms "abiCallerCoherenceNodes");
