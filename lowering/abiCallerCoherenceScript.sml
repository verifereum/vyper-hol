(* Recursive caller coherence from actual checked construction. The general
   induction carries semantic/compiler submaps through struct descent. The
   public constructed theorem assumes only namespaces, assignability and
   successful source type evaluation. *)
Theory abiCallerCoherence
Ancestors
  abiCallerCoherenceNodes abiCallerCoherenceStruct abiCallerMetadata
  abiCallerStructMap abiDecoderCoherence abiDecoderPrimitiveCaller
  compileVyper compileEnv vyperTypeSystem vyperValue vyperABI
  vyperContext finite_map list

Theorem abi_caller_coherent_from_metadata:
  abi_caller_metadata ce root ==>
  (!env ty. !tv sf.
    evaluate_type env ty = SOME tv /\ assignable_type env ty /\
    env SUBMAP root /\ sf SUBMAP ce.ce_struct_fields /\
    abi_caller_struct_map sf env ==>
    abi_decoder_coherent ce env sf ty tv) /\
  (!env tys. !tvs sf.
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    EVERY (assignable_type env) tys /\
    env SUBMAP root /\ sf SUBMAP ce.ce_struct_fields /\
    abi_caller_struct_map sf env ==>
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs)
Proof
  strip_tac >> ho_match_mp_tac vyper_to_abi_type_ind >>
  conj_tac >- simp[abi_decoder_base_caller_coherent] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
      irule abi_caller_tuple_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      irule abi_caller_array_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      irule abi_caller_array_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_struct_coherent >> simp[] >>
      qexists_tac `root` >> simp[] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!args. FLOOKUP _ _ = SOME (StructArgs args) ==> _`
        (fn ih => drule_all ih) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all abi_caller_flag_metadata_coherent >> simp[]) >>
  conj_tac >- simp[assignable_type_def] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`tvs`, `sf`] >>
  Cases_on `tvs` >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_caller_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields ty tv
Proof
  strip_tac >>
  `abi_caller_metadata
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)` by
    (irule abi_caller_constructed_metadata >> qexists_tac `in_deploy` >> simp[]) >>
  `abi_caller_struct_map
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields (type_env tops)` by
    (irule abi_caller_constructed_struct_map >> qexists_tac `in_deploy` >> simp[]) >>
  drule abi_caller_coherent_from_metadata >> strip_tac >>
  first_x_assum irule >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_COHERENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller coherence not kernel closed: " ^ n)
  end) (DB.thms "abiCallerCoherence");
