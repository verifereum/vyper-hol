(* Pure interfaces used by recursive coherence induction. The constructed
   compiler theorem discharges each interface from checked namespaces and
   the actual builder; callers need not assume this metadata predicate. *)
Theory abiCallerMetadata
Ancestors
  abiCallerHeader abiCallerLeaves abiCallerStructMetadata abiCallerStructMap
  compileVyper compileEnv vyperContext vyperValue
  finite_map list

Definition abi_caller_metadata_def:
  abi_caller_metadata ce root <=>
    (!env ty tv. env SUBMAP root /\ evaluate_type env ty = SOME tv ==>
      abi_decoder_header ce env ty tv) /\
    (!env nsid n. env SUBMAP root /\ FLOOKUP env nsid = SOME (FlagArgs n) ==>
      ce.ce_flag_n_members (nsid_to_string nsid) = n) /\
    (!env sf name args fields tvs.
      env SUBMAP root /\ sf SUBMAP ce.ce_struct_fields /\
      abi_caller_struct_map sf env /\
      FLOOKUP env (NONE,name) = SOME (StructArgs args) /\
      evaluate_types (env \\ (NONE,name)) (MAP SND args) [] = SOME tvs /\
      FLOOKUP sf name = SOME fields ==>
      EVERY (\(field_name,ty,sz). sz = type_memory_bytes ce ty) fields)
End

Theorem abi_caller_constructed_metadata:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] ==>
  abi_caller_metadata
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) (type_env tops)
Proof
  strip_tac >> simp[abi_caller_metadata_def] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all abi_caller_header >> simp[])
  >- (rpt strip_tac >>
      rename1 `FLOOKUP env nsid = SOME (FlagArgs members)` >>
      `FLOOKUP (type_env tops) nsid = SOME (FlagArgs members)` by
        (irule FLOOKUP_SUBMAP >> qexists_tac `env` >> simp[]) >>
      drule_all abi_caller_flag_count >> simp[]) >>
  rpt strip_tac >> drule_all abi_caller_struct_field_memory >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_METADATA_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller metadata not kernel closed: " ^ n)
  end) (DB.thms "abiCallerMetadata");
