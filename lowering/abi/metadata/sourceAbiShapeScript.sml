(* TOP-LEVEL: the source ABI type converter and source size-bound classifier
   agree for every type, including unresolved types and guarded structs.
   Helpers handle base types and the common recursive struct lookup. *)
Theory sourceAbiShape
Ancestors
  vyperABI vyperValue vyperAST contractABI finite_map list

Theorem source_abi_base_dynamic:
  !tenv bt.
    is_dynamic (vyper_base_to_abi_type bt) = vyper_is_dynamic tenv (BaseT bt)
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[vyper_base_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def] >>
  qmatch_goalsub_rename_tac `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[vyper_base_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def]
QED

Theorem source_abi_struct_dynamic_case:
  !tenv nsid.
    (!arg_kind args. FLOOKUP tenv nsid = SOME arg_kind /\ arg_kind = StructArgs args ==>
      any_dynamic (vyper_to_abi_types (tenv \\ nsid) (MAP SND args)) =
        vyper_any_dynamic (tenv \\ nsid) (MAP SND args)) ==>
    is_dynamic (vyper_to_abi_type tenv (StructT nsid)) = vyper_is_dynamic tenv (StructT nsid)
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `FLOOKUP tenv nsid`
  >- simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def] >>
  rename1 `FLOOKUP tenv nsid = SOME arg_kind` >> Cases_on `arg_kind` >>
  simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def] >>
  first_x_assum irule >> simp[]
QED

Theorem source_abi_dynamic_shape:
  (!tenv ty. is_dynamic (vyper_to_abi_type tenv ty) = vyper_is_dynamic tenv ty) /\
  (!tenv tys. any_dynamic (vyper_to_abi_types tenv tys) = vyper_any_dynamic tenv tys)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac >|
    [simp[source_abi_base_dynamic],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     MATCH_ACCEPT_TAC source_abi_struct_dynamic_case,
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def],
     simp[Once vyper_to_abi_type_def, Once vyper_is_dynamic_def, is_dynamic_def]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source ABI dynamic shape: " ^ name)
  end) (DB.thms "sourceAbiShape")
