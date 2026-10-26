(* Static ABI lengths equal semantic memory sizes for successfully evaluated
   types. This semantic boundary assumes no compiler metadata or coherence. *)
Theory abiCallerStaticMemory
Ancestors
  vyperTypeABI vyperABI vyperValue valueEncoding vfmConstants
  list pair arithmetic

Theorem abi_caller_static_base_memory:
  evaluate_type env (BaseT bt) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env (BaseT bt)) ==>
  static_length (vyper_to_abi_type env (BaseT bt)) = type_memory_size tv
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp_tac bool_ss [Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  simp_tac bool_ss [Once type_memory_size_def, word_size_def]
QED

Theorem abi_caller_static_fixed_array_memory:
  (!child. evaluate_type env ty = SOME child /\
     ~is_dynamic (vyper_to_abi_type env ty) ==>
     static_length (vyper_to_abi_type env ty) = type_memory_size child) /\
  evaluate_type env (ArrayT ty (Fixed n)) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_length (vyper_to_abi_type env (ArrayT ty (Fixed n))) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), type_memory_size_def]
QED

Theorem abi_caller_static_tuple_memory:
  (!tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
     ~any_dynamic (vyper_to_abi_types env tys) ==>
     static_length (Tuple (vyper_to_abi_types env tys)) = type_memory_size_list tvs) /\
  evaluate_type env (TupleT tys) = SOME tv /\
  ~any_dynamic (vyper_to_abi_types env tys) ==>
  static_length (vyper_to_abi_type env (TupleT tys)) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (TupleT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  simp[type_memory_size_def] >> first_x_assum irule >> simp[]
QED

(* Upstream form of the positional size fact also used by decoder consumers. *)
Theorem abi_caller_memory_fields_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
  type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem abi_caller_static_struct_memory:
  (!args. FLOOKUP env nsid = SOME (StructArgs args) ==>
    !tvs. LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv)
        (MAP SND args) tvs /\
      ~any_dynamic (vyper_to_abi_types (env \\ nsid) (MAP SND args)) ==>
      static_length (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) =
        type_memory_size_list tvs) /\
  evaluate_type env (StructT nsid) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env (StructT nsid)) ==>
  static_length (vyper_to_abi_type env (StructT nsid)) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs field_args)` >>
  rename1 `evaluate_types _ _ [] = SOME field_tvs` >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST field_args) = LENGTH field_tvs` by fs[LIST_REL_EL_EQN] >>
  simp[type_memory_size_def, abi_caller_memory_fields_zip] >>
  first_x_assum irule >> simp[]
QED

Theorem abi_caller_static_memory_induction:
  (!env ty. !tv. evaluate_type env ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type env ty) ==>
    static_length (vyper_to_abi_type env ty) = type_memory_size tv) /\
  (!env tys. !tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    ~any_dynamic (vyper_to_abi_types env tys) ==>
    static_length (Tuple (vyper_to_abi_types env tys)) = type_memory_size_list tvs)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >>
  conj_tac >- simp[abi_caller_static_base_memory] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_tuple_memory >> gvs[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_fixed_array_memory >> gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_struct_memory >> simp[]) >>
  conj_tac
  >- (simp[Once evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[type_memory_size_def]) >>
  conj_tac >- simp[evaluate_type_def, type_memory_size_def] >>
  conj_tac >- simp[type_memory_size_def] >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `tvs` >> Cases_on `tvs` >>
  simp[type_memory_size_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv /\ _ ==> _`
    (fn ih => drule_all ih) >> strip_tac >>
  qpat_x_assum `!tvs. LIST_REL _ _ tvs /\ _ ==> _`
    (fn ih => drule_all ih) >> simp[]
QED

Theorem abi_caller_static_memory:
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_length (vyper_to_abi_type env ty) = type_memory_size tv
Proof
  metis_tac[abi_caller_static_memory_induction]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_STATIC_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller static memory not kernel closed: " ^ n)
  end) (DB.thms "abiCallerStaticMemory");
