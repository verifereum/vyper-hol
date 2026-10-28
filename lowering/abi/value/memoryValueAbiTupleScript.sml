(* TOP-LEVEL: complete tuple layouts compose static source ABI encodings.
   Helpers: field layouts and field typing project to tuple layouts. *)
Theory memoryValueAbiTuple
Ancestors
  memoryValueAbiArray memoryValueDefs sourceAbiArray valueEncoding
  vyperABI vyperValue vyperTyping contractABI
  list rich_list pair option arithmetic

Definition memory_tuple_abi_def:
  memory_tuple_abi env ts tvs <=>
    !vs avs offset mem.
      memory_tuple_rel tvs vs offset mem /\ values_have_types tvs vs /\
      vyper_to_abi_list env ts vs = SOME avs /\
      ~any_dynamic (vyper_to_abi_types env ts) ==>
      mem_bytes_at offset (type_memory_size_list tvs) mem =
        enc (Tuple (vyper_to_abi_types env ts)) (ListV avs)
End

Theorem memory_tuple_abi_nil:
  !env. memory_tuple_abi env [] []
Proof
  gen_tac >> PURE_REWRITE_TAC [memory_tuple_abi_def] >> rpt gen_tac >> Cases_on `vs` >>
  simp[memory_value_rel_def, value_has_type_def, type_memory_size_def,
    mem_bytes_at_def, Once enc_def, REV_REVERSE_LEM]
QED

Theorem memory_tuple_abi_cons:
  !env ty tv ts tvs.
    memory_value_abi env ty tv /\ memory_tuple_abi env ts tvs ==>
    memory_tuple_abi env (ty::ts) (tv::tvs)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [memory_tuple_abi_def] >> rpt gen_tac >>
  Cases_on `vs` >> simp[memory_value_rel_def] >>
  simp[value_has_type_def, AllCaseEqs(), type_memory_size_def] >> rpt strip_tac >> gvs[] >>
  rename1 `vyper_to_abi env ty head_value = SOME head_abi` >>
  rename1 `vyper_to_abi_list env ts tail_values = SOME tail_abis` >>
  `mem_bytes_at offset (type_memory_size tv) mem = enc (vyper_to_abi_type env ty) head_abi` by
    (qpat_x_assum `memory_value_abi env ty tv`
       (mp_tac o REWRITE_RULE [memory_value_abi_def]) >>
     disch_then (qspecl_then [`head_value`, `head_abi`, `offset`, `mem`] mp_tac) >>
     impl_tac >- simp[] >> simp[]) >>
  `mem_bytes_at (offset + type_memory_size tv) (type_memory_size_list tvs) mem =
    enc (Tuple (vyper_to_abi_types env ts)) (ListV tail_abis)` by
    (qpat_x_assum `memory_tuple_abi env ts tvs`
       (mp_tac o REWRITE_RULE [memory_tuple_abi_def]) >>
     disch_then (qspecl_then [`tail_values`, `tail_abis`, `offset + type_memory_size tv`, `mem`] mp_tac) >>
     impl_tac >- simp[] >> simp[]) >>
  fs[mem_bytes_at_split, enc_tuple_static_acc] >> gvs[]
QED

Theorem memory_tuple_abi_list:
  !ts tvs env.
    LIST_REL (\ty tv. memory_value_abi env ty tv) ts tvs ==>
    memory_tuple_abi env ts tvs
Proof
  Induct_on `ts` >> Cases_on `tvs` >>
  simp[memory_tuple_abi_nil, memory_tuple_abi_cons]
QED

Theorem memory_value_abi_tuple:
  !env ts tvs.
    memory_tuple_abi env ts tvs ==> memory_value_abi env (TupleT ts) (TupleTV tvs)
Proof
  rpt strip_tac >> PURE_REWRITE_TAC [memory_value_abi_def] >> rpt gen_tac >>
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV array_value` >> Cases_on `array_value` >>
  simp[value_has_type_def, AllCaseEqs(), type_memory_size_def] >> rpt strip_tac >>
  rename1 `vyper_to_abi_list env ts values = SOME encoded` >>
  qpat_x_assum `memory_tuple_abi env ts tvs`
    (mp_tac o REWRITE_RULE [memory_tuple_abi_def]) >>
  disch_then (qspecl_then [`values`, `encoded`, `offset`, `mem`] mp_tac) >>
  impl_tac >- fs[memory_value_rel_def] >> gvs[]
QED

Theorem memory_fields_rel_tuple:
  !tvs fields offset mem.
    memory_fields_rel tvs fields offset mem ==>
    memory_tuple_rel (MAP SND tvs) (MAP SND fields) offset mem
Proof
  Induct_on `tvs` >> Cases_on `fields` >> simp[memory_value_rel_def] >>
  rpt gen_tac >> rename1 `memory_fields_rel (entry::rest) _ _ _` >>
  PairCases_on `entry` >> rename1 `memory_fields_rel _ (value_entry::values) _ _` >>
  PairCases_on `value_entry` >> simp[memory_value_rel_def]
QED

Theorem struct_has_type_tuple:
  !tvs fields.
    struct_has_type tvs fields ==> values_have_types (MAP SND tvs) (MAP SND fields)
Proof
  Induct_on `tvs` >> Cases_on `fields` >> simp[value_has_type_def] >>
  rpt gen_tac >> rename1 `struct_has_type (entry::rest) _` >> PairCases_on `entry` >>
  rename1 `struct_has_type _ (value_entry::values)` >> PairCases_on `value_entry` >>
  simp[value_has_type_def]
QED

Theorem type_memory_size_fields_list:
  !tvs. type_memory_size_fields tvs = type_memory_size_list (MAP SND tvs)
Proof
  Induct >> simp[type_memory_size_def] >> Cases >> simp[type_memory_size_def]
QED

Theorem memory_value_abi_struct:
  !env nsid args tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    memory_tuple_abi (env \\ nsid) (MAP SND args) (MAP SND tvs) ==>
    memory_value_abi env (StructT nsid) (StructTV tvs)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [memory_value_abi_def] >> rpt gen_tac >>
  Cases_on `v` >>
  simp[value_has_type_def, AllCaseEqs(), type_memory_size_def] >> rpt strip_tac >>
  rename1 `StructV values` >>
  rename1 `vyper_to_abi_list (env \\ nsid) (MAP SND args) (MAP SND values) = SOME encoded` >>
  `memory_tuple_rel (MAP SND tvs) (MAP SND values) offset mem` by
    (irule memory_fields_rel_tuple >> fs[memory_value_rel_def]) >>
  `values_have_types (MAP SND tvs) (MAP SND values)` by
    (irule struct_has_type_tuple >> simp[]) >>
  qpat_x_assum `memory_tuple_abi (env \\ nsid) (MAP SND args) (MAP SND tvs)`
    (mp_tac o REWRITE_RULE [memory_tuple_abi_def]) >>
  disch_then (qspecl_then [`MAP SND values`, `encoded`, `offset`, `mem`] mp_tac) >>
  impl_tac >- simp[] >> simp[type_memory_size_fields_list] >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory/ABI tuple theorem: " ^ name)
  end) (DB.thms "memoryValueAbiTuple")
