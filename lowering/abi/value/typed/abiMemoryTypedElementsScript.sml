(* TOP-LEVEL: convert an arbitrary typed homogeneous sequence in complete
   memory into recursive child encodings and exact static head widths. *)
Theory abiMemoryTypedElements
Ancestors
  abiMemoryTypedDefs sourceAbiArray sourceAbiStaticWidth memoryValueAbiStatic
  memoryValueDefs valueEncoding vyperABI vyperValue vyperTyping
  vyperAssignPreservesType contractABI list rich_list arithmetic

Theorem abi_typed_memory_element:
  !env ty tv info v av source mem.
    abi_typed_memory env ty info /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ memory_value_rel tv v source mem /\
    vyper_to_abi env ty v = SOME av ==>
    abi_memory_encoding info source (type_memory_size tv) mem (enc (vyper_to_abi_type env ty) av) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==>
      LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `abi_typed_memory env ty info` (mp_tac o REWRITE_RULE [abi_typed_memory_def]) >>
      disch_then (qspecl_then [`tv`, `v`, `av`, `source`, `type_memory_size tv`, `mem`] mp_tac) >>
      simp[]) >>
  strip_tac >> drule_all memory_value_rel_static_abi >>
  disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >> simp[]
QED

Theorem abi_typed_memory_elements:
  !env ty tv info vs avs source mem.
    abi_typed_memory env ty info /\ evaluate_type env ty = SOME tv /\
    all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs /\
    (!i. i < LENGTH vs ==>
      memory_value_rel tv (EL i vs) (source + i * type_memory_size tv) mem) ==>
    LENGTH avs = LENGTH vs /\
    (!i. i < LENGTH avs ==>
      abi_memory_encoding info (source + i * type_memory_size tv) (type_memory_size tv) mem
        (enc (vyper_to_abi_type env ty) (EL i avs))) /\
    EVERY (\av. ~is_dynamic (vyper_to_abi_type env ty) ==>
      LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv) avs
Proof
  rpt gen_tac >> strip_tac >> drule vyper_to_abi_same_EL >> strip_tac >> simp[] >>
  `!i. i < LENGTH vs ==>
    abi_memory_encoding info (source + i * type_memory_size tv) (type_memory_size tv) mem
      (enc (vyper_to_abi_type env ty) (EL i avs)) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==>
      LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) = type_memory_size tv)` by
    (qx_gen_tac `i` >> DISCH_TAC >>
     qspecl_then [`env`, `ty`, `tv`, `info`, `EL i vs`, `EL i avs`,
       `source + i * type_memory_size tv`, `mem`] mp_tac abi_typed_memory_element >>
     impl_tac >- fs[all_have_type_EVERY, EVERY_EL] >> simp[]) >>
  simp[EVERY_EL]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory elements: " ^ name)
  end) (DB.thms "abiMemoryTypedElements")
