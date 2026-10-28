(* TOP-LEVEL: stores of typed lowered values establish complete local layouts.
   Word stores and same-layout aggregate copies preserve the other live locals.
   Helpers connect source typing, allocation capacities and disjoint writes. *)
Theory localValueStoreProps
Ancestors
  valueLoadProps localPtrsProps memoryValueDefs memoryValueTyping memoryValueRelocation
  memoryReadProps valueEncoding valueEncodingProps compileEnv vyperTyping vyperValue
  vyperState venomState venomExecSemantics venomMemProps
  finite_map list words arithmetic

Theorem evaluated_word_memory_size:
  !tenv ty tv.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty ==> type_memory_size tv = 32
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  FIRST [drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_word_type_def, type_memory_size_def] >>
      rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
      gvs[is_word_type_def, type_memory_size_def],
    gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def]]
QED

Theorem mstore_local_region_frame:
  !ss dst region_size value offset byte_count.
    32 <= region_size /\ regions_disjoint dst region_size offset byte_count ==>
    mem_bytes_at offset byte_count (mstore dst value ss).vs_memory =
      mem_bytes_at offset byte_count ss.vs_memory
Proof
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem mcopy_local_region_frame:
  !ss dst src copied_count region_size offset byte_count.
    copied_count <= region_size /\ regions_disjoint dst region_size offset byte_count ==>
    mem_bytes_at offset byte_count (mcopy dst src copied_count ss).vs_memory =
      mem_bytes_at offset byte_count ss.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `read_memory offset byte_count (mcopy dst src copied_count ss) =
    read_memory offset byte_count ss` by
    (irule read_memory_mcopy_frame >> fs[regions_disjoint_def] >> decide_tac) >>
  fs[read_memory_eq_mem_bytes_at]
QED

Theorem store_lowered_aggregate_memory_value_rel:
  !ty tv v src_op src_addr dst copied_count ss.
    ~is_word_type ty /\ lowered_value_rel ty tv v src_op ss /\
    eval_operand src_op ss = SOME src_addr /\ type_memory_size tv <= copied_count ==>
    memory_value_rel tv v dst (mcopy dst (w2n (src_addr:bytes32)) copied_count ss).vs_memory
Proof
  rpt strip_tac >> gvs[lowered_value_rel_def] >>
  irule mcopy_establishes_memory_value_rel >> simp[] >>
  irule value_has_type_val_wf >> simp[]
QED

Theorem local_ptrs_rel_store_word:
  !tenv ty func cenv scopes scopes' ss name entry p region_size addr arg_op value_word.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes name scopes' = SOME entry /\
    (!n. n <> name ==> lookup_scopes n scopes' = lookup_scopes n scopes) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\
    lookup_var p ss = SOME addr /\ local_backed func p ss (w2n (addr:bytes32)) region_size /\
    w2n (addr:bytes32) + region_size <= ss.vs_alloca_next /\ type_memory_size entry.type <= region_size /\
    evaluate_type tenv ty = SOME entry.type /\ is_word_type ty /\
    lowered_value_rel ty entry.type entry.value arg_op ss /\
    eval_operand arg_op ss = SOME value_word /\
    (!n b sz. n <> name /\ local_region cenv scopes ss n b sz ==>
      regions_disjoint (w2n (addr:bytes32)) region_size b sz) ==>
    local_ptrs_rel func cenv scopes' (mstore (w2n (addr:bytes32)) value_word ss)
Proof
  rpt strip_tac >>
  `type_memory_size entry.type = 32` by (drule_all evaluated_word_memory_size >> simp[]) >>
  `val_wf entry.type entry.value` by
    (irule value_has_type_val_wf >> fs[lowered_value_rel_def]) >>
  `memory_value_rel entry.type entry.value (w2n (addr:bytes32))
    (mstore (w2n (addr:bytes32)) value_word ss).vs_memory` by
    (mp_tac (Q.SPECL [`tenv`, `ty`, `entry.type`, `entry.value`, `arg_op`,
      `value_word`, `w2n (addr:bytes32)`, `ss`] store_lowered_word_memory_value_rel) >> simp[]) >>
  `(mstore (w2n (addr:bytes32)) value_word ss).vs_vars = ss.vs_vars /\
   (mstore (w2n (addr:bytes32)) value_word ss).vs_allocas = ss.vs_allocas /\
   (mstore (w2n (addr:bytes32)) value_word ss).vs_alloca_next = ss.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `scopes'`, `ss`,
    `mstore (w2n (addr:bytes32)) value_word ss`, `name`, `entry`, `p`, `region_size`, `addr`]
    local_ptrs_rel_write_local) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      simp[lookup_var_def] >> NO_TAC,
      rpt strip_tac >> gvs[] >> decide_tac,
      rpt strip_tac >>
      qpat_x_assum `!n b sz. P n b sz ==> regions_disjoint _ _ b sz` (fn th => drule_all th) >>
      DISCH_TAC >> sym_tac >> irule mstore_local_region_frame >>
      qexists_tac `region_size` >> simp[]]) >> simp[]
QED

Theorem local_ptrs_rel_store_aggregate:
  !ty func cenv scopes scopes' ss name entry p region_size addr src_op src_addr copied_count.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes name scopes' = SOME entry /\
    (!n. n <> name ==> lookup_scopes n scopes' = lookup_scopes n scopes) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\
    lookup_var p ss = SOME addr /\ local_backed func p ss (w2n (addr:bytes32)) region_size /\
    w2n (addr:bytes32) + region_size <= ss.vs_alloca_next /\ type_memory_size entry.type <= copied_count /\
    copied_count <= region_size /\ ~is_word_type ty /\
    lowered_value_rel ty entry.type entry.value src_op ss /\
    eval_operand src_op ss = SOME src_addr /\
    (!n b sz. n <> name /\ local_region cenv scopes ss n b sz ==>
      regions_disjoint (w2n (addr:bytes32)) region_size b sz) ==>
    local_ptrs_rel func cenv scopes' (mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss)
Proof
  rpt strip_tac >>
  `val_wf entry.type entry.value` by
    (irule value_has_type_val_wf >> fs[lowered_value_rel_def]) >>
  `memory_value_rel entry.type entry.value (w2n (addr:bytes32))
    (mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss).vs_memory` by
    (drule_all store_lowered_aggregate_memory_value_rel >> simp[]) >>
  `(mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss).vs_vars = ss.vs_vars /\
   (mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss).vs_allocas = ss.vs_allocas /\
   (mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss).vs_alloca_next = ss.vs_alloca_next` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `scopes'`, `ss`,
    `mcopy (w2n (addr:bytes32)) (w2n (src_addr:bytes32)) copied_count ss`,
    `name`, `entry`, `p`, `region_size`, `addr`] local_ptrs_rel_write_local) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      simp[lookup_var_def] >> NO_TAC,
      rpt strip_tac >> gvs[] >> decide_tac,
      rpt strip_tac >>
      qpat_x_assum `!n b sz. P n b sz ==> regions_disjoint _ _ b sz` (fn th => drule_all th) >>
      DISCH_TAC >> sym_tac >> irule mcopy_local_region_frame >>
      qexists_tac `region_size` >> simp[]]) >> simp[]
QED

val () = List.app (fn theory => List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete local store theorem: " ^ theory ^ "." ^ name)
  end) (DB.thms theory)) ["localPtrsProps", "localValueStoreProps"]
