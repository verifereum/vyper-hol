(* Runtime immutable representation resources for raise/assert reasons.
   Reuse the semantic copy boundary: do not duplicate sub-layout decoding. *)
Theory reasonCodeResourcesPtr
Ancestors
  exprSimCopy reasonResourcesPtr reasonCodeCopyPtr representationCleanPtr
  exprSimProps valueEncoding valueEncodingDefs valueEncodingProps loweringPosts bodyPtrDefs
  immutableConstructorRelation immutableCopyExecution
  compileEnv venomState venomMemProofs valueEncodingProofs words list arithmetic
  vyperInterpreter vyperState vyperValue

Theorem immutable_holds_read_result_value:
  read_result cx tv es = (INL v,es) ==>
  (immutable_holds cenv cx ty tv a es s <=>
   immutable_holds cenv cx ty (Value v) a es s)
Proof
  strip_tac >> simp[immutable_holds_def, read_result_def, return_def]
QED

Theorem immutable_source_resources:
  immutable_holds cenv cx ty tv a es s /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME vt ==>
  val_wf vt v /\ w2n a + type_memory_size vt < dimword(:256) /\
  val_store_size vt v <= type_memory_size vt
Proof
  strip_tac >>
  `immutable_holds cenv cx ty (Value v) a es s` by
    metis_tac[immutable_holds_read_result_value] >>
  drule_all immutable_holds_bounds >> strip_tac >>
  simp[val_store_size_le]
QED

Theorem clean_memory_representation_ptr:
  evaluate_type (get_tenv cx) ty = SOME vt /\
  val_wf vt v /\ val_in_memory vt v (w2n b) s.vs_memory /\
  lookup_var root s = SOME b /\ ptr_covers G tn root s capacity /\
  val_store_size vt v <= capacity /\
  (!i. w2n b <= i /\ i < w2n b + val_footprint vt v ==> i NOTIN tn.t_mem) ==>
  ptr_mem_ok cx ty v (Var root) G tn s
Proof
  strip_tac >> simp[ptr_mem_ok_def, eval_operand_def] >> conj_tac
  >- (rpt strip_tac >> irule val_in_memory_footprint_agree >>
      conj_tac >- simp[] >> qexists_tac `s.vs_memory` >> simp[] >>
      irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
      rename1 `i < val_footprint vt v` >>
      `w2n b + i NOTIN tn.t_mem` by
        (first_x_assum irule >> decide_tac) >>
      `mem_bytes_at (w2n b+i) 1 s.vs_memory =
       mem_bytes_at (w2n b+i) 1 mem` by metis_tac[mem_agree_outside_def] >>
      pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  qpat_x_assum `ptr_covers _ _ _ _ _` mp_tac >>
  simp[ptr_covers_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

(* Only the data section is framed between the source boundary and the
   copy start: fresh allocation may have expanded the destination memory. *)
Theorem code_reason_snapshot_contents:
  stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx ty tv a es u' /\
  read_result cx tv es = (INL (StringV str),es) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  s.vs_data_section = u.vs_data_section /\
  w2n b + type_memory_size (BaseTV (StringT max)) < dimword(:256) /\
  z.vs_memory = (immutable_transfers F F a b
    (type_slot_size (BaseTV (StringT max))) 0 s).vs_memory ==>
  val_wf (BaseTV (StringT max)) (StringV str) /\
  val_in_memory (BaseTV (StringT max)) (StringV str) (w2n b) z.vs_memory
Proof
  strip_tac >> drule_all immutable_source_resources >> strip_tac >>
  drule_all immutable_holds_data >> strip_tac >> gvs[] >>
  `immutable_transfers F F a b (type_slot_size (BaseTV (StringT max))) 0 s =
   write_memory_with_expansion (w2n b)
     (mem_bytes_at (w2n a) (type_memory_size (BaseTV (StringT max)))
       s.vs_data_section) s` by
    (qspecl_then [`type_slot_size (BaseTV (StringT max))`, `w2n a`,
       `w2n b`, `0`, `s`] mp_tac immutable_runtime_transfers_snapshot >>
     gvs[type_slot_size_def, type_memory_size_slots, mem_bytes_at_def]) >>
  simp[] >> irule immutable_copy_memory_value >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem code_reason_normalization_resources:
  stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx ty tv a es u' /\
  read_result cx tv es = (INL (StringV str),es) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  s.vs_data_section = u.vs_data_section /\
  w2n b + type_memory_size (BaseTV (StringT max)) < dimword(:256) /\
  z.vs_memory = (immutable_transfers F F a b
    (type_slot_size (BaseTV (StringT max))) 0 s).vs_memory /\
  lookup_var root z = SOME b /\
  ptr_covers G tn root z (type_memory_size (BaseTV (StringT max))) /\
  (!i. w2n b <= i /\ i < w2n b + type_memory_size (BaseTV (StringT max)) ==>
       i NOTIN tn.t_mem) ==>
  val_wf (BaseTV (StringT max)) (StringV str) /\
  ptr_mem_ok cx ty (StringV str) (Var root) G tn z /\
  32 + 32 * word_size (LENGTH str) <= type_memory_size (BaseTV (StringT max))
Proof
  strip_tac >> drule_all code_reason_snapshot_contents >> strip_tac >> simp[] >>
  drule val_store_size_le >> simp[val_store_size_def] >> strip_tac >>
  irule clean_memory_representation_ptr >>
  goal_assum (drule_at Any) >> simp[val_store_size_def] >>
  qexists_tac `type_memory_size (BaseTV (StringT max))` >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >>
  drule val_footprint_le >> simp[] >> decide_tac
QED
