(* TOP-LEVEL: dynamic-array repacking preserves its length header and
   disjoint typed memory while copying only live payload elements.
   Helpers expose words through typed memory so the existing frames apply. *)
Theory typedDynLoopMemory
Ancestors
  dynCopyPrefixExec typedSArrayDynInvariant typedArrayCopyMemory
  memoryValueDefs memoryValueFrame valueEncoding valueEncodingProps
  vyperValue venomState list words arithmetic integer_word

Theorem memory_uint256_word:
  !offset mem (word:bytes32).
    memory_value_rel (BaseTV (UintT 256)) (IntV (&w2n word)) offset mem <=>
    mem_word_at offset mem = word
Proof
  simp[memory_value_rel_def, val_in_memory_def, val_to_w256_def, i2w_pos]
QED

Theorem array_copy_frame_word:
  !tv copy_count dst_off offset before_mem after_mem word.
    array_copy_frame tv copy_count dst_off before_mem after_mem /\
    mem_word_at offset before_mem = word /\
    (offset + 32 <= dst_off \/ dst_off + copy_count * type_memory_size tv <= offset) ==>
    mem_word_at offset after_mem = word
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  disch_then (qspecl_then [`BaseTV (UintT 256)`, `IntV (&w2n (word:bytes32))`, `offset`] mp_tac) >>
  impl_tac >- simp[memory_uint256_word, val_wf_def, type_memory_size_def] >> simp[memory_uint256_word]
QED

Theorem dyn_copy_prefix_header:
  !var_base dst_addr src_addr n ss.
    mem_word_at (w2n dst_addr) (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_memory = n2w n
Proof
  simp[dyn_copy_prefix_result_memory, mstore_mem_word_at_same]
QED

Theorem dyn_copy_prefix_preserves_value:
  !tv v offset var_base dst_addr src_addr n ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= w2n dst_addr \/ w2n dst_addr + 32 <= offset) ==>
    memory_value_rel tv v offset (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rewrite_tac[dyn_copy_prefix_result_memory] >> irule mstore_preserves_memory_value_rel >> simp[]
QED

Theorem dynarray_copy_payload_layout:
  !ftv atv vs capacity src_data dst initial_mem after_mem.
    array_copy_memory_inv ftv atv (\j. EL j vs) (LENGTH vs) src_data (dst + 32)
      initial_mem (LENGTH vs) after_mem /\ mem_word_at dst initial_mem = n2w (LENGTH vs) ==>
    memory_value_rel (ArrayTV ftv (Dynamic capacity)) (ArrayV (DynArrayV vs)) dst after_mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_copy_memory_inv _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_memory_inv_def] >> strip_tac >>
  `mem_word_at dst after_mem = n2w (LENGTH vs)` by
    (mp_tac (Q.SPECL [`ftv`, `LENGTH (vs:value list)`, `dst + 32`, `dst`,
       `initial_mem`, `after_mem`, `(n2w (LENGTH (vs:value list)):bytes32)`] array_copy_frame_word) >> simp[]) >>
  rewrite_tac[array_copy_dynamic_layout] >> asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem dynarray_copy_full_frame:
  !tv capacity dst n ss after_mem.
    n <= capacity /\ array_copy_frame tv n (dst + 32)
      (mstore dst (n2w n) ss).vs_memory after_mem ==>
    !other_tv other_v offset.
      memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst \/
        dst + type_memory_size (ArrayTV tv (Dynamic capacity)) <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `n * type_memory_size tv <= capacity * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >> DISCH_TAC >>
  `memory_value_rel other_tv other_v offset (mstore dst (n2w n) ss).vs_memory` by
    (mp_tac (Q.SPECL [`other_tv`, `other_v`, `offset`, `dst`, `(n2w n:bytes32)`, `ss`]
       mstore_preserves_memory_value_rel) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  disch_then (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive dynamic-array memory theorem: " ^ name)
  end) (DB.thms "typedDynLoopMemory")
