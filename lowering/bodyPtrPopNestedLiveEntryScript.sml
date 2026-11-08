Theory bodyPtrPopNestedLiveEntry
Ancestors
  bodyPtrPopNestedLiveHandoff bodyPtrPopMemoryHeader
  exprSimPopNestedLocalMemory bodyPtrDefs valueEncoding venomState

(* The natural root address makes this usable directly with robust encoding,
   without recovering any ghost_inv parameters. *)
Theorem pop_robust_path_array_entry:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv a b mem) /\ w2n addr = b+k ==>
  val_wf (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n addr) s.vs_memory /\
  mload (w2n addr) s = n2w (LENGTH vs) /\
  (!i. w2n addr <= i /\ i < w2n addr+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
       (w2n addr) mem` by
    (asm_simp_tac bool_ss [] >>
     match_mp_tac pop_mutable_path_robust >>
     qexistsl_tac [`path`, `tv`, `a`] >> asm_simp_tac bool_ss []) >>
  `val_in_memory tv a b s.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  drule_all val_in_memory_mutable_path >> strip_tac >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (fs[val_in_memory_def, mload_def, mem_word_at_def]) >>
  drule pop_robust_dynarray_header_clean >> simp[]
QED
