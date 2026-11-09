(* Placement interface probe: the zero-footprint alternative is explicit. *)
Theory exprExtRequestTransportProbe
Ancestors
  loweringPosts vyperTypeSystem valueEncodingProps

Theorem extrequest_footprint_frontier:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      b + sz <= s.vs_alloca_next) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
      b + sz <= s.vs_alloca_next) ==>
  val_footprint tv v = 0 \/
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  simp_tac bool_ss [expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Dynamic bytes/string always have a length word; all other positive
   memory types use their full memory size as their footprint. *)
Theorem extrequest_footprint_positive:
  0 < type_memory_size tv ==> 0 < val_footprint tv v
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[]
QED

Theorem extrequest_assignable_footprint_frontier:
  expr_val_at cenv cx ty sa sb es v op s /\
  assignable_type (get_tenv cx) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      b + sz <= s.vs_alloca_next) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
      b + sz <= s.vs_alloca_next) ==>
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >> drule_all extrequest_footprint_frontier >>
  drule_all assignable_type_slot_size_pos >> strip_tac >>
  `0 < type_memory_size tv` by metis_tac[type_memory_size_pos] >>
  drule extrequest_footprint_positive >>
  disch_then (qspec_then `v` assume_tac) >> simp[]
QED
