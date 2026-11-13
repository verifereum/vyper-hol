(* Boundary probes for pointer-safe unwrap. *)
Theory exprPtrUnwrapFacts
Ancestors
  bodyPtrDefs representationCleanPtr loweringPosts

Theorem ptr_mem_ok_prim_clean:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\
  ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
   (?k. v = FlagV k) \/ (?n. v = DecimalV n)) ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rw[ptr_mem_ok_def] >>
  irule robust_val_in_memory_prim_clean >>
  metis_tac[]
QED

(* Word types include fixed bytes and addresses, not just primitive value
   constructors. Use the typed word observer rather than a shape restriction. *)
Theorem ptr_mem_ok_word_clean:
  ptr_mem_ok cx t v op G tn s /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n w) mem = typed_val_to_w256 tv v` by
    (rpt strip_tac >> irule exprSimPropsTheory.val_in_memory_word_type >>
     conj_tac >- (qexistsl [`t`, `get_tenv cx`] >> simp[]) >>
     gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem ptr_mem_ok_read_covers:
  ptr_mem_ok cx t v op G tn s /\ op_taint tn op = {} /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 /\
  n <= val_store_size tv v ==>
  ?p. op = Var p /\ ptr_covers G tn p s n
Proof
  strip_tac >> gvs[ptr_mem_ok_def] >>
  simp[ptr_covers_def] >>
  qexists_tac `w` >> gvs[venomStateTheory.eval_operand_def]
QED

Theorem word_value_memory_extent:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==>
  val_footprint tv v = 32 /\ val_store_size tv v = 32
Proof
  Cases_on `t` >> simp[compileEnvTheory.is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[compileEnvTheory.is_word_type_def] >>
      Cases_on `v` >>
      simp[vyperValueTheory.evaluate_type_def, val_footprint_def,
           exprSimPropsTheory.val_store_size_def,
           valueEncodingTheory.type_memory_size_def] >>
      rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def] >>
      Cases_on `b` >>
      gvs[compileEnvTheory.is_word_type_def,
          vyperValueTheory.evaluate_type_def, val_footprint_def,
          exprSimPropsTheory.val_store_size_def,
          valueEncodingTheory.type_memory_size_def]) >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `v` >>
  simp[val_footprint_def, exprSimPropsTheory.val_store_size_def,
       valueEncodingTheory.type_memory_size_def]
QED

Theorem ptr_mem_ok_word_input:
  ptr_mem_ok cx t v op G tn s /\ op_taint tn op = {} /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\ eval_operand op s = SOME w ==>
  (?p. op = Var p /\ ptr_covers G tn p s 32) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> reverse conj_tac >- metis_tac[ptr_mem_ok_word_clean] >>
  `val_footprint tv v = 32 /\ val_store_size tv v = 32` by
    metis_tac[word_value_memory_extent] >>
  irule ptr_mem_ok_read_covers >> simp[] >>
  qexistsl [`cx`, `t`, `tv`, `v`] >> simp[]
QED
