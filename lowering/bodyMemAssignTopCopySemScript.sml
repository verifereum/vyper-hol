(* Non-bytestring values occupy their full declared memory footprint.
   Storage-copy semantics and compiler boundaries are shared with S1. *)
Theory bodyMemAssignTopCopySem
Ancestors
  stmtSimAssignStorageCopy exprSimHash exprSimProps loweringPosts
  compileEnv vyperValue vyperTyping valueEncodingProps
  words arithmetic

Theorem topcopy_val_footprint:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

Theorem topcopy_post_words:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv w.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    eval_operand op s = SOME w ==>
    type_slot_size tv < dimword (:256) /\
    (!i. i < type_slot_size tv ==>
         mload (w2n (w + n2w i * 32w)) s =
           mem_word_at (w2n w + 32*i) s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_post_footprint_bound >> strip_tac >>
  drule_all topcopy_val_footprint >> disch_then (qspec_then `v` assume_tac) >>
  gvs[type_memory_size_slots] >>
  rpt strip_tac >>
  `w2n (w + n2w i * 32w) = w2n w + 32*i` by
    (irule storage_copy_word_address >> qexists_tac `32 * type_slot_size tv` >>
     simp[] >> decide_tac) >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED
