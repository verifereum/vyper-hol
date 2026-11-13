(* The memory words a top-level copy reads: a non-bytestring value
   occupies its full declared memory footprint (topcopy_val_footprint).
   Storage-copy semantics and compiler boundaries are shared with S1. *)
Theory bodyMemAssignTopCopySem
Ancestors
  stmtSimAssignStorageCopy exprSimHash exprSimHashBoundary exprSimProps loweringPosts
  compileEnv loweringStateRelDefs vyperValue vyperTyping valueEncodingProps
  words arithmetic

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
