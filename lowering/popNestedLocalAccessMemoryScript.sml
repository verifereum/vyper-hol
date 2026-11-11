(* Local-root access frame for a nested target's index.  The complete scope
   entry is preserved, including its type, value and popped history. *)
Theory popNestedLocalAccessMemory
Ancestors
  popNestedLocalPoppedOverlap targetOverlapAccess
  vyperLocalAccessFrame vyperStorageAccessFrame

Theorem pop_nested_local_index_entry_frame:
  target_root bt = NameTarget id /\
  target_through_dynarray cenv bt /\
  ~target_subscript_overlap cenv bt e /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) ==>
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes
Proof
  strip_tac >>
  drule_all local_target_overlap_excludes_write >> strip_tac >>
  `~MEM (WriteAcc (LocalRef id)) (accesses_expr e)` by
    metis_tac[direct_expr_accesses] >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  imp_res_tac vyperStateTheory.read_result_state >> gvs[] >>
  metis_tac[eval_expr_unwritten_local]
QED
