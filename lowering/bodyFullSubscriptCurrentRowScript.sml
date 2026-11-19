(* A current-path read in every memory allowed by the endpoint ghost. *)
Theory bodyFullSubscriptCurrentRow
Ancestors
  bodyPtrDefs targetSubscriptMemory

Theorem subscript_current_row_robust_path:
  lookup_scopes id fin.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
  lookup_var q u = SOME B /\
  ghost_inv_at D lo d ce cx fin Gi tni u /\
  well_formed_type_value entry.type /\
  value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  w2n a = w2n B + k ==>
  !m. mem_agree_outside tni.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n a) m
Proof
  rpt strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
  `val_in_memory entry.type entry.value (w2n B) m` by
    (first_x_assum drule_all >> metis_tac[]) >>
  drule_all mem_path_offset_current_value >> simp[]
QED
