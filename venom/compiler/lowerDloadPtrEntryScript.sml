Theory lowerDloadPtrEntry
Ancestors
  lowerDloadPtrRel lowerDloadDefs unitMemInv contextRawReachable
  contextCodegenRel venomExecProofs venomExecSemantics venomState
  finite_map list words

Theorem dload_reachable_frontier_bound:
  mem_inv dload_headroom_ok C vs /\ raw_reachable vs C fn inst s ==>
  s.vs_alloca_next < dimword (:256)
Proof
  simp[mem_inv_raw_reachable] >> rpt strip_tac >>
  first_x_assum drule >> simp[dload_headroom_ok_def] >> decide_tac
QED

Theorem dload_enters_block_allocations:
  enters_block fn s t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rw[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* The arbitrary run state need not fit a word unless an active entry exists.
   This is exactly where the headroom package makes its bound available. *)
Theorem dload_active_entry_frontier_bound:
  mem_inv dload_headroom_ok C vs /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  vs.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `raw_reachable vs C fn inst s` by
    (irule raw_reachable_entry >> metis_tac[]) >>
  drule_all dload_reachable_frontier_bound >>
  drule_all dload_enters_block_allocations >> simp[]
QED
