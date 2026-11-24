(* An internal-call cut follows the selected native INVOKE, including the
   unfinished child trace when the selected visit is inside that activation. *)
Theory entryCreateInternalFocus
Ancestors
  entryCreateInvokeCut entryCreateFocusSpec entryCreatePendingScope
  entryCreateNativeResume venomExecProofs contextCodegenRel fragGasOriginPtr fragGasMode
  list pair venomRunBounded

Theorem create_cut_invoke_entered_trace:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  trace_step p d (SUC k) ctx caller inst s =
    create_trace_from ((d,inst.inst_id)::p) (SUC d) k ctx callee entered
Proof
  strip_tac >> drule_all create_cut_invoke_entry >>
  disch_then (qspecl_then [`p`,`SUC k`,`d`] strip_assume_tac) >>
  qpat_x_assum `enters_block _ _ _` (strip_assume_tac o REWRITE_RULE[enters_block_def]) >>
  `s_phi.vs_current_bb = setup.vs_current_bb` by
    (drule eval_phis_preserves_current_bb >> simp[]) >>
  drule_all create_trace_from_enter >> simp[]
QED

Theorem create_cut_invoke_pending_entered:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  trace_step p d fuel ctx caller inst s = inside ++ hit::suffix ==>
  ?k. fuel = SUC k /\
      create_trace_from ((d,inst.inst_id)::p) (SUC d) k ctx callee entered =
        inside ++ hit::suffix
Proof
  Cases_on `fuel` >> strip_tac
  >- (drule_all create_cut_invoke_entry >>
      disch_then (qspecl_then [`p`,`0`,`d`] strip_assume_tac) >> fs[]) >>
  drule_all create_cut_invoke_entered_trace >> metis_tac[]
QED

(* Rebase the native child trace through the actual lock landing. If the
   hit is in the prologue, disjointness suffices and the body IH is unused. *)
Theorem create_cut_invoke_pending_body:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  trace_step p d (SUC k) ctx caller inst s = inside ++ hit::suffix /\
  create_trace_from ((d,inst.inst_id)::p) (SUC d) k ctx callee entered =
    prologue ++ create_trace_from ((d,inst.inst_id)::p) d' k' ctx callee start /\
  EVERY (\(_,_,i,t). inst_create_size_ok i t) prologue /\
  create_cut_marks explicit prologue = [] /\
  gas_marked_path F ctx callee entered 0 (OK start) /\
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),locked) /\
  (!before after.
     create_trace_from ((d,inst.inst_id)::p) d' k' ctx callee start =
       before ++ hit::after ==>
     create_body_cut explicit tops (cx with stk updated_by CONS (NONE,name)) st0
       (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
       (locked,start) (before,hit)) /\
  (case hit of (_,_,i,t) => ~inst_create_size_ok i t) ==>
  ?before after. inside = prologue ++ before /\
    create_trace_from ((d,inst.inst_id)::p) d' k' ctx callee start = before ++ hit::after /\
    create_body_cut explicit tops (cx with stk updated_by CONS (NONE,name)) st0
      (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
      (locked,start) (before,hit)
Proof
  strip_tac >> drule_all create_cut_invoke_entered_trace >> strip_tac >> fs[] >>
  `inside ++ [hit] ++ suffix = prologue ++
       create_trace_from ((d,inst.inst_id)::p) d' k' ctx callee start` by fs[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE[APPEND_EQ_APPEND_MID])
  >- (PairCases_on `hit` >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

(* A pending child focus is not an edge on the caller spine. The marks up
   to the INVOKE are confined separately from the prefix of child marks. *)
Theorem create_cut_internal_pending_scope:
  create_expr_prefix sa sb explicit ctx caller s marks u /\
  create_operand_fetch sa sb caller u inst /\
  gas_invoke_entry (ctx,caller) u callee entered /\
  gas_origin_ptr_focus (D,lo,explicit,ctx,callee,PG)
    (entered,G,tn) child focus ==>
  create_operand_focus_scope sa sb explicit ctx caller s (marks ++ child)
Proof
  PairCases_on `focus` >>
  simp[create_operand_fetch_def, create_operand_at_def] >>
  metis_tac[create_operand_focus_scope_pending]
QED
