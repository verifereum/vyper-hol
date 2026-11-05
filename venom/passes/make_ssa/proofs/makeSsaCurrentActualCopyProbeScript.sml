Theory makeSsaCurrentActualCopyProbe
Ancestors makeSsaCurrentDefs makeSsaCurrentCollapsedOrigin makeSsaCurrentCleanupRuntime
  makeSsaCurrentSimDefs venomExecSemantics venomState finite_map

(* Local incoming-source branch.  No old PHI output or reinsertion premise
   is used: the selected nonself input itself supplies the value.  This
   does not assert that every compiler copy has this selected input. *)
Theorem current_collapsed_nonself_selected_ready:
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] /\
  st.vs_prev_bb = SOME p /\
  resolve_phi p i.inst_operands = SOME (Var y) /\
  eval_one_phi st i = SOME (x,value) ==>
  step_inst_base (simplify_current_phi i) st = OK (update_var x value st)
Proof
  strip_tac >>
  `lookup_var y st = SOME value` by
    gvs[eval_one_phi_def, eval_operand_def, AllCaseEqs()] >>
  `(simplify_current_phi i).inst_outputs = [x]` by
    (gvs[simplify_current_phi_def, simplify_current_phi_raw_def,
      keep_current_phi_vars_def, current_phi_output_def] >>
     rpt CASE_TAC >> gvs[]) >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` mp_tac) >> simp[]
QED

(* An inserted merge can select its own name on an edge.  A successful
   pre-cleanup PHI evaluation then does NOT certify the copy's read.
   This bounded fixture is not a certificate or a task counterexample. *)
Definition current_copy_probe_phi_def:
  current_copy_probe_phi = current_probe_inst 0 PHI
    [Label "E"; Var "y"; Label "B"; Var "x"] ["x"]
End

Theorem current_copy_probe_nonself:
  (simplify_current_phi current_copy_probe_phi).inst_opcode = ASSIGN /\
  eval_one_phi
    ((update_var "y" 7w (init_venom_state "H")) with vs_prev_bb := SOME "E")
    current_copy_probe_phi = SOME ("x",7w) /\
  step_inst_base (simplify_current_phi current_copy_probe_phi)
    ((update_var "y" 7w (init_venom_state "H")) with vs_prev_bb := SOME "E") =
    OK (update_var "x" 7w
      ((update_var "y" 7w (init_venom_state "H")) with vs_prev_bb := SOME "E"))
Proof
  EVAL_TAC
QED

Theorem current_copy_probe_self_needs_other_source:
  eval_one_phi
    ((update_var "x" 7w (init_venom_state "H")) with vs_prev_bb := SOME "B")
    current_copy_probe_phi = SOME ("x",7w) /\
  step_inst_base (simplify_current_phi current_copy_probe_phi)
    ((update_var "x" 7w (init_venom_state "H")) with vs_prev_bb := SOME "B") =
    Error "undefined operand"
Proof
  EVAL_TAC
QED

(* CHECKPOINT INVENTORY (not additional theorem assertions).

   Exhaustive simplifier branches on a well-formed singleton-output PHI:
   - no nonself values: NOP, unconditionally executable;
   - nonempty constant nonself values: ASSIGN x := y, x <> y;
   - nonconstant values: unchanged PHI, handled in the retained batch.
   A failed keep_current_phi_vars guard also returns the original PHI,
   not a copy. current_phi_slots_classify is the checked boundary.

   Actual origins after current_cleanup_if_copy_inverse:
   1. An original source PHI. Under the task premises this stays PHI:
      current_certificate_retained_read_replay gives simplify i = i.
      Source coverage supplies a selected operand; original PHIs therefore
      cannot account for a member of the non-PHI cleanup segment.
   2. An inserted PHI for an old PHI output in this same block.
      current_certificate_reinserted_next_ready supplies a retained producer
      r < batch <= c. current_phi_batch_selected_value gives SOME postbatch;
      current_cleanup_segment_next_ready uses output distinctness to protect
      that value through earlier copies.
   3. Any other inserted PHI. current_certificate_collapsed_origin identifies
      a nondefault token t, distinct from this inserted token, named y.
      current_certificate_collapsed_predecessor_tokens gives the exhaustive
      selected-token alternatives: this inserted token, t, or CurrentDefault v
      (the last implies v = x or v = y). This is static provenance only.
      It supplies neither runtime realization of t nor producer ordering.

   For case 3 with selected name y, current_actual_insertion_input_defined
   gives source lookup v = SOME value when v is not a source leading-PHI
   output. To use it for this copy one still needs demanded agreement for
   the read y. current_collapsed_nonself_selected_ready checks the local
   execution branch once that value is present, without any reinsertion
   hypothesis. The self-selected fixture above shows why success of the
   uncleaned PHI alone does not prove readiness of a copy reading y.
   These fixtures are local branches, NOT certified compiler instances.

   Precise residual interfaces, to be discharged under the certificate,
   task hypotheses and source transition premises of
   current_graph_actual_phi_batch_transfer (not assumed as new invariants):

   A. For every ASSIGN at c = batch+k in the actual cleanup segment, with
      outputs [n] and operands [Var y], establish
        ?v. current_actual_inserted fn v h /\
            current_token_name H (CurrentInserted v h) = SOME n /\
            (?value. lookup_var v source_post = SOME value).
      Here eval_phis incoming hb.bb_instructions = OK source_post.
      Split old leading-PHI output v versus no such output. The former is
      defined by the successful source parallel batch; the latter by
      current_actual_insertion_input_defined plus preservation of variables
      not written by that batch. This avoids assuming any target copy runs.

   B. Possible shorter route than a producer-order classification:
      current_graph_demand_copy_seed already seeds (Var v,Var y) at the
      current copy cut from current_static_owner, which follows directly
      from the inserted-token half of A. Actual batch transfer establishes
      demanded agreement after the batches. Successful copy transfer
      advances it through ONLY the already executed TAKE k prefix.
      Thus A and current-cut demanded agreement directly give
        ?value. lookup_var y before_copy = SOME value,
      including the self-selected case. No target future success, incoming
      y nonclobber or earlier-copy producer ordering is needed for readiness
      via this route. The graph-edge alignment of the canonical cleanup
      segment still needs to be established. This is a proposed interface
      simplification, NOT a proved all-copy theorem.

   If instead using the direct producer route for case 3, the missing
   exhaustive statement must supply one of: incoming SOME y preserved by
   batch/prior copies; a retained output r < batch; or an earlier copy
   output at j < k. The strict inequality is essential and is not implied
   by collapsed_origin. No existing lemma found certifies this trichotomy.
   Output-distinctness only protects a value AFTER a producer exists.
*)
