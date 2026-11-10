Theory loadElimCaptureInvariant
Ancestors
  loadElimDefs loadElimKeyRead loadElimOccurrence list rich_list

(* Post-PHI/body-phase invariant only.  Actions carry no key field, so each
   validated computation witness indexes its own read obligation.  This is
   separate from padded equivalence and from target instruction indices. *)
Definition le_latest_captures_def:
  le_latest_captures m ctx cfg result actions h t <=>
    !pa key lbl inst pre bb u p suffix.
      MEM pa actions /\
      compute_phi_action m cfg result key lbl inst = SOME pa /\
      h = pre ++ PhiOcc bb u p :: suffix /\
      bb.bb_label = pa.pa_join_lbl /\
      (!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl) ==>
      ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
          lookup_var pa.pa_phi_out t = SOME w
End

Theorem le_latest_captures_empty[simp]:
  le_latest_captures m ctx cfg result actions [] t
Proof
  simp[le_latest_captures_def]
QED

Theorem le_latest_captures_lookup_transport:
  le_latest_captures m ctx cfg result actions h t /\
  (!pa. MEM pa actions ==>
    lookup_var pa.pa_phi_out t' = lookup_var pa.pa_phi_out t) ==>
  le_latest_captures m ctx cfg result actions h t'
Proof
  simp[le_latest_captures_def] >> metis_tac[]
QED
