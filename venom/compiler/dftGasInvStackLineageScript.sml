Theory dftGasInvStackLineage
Ancestors
  dftDefs list rich_list arithmetic

Definition inv_line_children_def:
  inv_line_children bi order eda om p =
    sort_children bi order eda om p (inst_all_deps bi order eda p)
End

Definition inv_line_emit_def:
  inv_line_emit bi order eda om do_flip p =
    if do_flip /\ is_flippable p.inst_opcode /\
       inv_line_children bi order eda om p <> inst_all_deps bi order eda p
    then flip_operands p else p
End

Definition inv_line_flat_def:
  inv_line_flat emit [] roots = MAP DfsProcess roots /\
  inv_line_flat emit ((p,rs)::frames) roots =
    MAP DfsProcess rs ++ [DfsEmit (emit p)] ++ inv_line_flat emit frames roots
End

Definition inv_line_suffix_def:
  inv_line_suffix whole rs <=> ?front. whole = front ++ rs
End

Definition inv_line_link_def:
  inv_line_link whole p rs <=> ?front middle.
    whole = front ++ [p] ++ middle ++ rs
End

Definition inv_line_ok_def:
  inv_line_ok children entries [] roots = inv_line_suffix entries roots /\
  inv_line_ok children entries ((p,rs)::frames) roots =
    (inv_line_suffix (children p) rs /\
     (case frames of [] => inv_line_link entries p roots
      | (q,qs)::rest => inv_line_link (children q) p qs) /\
     inv_line_ok children entries frames roots)
End

Theorem inv_line_suffix_drop:
  inv_line_suffix whole (h::rs) ==> inv_line_suffix whole rs
Proof
  simp[inv_line_suffix_def] >> rpt strip_tac >>
  qexists_tac `front ++ [h]` >> simp[APPEND_ASSOC]
QED

Theorem inv_line_suffix_link:
  inv_line_suffix whole (h::rs) ==> inv_line_link whole h rs
Proof
  simp[inv_line_suffix_def, inv_line_link_def] >> rpt strip_tac >>
  qexistsl_tac [`front`, `[]`] >> simp[]
QED

Theorem inv_line_link_drop:
  inv_line_link whole p (h::rs) ==> inv_line_link whole p rs
Proof
  simp[inv_line_link_def] >> rpt strip_tac >>
  qexistsl_tac [`front`, `middle ++ [h]`] >> simp[APPEND_ASSOC]
QED

Theorem inv_line_ok_advance:
  inv_line_ok children entries ((p,h::rs)::frames) roots ==>
  inv_line_ok children entries ((p,rs)::frames) roots
Proof
  simp[inv_line_ok_def] >> metis_tac[inv_line_suffix_drop]
QED

Theorem inv_line_ok_push:
  inv_line_ok children entries ((p,h::rs)::frames) roots ==>
  inv_line_ok children entries ((h,children h)::(p,rs)::frames) roots
Proof
  strip_tac >> drule inv_line_ok_advance >> strip_tac >>
  simp[inv_line_ok_def, inv_line_suffix_def] >>
  gvs[inv_line_ok_def] >> metis_tac[inv_line_suffix_link]
QED

Theorem inv_line_ok_roots_drop:
  !frames. inv_line_ok children entries frames (h::roots) ==>
    inv_line_ok children entries frames roots
Proof
  Induct >> simp[inv_line_ok_def]
  >- metis_tac[inv_line_suffix_drop] >>
  qx_gen_tac `frame` >> Cases_on `frame` >> Cases_on `frames` >>
  simp[inv_line_ok_def] >> metis_tac[inv_line_link_drop]
QED

Theorem inv_line_root_push:
  inv_line_suffix entries (h::roots) ==>
  inv_line_ok children entries [(h,children h)] roots
Proof
  strip_tac >> simp[inv_line_ok_def, inv_line_suffix_def] >>
  metis_tac[inv_line_suffix_drop, inv_line_suffix_link, inv_line_suffix_def]
QED

Theorem inv_line_process_stack:
  st.ds_stack = DfsProcess h :: rest ==>
  (dfs_step bi order eda om do_flip st).ds_stack =
    if MEM h.inst_id st.ds_visited \/ is_pseudo h.inst_opcode
    then rest
    else MAP DfsProcess (inv_line_children bi order eda om h) ++
      [DfsEmit (inv_line_emit bi order eda om do_flip h)] ++ rest
Proof
  strip_tac >> simp[dfs_step_def, inv_line_children_def, inv_line_emit_def] >>
  Cases_on `MEM h.inst_id st.ds_visited` >> simp[] >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[]
QED

Definition inv_line_rep_def:
  inv_line_rep children emit entries st <=>
    ?frames roots. st.ds_stack = inv_line_flat emit frames roots /\
      inv_line_ok children entries frames roots
End

Theorem inv_line_rep_step:
  inv_line_rep (inv_line_children bi order eda om)
    (inv_line_emit bi order eda om do_flip) entries st ==>
  inv_line_rep (inv_line_children bi order eda om)
    (inv_line_emit bi order eda om do_flip) entries
    (dfs_step bi order eda om do_flip st)
Proof
  simp[inv_line_rep_def] >> rpt strip_tac >>
  Cases_on `frames`
  >- (Cases_on `roots`
      >- (qexistsl_tac [`[]`, `[]`] >> gvs[inv_line_flat_def, dfs_step_def]) >>
      rename1 `h::rs` >>
      `st.ds_stack = DfsProcess h :: MAP DfsProcess rs` by
        gvs[inv_line_flat_def] >>
      drule inv_line_process_stack >> strip_tac >>
      Cases_on `MEM h.inst_id st.ds_visited \/ is_pseudo h.inst_opcode`
      >- (qexistsl_tac [`[]`, `rs`] >>
          gvs[inv_line_flat_def, inv_line_ok_def] >>
          metis_tac[inv_line_suffix_drop]) >>
      qexistsl_tac [`[(h,inv_line_children bi order eda om h)]`, `rs`] >>
      simp[inv_line_flat_def] >> irule inv_line_root_push >>
      gvs[inv_line_ok_def]) >>
  rename1 `frame::outer` >> Cases_on `frame` >>
  rename1 `(p,pending)::outer` >> Cases_on `pending`
  >- (qexistsl_tac [`outer`, `roots`] >>
      gvs[inv_line_flat_def, dfs_step_def, inv_line_ok_def]) >>
  rename1 `(p,h::rs)::outer` >>
  `st.ds_stack = DfsProcess h ::
      inv_line_flat (inv_line_emit bi order eda om do_flip) ((p,rs)::outer) roots` by
    gvs[inv_line_flat_def] >>
  drule inv_line_process_stack >> strip_tac >>
  Cases_on `MEM h.inst_id st.ds_visited \/ is_pseudo h.inst_opcode`
  >- (qexistsl_tac [`(p,rs)::outer`, `roots`] >> simp[] >>
      metis_tac[inv_line_ok_advance]) >>
  qexistsl_tac [`(h,inv_line_children bi order eda om h)::(p,rs)::outer`, `roots`] >>
  simp[inv_line_flat_def] >> metis_tac[inv_line_ok_push]
QED

Definition inv_line_state_def:
  inv_line_state bi order eda om do_flip entries n =
    FUNPOW (dfs_step bi order eda om do_flip) n
      <|ds_stack := MAP DfsProcess entries;
        ds_output := []; ds_visited := []|>
End

Theorem inv_line_initialized:
  !n. inv_line_rep (inv_line_children bi order eda om)
    (inv_line_emit bi order eda om do_flip) entries
    (inv_line_state bi order eda om do_flip entries n)
Proof
  Induct
  >- (simp[inv_line_state_def, inv_line_rep_def] >>
      qexistsl_tac [`[]`, `entries`] >>
      simp[inv_line_flat_def, inv_line_ok_def, inv_line_suffix_def]) >>
  simp[inv_line_state_def, FUNPOW_SUC] >>
  irule inv_line_rep_step >> gvs[inv_line_state_def]
QED

Theorem inv_line_flat_emit_head:
  inv_line_flat emit frames roots = DfsEmit c :: rest ==>
  ?p outer. frames = (p,[])::outer /\ emit p = c /\
    rest = inv_line_flat emit outer roots
Proof
  Cases_on `frames`
  >- (Cases_on `roots` >> simp[inv_line_flat_def]) >>
  rename1 `frame::outer` >> Cases_on `frame` >>
  rename1 `(p,pending)::outer` >> Cases_on `pending` >>
  simp[inv_line_flat_def] >> metis_tac[]
QED

Theorem inv_line_initialized_emit:
  (inv_line_state bi order eda om do_flip entries n).ds_stack = DfsEmit c :: rest ==>
  ?p outer roots.
    inv_line_emit bi order eda om do_flip p = c /\
    rest = inv_line_flat (inv_line_emit bi order eda om do_flip) outer roots /\
    inv_line_suffix (inv_line_children bi order eda om p) [] /\
    (case outer of [] => inv_line_link entries p roots
     | (q,qs)::more => inv_line_link (inv_line_children bi order eda om q) p qs) /\
    inv_line_ok (inv_line_children bi order eda om) entries outer roots
Proof
  strip_tac >> mp_tac inv_line_initialized >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[inv_line_rep_def] >> rpt strip_tac >>
  qpat_x_assum `DfsEmit _ :: _ = _` (assume_tac o SYM) >>
  drule inv_line_flat_emit_head >> strip_tac >>
  gvs[inv_line_ok_def] >> metis_tac[]
QED
