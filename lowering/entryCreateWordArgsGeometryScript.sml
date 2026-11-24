Theory entryCreateWordArgsGeometry
Ancestors
  entryCreateIntervalLayout entryCreateRegionLift entryCreatePendingScope
  entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec
  createSizeCutRegion createSizePrefixReplay compileEnv abiEncoderProps
  fragExec bodySim arithmetic list

(* The suffix keeps its stop; only its lower instruction-ID bound changes. *)
Theorem word_args_suffix_step_widen[local]:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E C f t ms u ==>
  create_prefix_step a b E C f t ms u
Proof
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem word_args_scope_join_full[local]:
  a.cs_next_id <= m.cs_next_id /\
  create_expr_prefix a b E C f s left t /\
  create_operand_full_scope m b E C f t right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono,word_args_suffix_step_widen,
            create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem word_args_scope_join_focus[local]:
  a.cs_next_id <= m.cs_next_id /\ body_inv tops C ce cx /\
  MEM f C.ctx_functions /\ create_cut_code {} m b /\ fn_has_code m b f /\
  create_operand_at m t /\ create_expr_prefix a b E C f s left t /\
  create_operand_focus_scope m b E C f t right ==>
  create_operand_focus_scope a b E C f s (left ++ right)
Proof
  strip_tac >> irule create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule create_operand_focus_scope_lift >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >> simp[] >>
  `create_cut_region m b t` by
    (drule_all create_cut_region_rules >> fs[create_operand_at_def]) >>
  metis_tac[word_args_suffix_step_widen]
QED

Theorem create_word_args_scope_embeddings:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  cs_extends a m /\ cs_extends m b /\
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
  create_layout a b /\ create_operand_at a s /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    (rpt strip_tac >> drule_all create_layout_left_stop >> simp[]) >>
  `!left t. create_operand_full_scope a m E C f s left (OK t) ==>
            create_expr_prefix a b E C f s left t /\ create_operand_at m t` by
    (simp[create_operand_full_scope_def,create_operand_at_def] >>
     rpt strip_tac >> drule_all create_left_prefix_lift_at >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all create_left_focus_lift_at >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all create_left_terminal_lift_at >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[word_args_scope_join_focus]) >>
  rpt strip_tac >> metis_tac[word_args_scope_join_full]
QED
