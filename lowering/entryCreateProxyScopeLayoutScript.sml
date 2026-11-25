(* Scope of the actual proxy compiler stages, independent of source outcomes. *)
Theory entryCreateProxyScopeLayout
Ancestors
  entryCreateIntervalLayout entryCreateRegionLift entryCreatePendingScope
  createSizeOperandCode createSizeFixedPreparation createSizeCreateLayoutCode
  createSizeResultCheckCode createSizeCutRegion createSizeCutCode createSizePrefixReplay
  entryCreateFocusSpec entryCreateCompletedCut entryCreatePathScope
  bodySim builtinCreate exprLowering compileEnv fragExec abiEncoderProps
  list pair arithmetic

Theorem proxy_suffix_step_widen[local]:
  x.cs_next_id <= m.cs_next_id /\ create_prefix_step m z E ctx f u marks v ==>
  create_prefix_step x z E ctx f u marks v
Proof
  simp[create_prefix_step_def, frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem proxy_suffix_full_widen[local]:
  x.cs_next_id <= m.cs_next_id /\
  create_expr_prefix x z E ctx f s left u /\
  create_operand_full_scope m z E ctx f u right r ==>
  create_operand_full_scope x z E ctx f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono, proxy_suffix_step_widen,
            create_expr_prefix_append, APPEND_ASSOC]
QED

Theorem proxy_suffix_focus_widen[local]:
  x.cs_next_id <= m.cs_next_id /\ body_inv tops ctx ce cx /\
  MEM f ctx.ctx_functions /\ create_cut_code {} m z /\ fn_has_code m z f /\
  create_cut_region m z u /\ create_expr_prefix x z E ctx f s left u /\
  create_operand_focus_scope m z E ctx f u right ==>
  create_operand_focus_scope x z E ctx f s (left ++ right)
Proof
  strip_tac >> irule create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule create_operand_focus_scope_lift >>
  rpt (goal_assum (drule_at Any)) >>
  metis_tac[proxy_suffix_step_widen]
QED

Theorem proxy_split_scopes[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} x m /\ create_cut_code {} m z /\
  fn_has_code x m f /\ fn_has_code m z f /\ create_layout x z /\
  create_operand_at x s ==>
  (!marks. create_operand_focus_scope x m E ctx f s marks ==>
           create_operand_focus_scope x z E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope x m E ctx f s marks r ==>
             create_operand_full_scope x z E ctx f s marks r) /\
  (!left u right. create_operand_full_scope x m E ctx f s left (OK u) /\
                  create_operand_focus_scope m z E ctx f u right ==>
                  create_operand_focus_scope x z E ctx f s (left ++ right)) /\
  (!left u right r. create_operand_full_scope x m E ctx f s left (OK u) /\
                    create_operand_full_scope m z E ctx f u right r ==>
                    create_operand_full_scope x z E ctx f s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends x m /\ cs_extends m z /\ x.cs_next_id <= m.cs_next_id /\
   m.cs_next_id <= z.cs_next_id` by fs[create_cut_code_def] >>
  `create_cut_region x m s` by metis_tac[create_cut_region_rules,create_operand_at_def] >>
  `!u. create_cut_region x m u /\ ~create_operand_at m u ==> ~create_operand_at z u`
    by metis_tac[create_layout_left_stop] >>
  `!left u. create_operand_full_scope x m E ctx f s left (OK u) ==>
           create_expr_prefix x z E ctx f s left u /\ create_cut_region m z u` by
    (simp[create_operand_full_scope_def] >> rpt strip_tac
     >- metis_tac[create_left_prefix_lift_at] >>
     metis_tac[create_cut_region_rules]) >>
  rpt conj_tac
  >- metis_tac[create_left_focus_lift_at]
  >- metis_tac[create_left_terminal_lift_at]
  >- metis_tac[proxy_suffix_focus_widen] >>
  metis_tac[proxy_suffix_full_widen]
QED

Theorem proxy_salt_closed_code[local]:
  compile_create_salt compile_expr ce salt c = (sop,sm) ==>
  create_cut_code {} c sm
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, comp_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr ce (expr_type x) x c` >>
  simp[] >> metis_tac[cj 2 create_operand_cut_code,SND]
QED

(* Select any of the four adjacent splits, including c = sm when salt is absent. *)
Theorem proxy_stage_scope_joins:
  lower_value compile_expr ce (expr_type target) target sa = (p,a) /\
  lower_value compile_expr ce (expr_type amount) amount a = (v,b) /\
  compile_create_proxy_buf p b = (buf,c) /\
  compile_create_salt compile_expr ce salt c = (sop,sm) /\
  compile_create_dispatch buf (Lit 54w) v sop rof sm = (out,sb) /\
  fn_has_code sa sb f /\ create_layout sa sb /\
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  ((x = sa /\ m = a) \/ (x = a /\ m = b) \/ (x = b /\ m = c) \/ (x = c /\ m = sm)) /\
  create_operand_at x s ==>
  create_cut_code {} x m /\ create_cut_code {} m sb /\
  fn_has_code x m f /\ fn_has_code m sb f /\ create_cut_region x m s /\
  (!marks. create_operand_focus_scope x m E ctx f s marks ==>
           create_operand_focus_scope x sb E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope x m E ctx f s marks r ==>
             create_operand_full_scope x sb E ctx f s marks r) /\
  (!left u right. create_operand_full_scope x m E ctx f s left (OK u) /\
                  create_operand_focus_scope m sb E ctx f u right ==>
                  create_operand_focus_scope x sb E ctx f s (left ++ right)) /\
  (!left u right r. create_operand_full_scope x m E ctx f s left (OK u) /\
                    create_operand_full_scope m sb E ctx f u right r ==>
                    create_operand_full_scope x sb E ctx f s (left ++ right) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_cut_code {} sa a /\ create_cut_code {} a b` by
    metis_tac[cj 2 create_operand_cut_code,SND] >>
  `create_cut_code {} b c` by metis_tac[cj 4 create_fixed_preparation_intervals,SND] >>
  `create_cut_code {} c sm` by metis_tac[proxy_salt_closed_code] >>
  `create_cut_code {} sm sb` by
    (mp_tac create_dispatch_cut >> simp[create_result_check_cut_code] >>
     metis_tac[SND]) >>
  `create_cut_code {} c sb /\ create_cut_code {} b sb /\ create_cut_code {} a sb` by
    metis_tac[create_cut_code_join] >>
  `cs_extends sa x /\ create_cut_code {} x m /\ create_cut_code {} m sb` by
    (fs[create_cut_code_def,cs_extends_refl] >> metis_tac[cs_extends_trans]) >>
  `cs_extends x m /\ cs_extends m sb` by fs[create_cut_code_def] >>
  `cs_extends x sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code x m f /\ fn_has_code m sb f` by metis_tac[fn_has_code_split] >>
  `create_layout x sb` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  drule_all proxy_split_scopes >> simp[] >>
  metis_tac[create_cut_region_rules,create_operand_at_def]
QED
