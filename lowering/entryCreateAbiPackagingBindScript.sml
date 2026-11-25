(* The argument-list witness and the native hit are split independently.
   Only a normal list exit enters the source packaging continuation. *)
Theory entryCreateAbiPackagingBind
Ancestors
  entryCreateNativeFirstExit entryCreateRegionLift entryCreateIntervalLayout
  entryCreatePendingScope entryCreateScopedBind entryCreateStmtCases
  bodyFullExtCallPosList exprSimAbiEncodeRuntimeInputs stmtSimProps haltExitProj
  entryCreateCompletedCut entryCreateFocusSpec entryCreatePathScope entryCreateBodyCut
  createSizeCutRegion createSizeCutCode createSizePrefixReplay abiEncoderProps
  gasExemptCert vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Definition abi_encode_packaging_action_def:
  abi_encode_packaging_action cx ensure mid target args = \vs es.
    ((case evaluate_type_builtin cx (AbiEncode ensure mid) target
            (MAP expr_type args) vs of
        INL v => INL (Value v)
      | INR err => INR (Error err)),es)
End

Triviality abi_packaging_source:
  1 <= LENGTH args ==>
  eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) =
    vyperState$bind (eval_exprs cx args) (abi_encode_packaging_action cx ensure mid target args)
Proof
  simp[eval_expr_abi_encode_action,abi_encode_packaging_action_def]
QED

Triviality abi_packaging_frame:
  storage_trace_frame (abi_encode_packaging_action cx ensure mid target args vs)
Proof
  simp[storage_trace_frame_def,abi_encode_packaging_action_def]
QED

(* The positional post is inherited on normal exits; exception exits have
   the same obligation at the list and expression result types. *)
Triviality abi_packaging_list_posts:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa st
    (eval_exprs cx args) (es,s,G,tn) Q (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa st
    (eval_exprs cx args) (es,s,G,tn)
    (\H res ee G1 tn1 t. Q H res ee G1 tn1 t /\ ee.gas_obs = [])
    (\H res ee gt r. ?exc. res = INR exc /\
       create_operand_exit_post ctx cx H (INR exc : eval_result + exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> fs[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def,
        halt_exit_INR_type] >> metis_tac[expr_exit_INR_type,halt_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Triviality abi_packaging_suffix_visit:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} st sb /\ fn_has_code st sb func /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb) /\
  create_interior_visit st sb E ctx func (p,d,k) t (back,hit,after) ==>
  ?key i u. hit = (key,func,i,u) /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2
Proof
  strip_tac >>
  `create_cut_region st sb t` by
    (drule_all create_cut_region_rules >> strip_tac >>
     fs[create_interior_visit_def,create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region st sb u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >> metis_tac[]
QED

Triviality abi_packaging_cut:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sa st /\ fn_has_code sa st func /\
  create_cut_code {} st sb /\ fn_has_code st sb func /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb) /\
  create_operand_cut sa st E ctx func tops cx st0 (eval_exprs cx args) (es,s) ==>
  create_operand_cut sa sb E ctx func tops cx st0
    (vyperState$bind (eval_exprs cx args) (abi_encode_packaging_action cx ensure mid target args)) (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> simp[abi_packaging_frame] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_all abi_packaging_suffix_visit >> strip_tac >> gvs[] >>
  irule create_cut_noncreate_visit >> simp[]
QED

Triviality abi_packaging_step_widen:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E ctx f s ms t ==>
  create_prefix_step a b E ctx f s ms t
Proof
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Triviality abi_packaging_full_join:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E ctx f s left t /\
  create_operand_full_scope m b E ctx f t right r ==>
  create_operand_full_scope a b E ctx f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono,abi_packaging_step_widen,
    create_expr_prefix_append,APPEND_ASSOC]
QED

Triviality abi_packaging_focus_join:
  a.cs_next_id <= m.cs_next_id /\
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_operand_at m t /\
  create_expr_prefix a b E ctx f s left t /\
  create_operand_focus_scope m b E ctx f t right ==>
  create_operand_focus_scope a b E ctx f s (left ++ right)
Proof
  strip_tac >> irule create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule create_operand_focus_scope_lift >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >> simp[] >>
  `create_cut_region m b t` by
    (drule_all create_cut_region_rules >> fs[create_operand_at_def]) >>
  metis_tac[abi_packaging_step_widen]
QED

Theorem abi_encode_scoped_bind_from_list_suffix:
  1 <= LENGTH args /\ body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_layout sa sb /\ create_operand_at sa s /\
  create_cut_code {} sa st /\ fn_has_code sa st func /\
  create_cut_code {} st sb /\ fn_has_code st sb func /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code st sb) /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa st
    (eval_exprs cx args) (es,s,G,tn)
    (extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s G tn)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa st E ctx func tops cx st0 (eval_exprs cx args) (es,s) /\
  (!marks vs ee G1 tn1 t.
     (!tail. eval_exprs cx args
         (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (INL vs,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
     create_operand_at st t /\ create_operand_full_scope sa st E ctx func s marks (OK t) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s G tn
         H (INL vs : value list + exception) ee G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
     scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 st sb
       (abi_encode_packaging_action cx ensure mid target args vs) (ee,t,G1,tn1)
       Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    (eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args)) (es,s,G,tn)
    Q (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb E ctx func tops cx st0
    (eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args)) (es,s)
Proof
  strip_tac >> simp[abi_packaging_source] >> reverse conj_tac
  >- (irule abi_packaging_cut >> first_assum (irule_at Any) >> metis_tac[]) >>
  `cs_extends sa st /\ cs_extends st sb /\ sa.cs_next_id <= st.cs_next_id /\
   st.cs_next_id <= sb.cs_next_id` by fs[create_cut_code_def] >>
  `create_cut_region sa st s` by
    (irule (cj 1 create_cut_region_rules) >> fs[create_operand_at_def] >>
     qexists_tac `func` >> simp[]) >>
  `!u. create_cut_region sa st u /\ ~create_operand_at st u ==> ~create_operand_at sb u` by
    metis_tac[create_layout_left_stop] >>
  `!marks t. create_operand_full_scope sa st E ctx func s marks (OK t) ==>
     create_expr_prefix sa sb E ctx func s marks t /\ create_operand_at st t` by
    (simp[create_operand_full_scope_def,create_operand_at_def] >>
     metis_tac[create_left_prefix_lift_at,create_operand_at_def]) >>
  drule abi_packaging_list_posts >> strip_tac >>
  irule scoped_operand_bind_all_mixed >> first_assum (irule_at Any) >>
  simp[abi_packaging_frame,cj 6 evaluate_storage_trace_frame] >>
  rpt conj_tac >> rpt strip_tac
  >~ [`gas_exempt_cert _ _ _ _ _ (left ++ right) _ _`]
  >- (simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_values >> simp[GSYM ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC)
  >~ [`create_operand_full_scope sa sb E ctx func s marks r`]
  >- (irule create_left_terminal_lift_at >> first_assum (irule_at Any) >> metis_tac[])
  >- (`valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid'.storage_trace` (drule_then strip_assume_tac)) >>
      `?vs. res = INL vs` by
        (qhdtm_assum `extcall_positional_post`
          (mp_tac o BETA_RULE o REWRITE_RULE [extcall_positional_post_def]) >>
         strip_tac >> goal_assum drule) >>
      qexists_tac `vs` >> qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
      conj_tac >- simp[] >>
      qpat_assum `!marks vs ee G1 tn1 t. _` irule >> simp[] >>
      qexists_tac `marks` >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
        (qspec_then `H` mp_tac) >> simp[]) >>
  metis_tac[create_left_focus_lift_at,abi_packaging_focus_join,abi_packaging_full_join]
QED
