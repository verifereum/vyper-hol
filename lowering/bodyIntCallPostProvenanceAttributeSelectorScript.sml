(* Attribute selection on the actual enriched base execution. *)
Theory bodyIntCallPostProvenanceAttributeSelector
Ancestors
  bodyIntCallPostProvenanceSelectors
  exprSimAttribute exprSimWordArgs bodyIntCallProducerInterface
  loweringPosts context exprSimDefs exprSimCopy loweringStateRelDefs
  exprSimVVFrame exprOperandVar emitHelper emitHelperProps compileEnv
  venomState venomInst finite_map freshWrites ASCIInumbers
  bodyPtrAttributeSource exprSimFieldLayout exprSimProps exprSimAttributeProps
  valueEncoding valueEncodingDefs vyperAST bodyIntCallArgType exprSimAttributeFields
  bodyPtrAttributeObservation gasSummary gasSummaryCompose gasContext gasOutcome
  fragGasMode fragGasPath gasExemptCert vyperState exprSimUnwrap fragExec

(* Only metadata is needed: memory may change provided ownership and the
   operand and local pointer registers are retained. *)
Theorem intcall_provenance_register_frame:
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ local_ptrs_reserved ce sm /\
  sm.cs_next_id <= sn.cs_next_id ==>
  intcall_vv_provenance ce cx ty sa sn es raw vv t
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     metis_tac[]) >>
  `!n p sz. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz) ==>
             lookup_var p t = lookup_var p s` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `vv` >>
  gvs[intcall_vv_provenance_def, vv_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
    disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >>~- ([`local_val_at ce cx n (w2n w - b) tvt v`],
    disj2_tac >> disj2_tac >> disj1_tac >>
    qexistsl_tac [`n`, `b`, `sz`] >> simp[])
  >> disj2_tac >> disj2_tac >> disj2_tac >>
  rename1 `lookup_var rootp s = SOME rootw` >>
  qexistsl_tac [`n`, `sz`, `entry`, `rootp`, `rootw`, `k`] >> simp[] >>
  metis_tac[]
QED

Theorem intcall_attr_add_path:
  compile_expr ce ty e sa = (vv,sm) /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  intcall_vv_provenance ce cx bt sa sm ee raw vv s ==>
  ?t w. gas_path ctx func s 0 (OK t) /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e es sa sn s0 ee raw vv t /\
    eval_operand (vv_operand vv) t = SOME w /\
    eval_operand dst t = SOME (w + n2w off) /\
    intcall_vv_provenance ce cx bt sa sn ee raw vv t
Proof
  rpt strip_tac >>
  `?w. eval_operand (vv_operand vv) s = SOME w` by
    (gvs[vv_post_def] >> Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[cj 1 compiler_compile_var] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   LENGTH sn.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
   sm.cs_next_id <= sn.cs_next_id` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!x. not_fresh_at sm x ==>
       lookup_var x (update_var (STRING #"%" (toString sm.cs_next_var))
                       (w + n2w off) s) = lookup_var x s` by
    (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand (vv_operand vv)
     (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s) =
     eval_operand (vv_operand vv) s` by
    (irule literal_operand_frame >> conj_tac
     >- (qexists_tac `sm` >> simp[]) >> simp[update_var_def]) >>
  qexistsl_tac [`update_var (STRING #"%" (toString sm.cs_next_var))
                  (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx`, `w`] >>
  simp[] >> conj_tac
  >- (drule emit_op_zero_path >> simp[is_terminator_def] >>
      disch_then irule >> simp[] >> gen_tac >>
      irule step_ADD >> simp[eval_operand_def]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, toString_11]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule intcall_provenance_register_frame >>
  goal_assum (drule_at Any) >> simp[update_var_def] >>
  qexists_tac `s` >> simp[] >>
  Cases_on `vv_operand vv` >> gvs[eval_operand_def, lookup_var_def, update_var_def]
QED

Theorem intcall_struct_field_layout[local]:
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP vals fld = SOME fv /\ ALOOKUP fs fld = SOME ftv /\
  val_wf ftv fv ==>
  sub_layout (StructTV fs) (StructV vals)
    (struct_field_offset fields fld) ftv fv /\
  struct_field_offset fields fld + val_footprint ftv fv <=
    val_footprint (StructTV fs) (StructV vals)
Proof
  strip_tac >>
  `struct_field_offset fields fld + type_memory_size ftv <=
   type_memory_size_fields fs` by
    (irule struct_field_offset_le >> metis_tac[]) >>
  conj_tac
  >- (simp[sub_layout_def, type_memory_size_def] >> rpt strip_tac >>
      irule fields_in_memory_field >> gvs[val_in_memory_def] >> metis_tac[]) >>
  drule val_footprint_le >> strip_tac >>
  CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss())
    [val_footprint_def, type_memory_size_def])) >> decide_tac
QED

Theorem intcall_attribute_dynamic_memory_provenance[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL raw,ee) /\
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  intcall_vv_provenance ce cx (expr_type obj) sa sb ee raw bvv t /\
  vv_loc bvv = LocMemory /\
  (!tv. evaluate_type (get_tenv cx) (expr_type obj) = SOME tv ==>
        ~dynarray_free tv) /\
  eval_operand dst t = SOME
    (w + n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld)) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  select_result cx (expr_type obj) raw (AttrSubscript fld) ee = (INL result,ee) ==>
  intcall_vv_provenance ce cx ann sa sb ee result
    (LocatedValue ann (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> drule_all attribute_typed_selection >> strip_tac >> gvs[] >>
  `post_value_type ce obj = StructT sid` by
    (drule attr_pre_base >> strip_tac >> gvs[] >>
     drule_all attr_post_value_type >> simp[]) >>
  drule_all attribute_memory_field_address >> strip_tac >>
  drule_all intcall_struct_field_layout >> strip_tac >>
  irule intcall_dynamic_memory_selection >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`StructT sid`, `bvv`, `vv_operand bvv`, `raw`] >>
  simp[attr_offset_def] >>
  Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def]
QED

Theorem intcall_attribute_selection_provenance[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es0 /\
  ~expr_has_effect (Attribute ann obj fld) /\
  eval_expr cx obj es0 = (INL raw,ee) /\
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  intcall_vv_provenance ce cx (expr_type obj) sa sb ee raw bvv t /\
  vv_post ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee result
    (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
  eval_operand dst t = SOME
    (w + n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld)) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  select_result cx (expr_type obj) raw (AttrSubscript fld) ee = (INL result,ee) ==>
  intcall_vv_provenance ce cx ann sa sb ee result
    (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >>
  `post_value_type ce (Attribute ann obj fld) = ann` by
    simp[bodyIntCallArgTypeTheory.effect_free_post_value_type, expr_type_def] >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (drule_all attribute_typed_selection >> strip_tac >> gvs[] >>
      Cases_on `dynarray_free (StructTV fs)`
      >- (`dynarray_free ftv` by
            (drule_all exprSimAttributeFieldsTheory.mem_field_offset_layout >> strip_tac >>
             simp[dynarray_free_def] >> rpt strip_tac >>
             qpat_x_assum `dynarray_free (StructTV fs)`
               (mp_tac o REWRITE_RULE [dynarray_free_def]) >>
             disch_then (qspec_then `AttrSubscript fld::path` mp_tac) >>
             simp[mem_path_offset_def, mem_step_offset_def] >> metis_tac[]) >>
          qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` kall_tac >>
          qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
          gvs[vv_post_def, intcall_vv_provenance_def, mk_ptr_def,
              vv_at_def, expr_type_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
      drule intcall_attribute_dynamic_memory_provenance >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[vv_post_def, intcall_vv_provenance_def, mk_ptr_def, vv_holds_def,
      immutable_holds_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem intcall_attribute_selected_post[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL raw,ee) /\
  vv_post ctx func ce cx obj es sa sb s0 ee raw bvv t /\
  eval_operand dst t = SOME
    (w + n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld)) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  select_result cx (expr_type obj) raw (AttrSubscript fld) ee = (INL result,ee) ==>
  vv_post ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee result
    (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >> drule_all attribute_typed_selection >> strip_tac >> gvs[] >>
  `post_value_type ce obj = expr_type obj` by
    (drule attr_pre_base >> strip_tac >> drule_all attr_post_value_type >> simp[]) >>
  drule select_result_memory_place >> strip_tac >>
  irule attr_vv_post >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `raw` >> simp[] >>
  rpt strip_tac >> gvs[] >> simp[vyperTypingTheory.value_has_type_def]
QED

Theorem intcall_attribute_summary[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  ~expr_has_effect (Attribute ann obj fld) /\
  compile_expr ce ty obj sa = (bvv,sm) /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv;
    Lit (n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld))] sm = (dst,sb) /\
  fn_has_code sm sb func /\
  gas_marked_exec F (ctx,func) (eval_expr cx obj) (es,s0) marks (INL raw) fe (OK t) /\
  vv_post ctx func ce cx obj es sa sm s0 (fe with gas_obs := []) raw bvv t /\
  intcall_vv_provenance ce cx (expr_type obj) sa sm (fe with gas_obs := []) raw bvv t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) marks (eval_expr cx (Attribute ann obj fld)) (es,s0)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee tv
        (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx ann sa sb ee tv
        (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u) R
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,fe with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  drule_all intcall_attr_add_path >> strip_tac >>
  rename1 `gas_path ctx func t 0 (OK u)` >>
  `expr_body_pre ce cx env (Attribute ann obj fld)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all attribute_typed_selection >> strip_tac >>
  `vv_post ctx func ce cx (Attribute ann obj fld) es sa sb s0
     (fe with gas_obs := []) tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u` by
    (irule intcall_attribute_selected_post >> metis_tac[]) >>
  `intcall_vv_provenance ce cx ann sa sb (fe with gas_obs := []) tv'
     (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u` by
    (irule intcall_attribute_selection_provenance >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `eval_expr cx (Attribute ann obj fld) =
     bind (eval_expr cx obj)
       (\r. select_result cx (expr_type obj) r (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >>
  gvs[intcall_vv_provenance_gas_obs] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INL tv'`,`fe`,`OK u`] >> simp[] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
    |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`fe`,`t`,`raw`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def,
       bodyPtrAttributeObservationTheory.select_attr_gas_update]
QED

Theorem intcall_attribute_exempt[local]:
  gas_exempt_cert memory tops p (ignore_bind (eval_expr cx obj) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (eval_expr cx (Attribute ann obj fld)) (return ()))
    start marks out endpoint
Proof
  strip_tac >>
  `eval_expr cx (Attribute ann obj fld) =
     bind (eval_expr cx obj)
       (\r. select_result cx (expr_type obj) r (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >> simp[] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `bind (eval_expr cx obj) sel` >>
  `ignore_bind (bind (eval_expr cx obj) sel) (return ()) =
   bind (eval_expr cx obj) (\r. ignore_bind (sel r) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx obj x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED

Theorem intcall_attribute_outcome:
  (!env ty es sa sb vv s0.
    expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
    compile_expr ce ty obj sa = (vv,sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx obj) (es,s0)
      (\res ee t. ?tv. res = INL tv /\
        vv_post ctx func ce cx obj es sa sb s0 ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        intcall_vv_provenance ce cx (expr_type obj) sa sb ee tv vv t)
      (\res ee r. expr_exit res r)) /\
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  ~expr_has_effect (Attribute ann obj fld) /\
  compile_expr ce ty (Attribute ann obj fld) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Attribute ann obj fld)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (Attribute ann obj fld)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx ann sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule attr_pre_base >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  `~expr_has_effect obj` by gvs[] >>
  `local_ptrs_reserved ce sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  first_x_assum drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
      >- (irule intcall_attribute_summary >> simp[] >>
          conj_tac >- metis_tac[] >>
          qexistsl_tac [`es_end`,`tv`,`sm`,`t`,`ty`] >> simp[]) >>
      Cases_on `res` >> gvs[] >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >> simp[] >>
      `eval_expr cx (Attribute ann obj fld) =
         bind (eval_expr cx obj)
           (\v. select_result cx (expr_type obj) v (AttrSubscript fld))` by
        simp[FUN_EQ_THM, eval_expr_attribute] >>
      simp[] >> irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[intcall_attribute_exempt]
QED
