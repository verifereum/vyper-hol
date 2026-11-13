(* Attribute selection on the actual enriched base execution. *)
Theory bodyIntCallPostProvenanceAttributeSelector
Ancestors
  bodyIntCallPostProvenanceSelectors
  exprSimAttribute exprSimWordArgs bodyIntCallProducerInterface
  loweringPosts context exprSimDefs exprSimCopy loweringStateRelDefs
  exprSimVVFrame exprOperandVar emitHelper emitHelperProps compileEnv
  venomState venomInst finite_map freshWrites ASCIInumbers
  bodyPtrAttributeSource

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
  drule val_footprint_le >> simp[val_footprint_def] >> decide_tac
QED
