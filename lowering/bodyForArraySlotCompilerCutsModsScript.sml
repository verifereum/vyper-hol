(* Physical compiler cuts for the reached storage/transient Array branch. *)
Theory bodyForArraySlotCompilerCutsMods
Ancestors
  bodyFullForArrayRound bodyFullForFacts bodyAssignNameLinkedSetup
  exprBodyPreProps vyperTypeSystem vyperTypeEvalCaseProofs valueEncodingProps
  exprSafeOperandBuiltins exprLowering
  compileEnv context targetPlaceSim loweringPosts vyperTypeValues
  vyperTypeContract[qualified,ignore_grammar]
  stmtLowering copyExecution exprPtrUnwrapRuntimeFrame slotCopyExecution
  emitHelperProps loweringShapeRules exprLoweringProps vyperAST list arithmetic

Theorem slot_iterator_nonlabel[local]:
  compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
  vyperTypeContract$loop_iterator_place e = SOME tgt /\
  target_root tgt = TopLevelNameTarget nid ==>
  !lbl. vv_operand vv <> Label lbl
Proof
  Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def] >>
  simp[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
  rpt strip_tac >> gvs[target_root_def]
  >- (qpat_x_assum `_ = (vv,sbExpr)` mp_tac >> simp[AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[vv_operand_def,mk_ptr_def])
  >- (drule compile_subscript_not_label >> simp[]) >>
  drule compile_attribute_safe_operand >> simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem slot_cut_sizes[local]:
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  expr_sim_inv_mods mods c cx env es /\
  expr_type e = ArrayT sty bd /\ evaluate_type (get_tenv cx) fty = SOME tv ==>
  sty = fty /\ well_formed_type_value tv /\ 0 < type_slot_size tv /\
  type_memory_bytes c fty = 32 * type_slot_size tv
Proof
  strip_tac >> drule_then strip_assume_tac type_stmt_for_projection >>
  `sty = fty` by (fs[well_typed_iterator_def] >> gvs[]) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  `assignable_type (get_tenv cx) fty` by fs[] >>
  drule_all_then assume_tac assignable_type_slot_size_pos >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >>
  simp[type_memory_size_slots]
QED

Theorem slot_copy_physical_cut[local]:
  compile_iter_elem_copy c src (Var xd) stride (slot_loc tr) T fty sty
    saCopy = ((),sbCopy) /\ fn_has_code saCopy sbCopy func ==>
  compile_slot_to_memory src (Var xd) stride (slot_loc tr) saCopy =
    (slot_copy_body saCopy,sbCopy) /\
  lookup_block saCopy.cs_current_bb func.fn_blocks =
    SOME <|bb_label := saCopy.cs_current_bb;
           bb_instructions := saCopy.cs_current_insts ++ slot_copy_init_insts saCopy|> /\
  lookup_block (slot_copy_cond saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_cond saCopy;
           bb_instructions := slot_copy_cond_insts saCopy stride|> /\
  lookup_block (slot_copy_body saCopy) func.fn_blocks =
    SOME <|bb_label := slot_copy_body saCopy;
           bb_instructions := slot_copy_body_insts saCopy src (Var xd)
             (if tr then TLOAD else SLOAD)|>
Proof
  `compile_slot_to_memory src (Var xd) stride (slot_loc tr) saCopy =
    (slot_copy_body saCopy,
     slot_copy_final saCopy src (Var xd) stride (if tr then TLOAD else SLOAD))` by
    (Cases_on `tr` >> simp[slot_loc_def, compile_slot_to_memory_shape]) >>
  simp[compile_iter_elem_copy_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >> strip_tac >>
  qpat_x_assum `slot_copy_final _ _ _ _ _ = sbCopy` (SUBST_ALL_TAC o SYM) >>
  drule_then strip_assume_tac slot_copy_lookup >> simp[]
QED

Theorem slot_cut_address_ops[local]:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (off_op,sm) /\
  (let hdr = case bd of Fixed _ => 0 | Dynamic _ => 1 in
   if 0 < hdr then emit_op ADD [Lit (n2w hdr);off_op] sm = (sum_op,sn)
   else sum_op = off_op /\ sn = sm) /\
  emit_op ADD [base_op;sum_op] sn = (addr,saCopy) ==>
  ?ov sum ep. off_op = Var ov /\ sum_op = Var sum /\ addr = Var ep /\
    (case bd of Fixed _ => sn = sm /\ sum = ov
     | Dynamic _ => emit_op ADD [Lit 1w;Var ov] sm = (Var sum,sn)) /\
    not_fresh_at saCopy ep
Proof
  Cases_on `bd` >> simp[] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_assum `emit_op ADD [base_op;_] _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >>
  qpat_assum `emit_op ADD [Lit 1w;_] _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[]
QED

Theorem slot_cut_external[local]:
  (!x. op = Var x ==> not_fresh_at sc x) ==> slot_copy_external sc op
Proof
  Cases_on `op` >> simp[slot_copy_external_def] >>
  metis_tac[slot_copy_not_fresh_external,slot_copy_external_def]
QED

Theorem for_array_slot_compiler_cuts_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,cap,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  loc = slot_loc tr /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  expr_sim_inv_mods mods c cx env es /\ evaluate_type (get_tenv cx) fty = SOME tv /\
  vyperTypeContract$loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid ==>
  sty = fty /\ well_formed_type_value tv /\ 0 < type_slot_size tv /\
  32 * type_slot_size tv = cap /\ stride = type_slot_size tv /\
  fn_has_code sa saCopy func /\ local_ptrs_reserved c sa /\ local_ptrs_reserved c saCopy /\
  not_fresh_at sa idx /\ not_fresh_at saCopy xd /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at saCopy x) /\
  (!x. not_fresh_at saL x ==> not_fresh_at sa x /\ not_fresh_at saCopy x /\
       slot_copy_external saCopy (Var x)) /\
  (!x. vv_operand vv = Var x \/ len_op = Var x ==> not_fresh_at sa x) /\
  (!lbl. vv_operand vv <> Label lbl) /\
  slot_copy_external saCopy (Var idx) /\ slot_copy_external saCopy (vv_operand vv) /\
  slot_copy_external saCopy len_op /\
  ?ov sum ep. off_op = Var ov /\ sum_op = Var sum /\ addr = Var ep /\
    emit_op MUL [Var idx;Lit (n2w (type_slot_size tv))] sa = (Var ov,sm) /\
    (case bd of Fixed _ => sn = sm /\ sum = ov
     | Dynamic _ => emit_op ADD [Lit 1w;Var ov] sm = (Var sum,sn)) /\
    emit_op ADD [vv_operand vv;Var sum] sn = (Var ep,saCopy) /\
    slot_copy_external saCopy (Var ep) /\
    compile_slot_to_memory (Var ep) (Var xd) (type_slot_size tv) (slot_loc tr) saCopy =
      (slot_copy_body saCopy,sbCopy) /\
    lookup_block saCopy.cs_current_bb func.fn_blocks =
      SOME <|bb_label := saCopy.cs_current_bb;
             bb_instructions := saCopy.cs_current_insts ++ slot_copy_init_insts saCopy|> /\
    lookup_block (slot_copy_cond saCopy) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond saCopy;
             bb_instructions := slot_copy_cond_insts saCopy (type_slot_size tv)|> /\
    lookup_block (slot_copy_body saCopy) func.fn_blocks =
      SOME <|bb_label := slot_copy_body saCopy;
             bb_instructions := slot_copy_body_insts saCopy (Var ep) (Var xd)
               (if tr then TLOAD else SLOAD)|>
Proof
  strip_tac >> qpat_x_assum `loc = _` SUBST_ALL_TAC >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  qpat_x_assum `slot_loc tr = _` kall_tac >>
  qpat_assum `type_stmt _ _ _ = _`
    (mp_then (Pat `type_stmt _ _ _ = _`) (drule_all_then strip_assume_tac) slot_cut_sizes) >>
  qpat_x_assum `sty = fty` SUBST_ALL_TAC >>
  `word_scale (slot_loc tr) = 1 /\ is_slot_addressed (slot_loc tr) /\
   elem_size_in_location c (slot_loc tr) fty = type_slot_size tv` by
    (Cases_on `tr` >> simp[slot_loc_def, word_scale_def, is_slot_addressed_def,
       elem_size_in_location_def, ADD_DIV_RWT]) >>
  `stride = type_slot_size tv` by metis_tac[] >>
  `cap = 32 * type_slot_size tv` by metis_tac[] >>
  `!lbl. vv_operand vv <> Label lbl` by
    (qpat_assum `compile_expr c _ e _ = _`
       (mp_then Any (drule_all_then ACCEPT_TAC) slot_iterator_nonlabel)) >>
  `sa0.cs_next_var <= saL.cs_next_var /\ saL.cs_next_var <= sa.cs_next_var /\
   sa.cs_next_var <= saCopy.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at saL x ==> not_fresh_at sa x /\ not_fresh_at saCopy x /\
       slot_copy_external saCopy (Var x)` by
    (rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
                               LESS_EQ_TRANS,slot_copy_not_fresh_external]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x /\ not_fresh_at saCopy x` by
    (rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
                               LESS_EQ_TRANS]) >>
  `not_fresh_at saCopy xd /\ not_fresh_at saCopy idx` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x. vv_operand vv = Var x \/ len_op = Var x ==> not_fresh_at sa x /\
       not_fresh_at saCopy x` by
    (gen_tac >> strip_tac >>
     `not_fresh_at saL x` by simp[] >>
     qpat_assum `!y. not_fresh_at saL y ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `slot_copy_external saCopy (vv_operand vv) /\ slot_copy_external saCopy len_op` by
    (conj_tac >> irule slot_cut_external >> simp[]) >>
  simp[slot_copy_not_fresh_external] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!y. vv_operand vv = Var y \/ len_op = Var y ==> _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  qpat_assum `word_scale (slot_loc tr) = 1` (fn scale =>
    qpat_x_assum `let hdr = _ in _` (assume_tac o SRULE [scale])) >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then (Pat `emit_op MUL _ _ = _`) (drule_all_then strip_assume_tac)
       (SIMP_RULE (srw_ss()) [] slot_cut_address_ops)) >>
  qpat_assum `is_slot_addressed (slot_loc tr)` (fn isl =>
    qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`
      (mp_then Any (drule_then strip_assume_tac) slot_copy_physical_cut o SRULE [isl])) >>
  qexistsl [`ov`,`sum`,`ep`] >> gvs[slot_copy_not_fresh_external]
QED
