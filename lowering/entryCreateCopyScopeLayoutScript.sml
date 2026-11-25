(* Installed scalar and administrative intervals of create_copy_of. *)
Theory entryCreateCopyScopeLayout
Ancestors
  dallocaCreateGeometry createSizeStraightPrefix createSizePreparationCode
  createSizeOperandCode createSizeResultCheckCode loweringShapeRules
  entryCreateIntervalLayout entryCreateRegionLift entryCreatePendingScope
  entryCreateAdminSequence entryCreatePathScope entryCreateFocusSpec
  externalEntryShape builtinCreate compileEnv fragExec createSizeCutCode
  createSizePrefixReplay createSizeCutRegion entryCreateCompletedCut bodySim
  venomExecSemantics exprLowering emitHelper context venomInst loweringShapeDefs
  abiEncoderProps exprLoweringProps exprSimAbiGasBridge
  rich_list list arithmetic pair pred_set

(* In a suffix that already ends at b, extending its lower band does
   not move the stopping cursor. *)
Theorem copy_suffix_step_widen[local]:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E C f u ms v ==>
  create_prefix_step a b E C f u ms v
Proof
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem copy_scope_split_joins[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_layout a b /\
  create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code a b f /\
  create_operand_at a s ==>
  (!ms. create_operand_focus_scope a m E C f s ms ==>
        create_operand_focus_scope a b E C f s ms) /\
  (!ms r. exit_result r /\ create_operand_full_scope a m E C f s ms r ==>
          create_operand_full_scope a b E C f s ms r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
     create_operand_focus_scope m b E C f t right ==>
     create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
     create_operand_full_scope m b E C f t right r ==>
     create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\
   a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  `fn_has_code a m f /\ fn_has_code m b f` by metis_tac[fn_has_code_split] >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u` by metis_tac[create_layout_left_stop] >>
  `create_cut_region a m s` by
    metis_tac[create_operand_at_def,cj 1 create_cut_region_rules] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule create_left_focus_lift_at >>
      first_assum (irule_at Any) >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> irule create_left_terminal_lift_at >>
      first_assum (irule_at Any) >> simp[] >> metis_tac[])
  >- (simp[create_operand_full_scope_def] >> rpt strip_tac >>
      `create_expr_prefix a b E C f s left t` by
        (irule create_left_prefix_lift_at >> first_assum (irule_at Any) >>
         simp[] >> metis_tac[]) >>
      `create_cut_region m b t` by metis_tac[cj 1 create_cut_region_rules] >>
      irule create_operand_focus_scope_prepend >> first_assum (irule_at Any) >>
      irule create_operand_focus_scope_lift >>
      first_assum (irule_at Any) >> first_assum (irule_at Any) >>
      simp[] >> metis_tac[copy_suffix_step_widen]) >>
  simp[create_operand_full_scope_def] >> rpt strip_tac >>
  `create_expr_prefix a b E C f s left t` by
    (irule create_left_prefix_lift_at >> first_assum (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  Cases_on `r` >> fs[create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_mono,copy_suffix_step_widen,
            create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem copy_dispatch_closed_cut[local]:
  compile_create_dispatch buf len value salt rof sc = (result,sb) ==>
  create_cut_code {} sc sb
Proof
  strip_tac >>
  `create_cut_code {} sc (SND (compile_create_dispatch buf len value salt rof sc))` suffices_by simp[] >>
  pop_assum kall_tac >> pure_rewrite_tac[compile_create_dispatch_def] >>
  irule create_cut_code_bind >> simp[create_result_check_cut_code] >>
  Cases_on `salt` >> simp[create_cut_code_emit_op,create_cut_targets_def]
QED

(* Keep the actual compiler decomposition, rather than obtaining a second
   existential compilation that might not name the supplied dispatch cut. *)
Theorem copy_prepare_scope_layout[local]:
  emit_op EXTCODESIZE [target] sm = (code,g1) /\
  emit_void ASSERT [code] g1 = ((),g2) /\
  emit_op SHL [Lit 56w;code] g2 = (shifted,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
  emit_op ADD [code;Lit 32w] a4 = (request,a5) /\
  compile_alloc_dynamic request a5 = (alloc_ptr,a6) /\
  emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
  emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
  emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
  emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [code;Lit 11w] a10 = (len,sc) ==>
  create_cut_code {} sm sc /\ emitted_blocks sm sc = [] /\
  sc.cs_current_bb = sm.cs_current_bb /\
  sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc /\
  EVERY (\i. i.inst_id IN frag_ids sm sc /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sc) /\
  ?reg rest.
    code = Var reg /\ g1.cs_current_bb = sm.cs_current_bb /\
    LENGTH g1.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
    emitted_insts sm sc =
      mk_inst sm.cs_next_id EXTCODESIZE [target] [reg] ::
      mk_inst g1.cs_next_id ASSERT [code] [] :: rest
Proof
  strip_tac >> drule_all create_copy_preparation_code >> strip_tac >>
  `create_cut_code {} sm sc` by
    (irule (cj 5 create_preparation_cut_code) >> rpt (goal_assum (drule_at Any))) >>
  simp[] >>
  `emitted_blocks sm sc = [] /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm sc) /\
   ?reg rest. code = Var reg /\ g1.cs_current_bb = sm.cs_current_bb /\
    LENGTH g1.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
    emitted_insts sm sc = mk_inst sm.cs_next_id EXTCODESIZE [target] [reg] ::
      mk_inst g1.cs_next_id ASSERT [code] [] :: rest` by
    (fs[compile_alloc_dynamic_def,emit_op_eq,emit_void_eq] >> gvs[] >>
     SIMP_TAC pure_ss [emitted_blocks_def,emitted_insts_def,compile_state_accfupds,
       GSYM APPEND_ASSOC,APPEND,DROP_LENGTH_APPEND] >>
     simp[DROP_APPEND,DROP_LENGTH_TOO_LONG,mk_inst_def]) >>
  `frag_code sm sc = emitted_insts sm sc` by simp[frag_code_def] >>
  fs[create_cut_code_def, EVERY_MEM] >> metis_tac[]
QED

Theorem copy_guard_fetch_widen[local]:
  create_layout sm sb /\ create_cut_code {} sm sc /\ create_cut_code {} sc sb /\
  create_cut_region sm sc u /\ create_operand_fetch sm sc f u i ==>
  create_operand_fetch sm sb f u i
Proof
  simp[create_operand_fetch_def,create_cut_code_def,frag_ids_def] >>
  strip_tac >> metis_tac[create_layout_left_stop]
QED

Theorem copy_guard_installed[local]:
  create_layout sm sb /\ create_cut_code {} sm sc /\ create_cut_code {} sc sb /\
  fn_has_code sm sc f /\ emitted_blocks sm sc = [] /\
  sc.cs_current_bb = sm.cs_current_bb /\
  sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc /\
  g1.cs_current_bb = sm.cs_current_bb /\
  LENGTH g1.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
  emitted_insts sm sc = i0::i1::rest /\
  EVERY (\i. i.inst_id IN frag_ids sm sc /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sc) ==>
  (!u. create_operand_at sm u ==>
    create_operand_fetch sm sc f u i0 /\ create_operand_fetch sm sb f u i0) /\
  (!u. create_operand_at g1 u ==>
    create_operand_fetch sm sc f u i1 /\ create_operand_fetch sm sb f u i1)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  qpat_assum `emitted_insts sm sc = i0::i1::rest`
    (fn eq => qpat_x_assum `!j. _ ==> get_instruction _ _ = _`
      (assume_tac o REWRITE_RULE[eq])) >>
  `get_instruction bb (LENGTH sm.cs_current_insts) = SOME i0 /\
   get_instruction bb (SUC (LENGTH sm.cs_current_insts)) = SOME i1` by
    (conj_tac
     >- (qpat_assum `!j. _ ==> get_instruction _ _ = _`
           (qspec_then `0` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [EL]))) >>
     qpat_assum `!j. _ ==> get_instruction _ _ = _`
       (qspec_then `1` (mp_tac o SIMP_RULE (srw_ss()) [EL,EL_CONS])) >>
     pure_rewrite_tac[ADD1] >> simp[]) >>
  `SUC (LENGTH sm.cs_current_insts) < LENGTH sc.cs_current_insts` by simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  `create_cut_region sm sc u` by
    (simp[create_cut_region_def] >> fs[create_operand_at_def] >> decide_tac) >>
  `~create_operand_at sc u` by (fs[create_operand_at_def] >> decide_tac) >>
  `i0.inst_id IN frag_ids sm sc /\ i1.inst_id IN frag_ids sm sc` by
    (qpat_assum `emitted_insts sm sc = i0::i1::rest`
      (fn eq => qpat_assum `EVERY _ (emitted_insts sm sc)`
        (mp_tac o REWRITE_RULE[eq,EVERY_DEF])) >> simp[]) >>
  fs[create_operand_at_def] >>
  metis_tac[create_operand_fetch_def, copy_guard_fetch_widen, create_operand_at_def]
QED

(* The optional salt introduces an empty cut only in the NONE branch. *)
Theorem copy_salt_scope_code[local]:
  compile_create_salt compile_expr ce salt_e a = (salt,m) ==>
  create_cut_code {} a m /\
  (case salt_e of NONE => salt = NONE /\ m = a
   | SOME e => ?op. salt = SOME op /\
      lower_value compile_expr ce (expr_type e) e a = (op,m))
Proof
  Cases_on `salt_e` >> simp[compile_create_salt_def,comp_return_def,comp_bind_def] >>
  rename1 `lower_value compile_expr ce (expr_type e) e a` >>
  Cases_on `lower_value compile_expr ce (expr_type e) e a` >>
  simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`ce`,`expr_type e`,`e`,`a`] mp_tac (cj 2 create_operand_cut_code) >> simp[]
QED

Theorem copy_stage_scope_joins:
  lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a1) /\
  lower_value compile_expr ce (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr ce salt_e a2 = (salt,sm) /\
  emit_op EXTCODESIZE [target] sm = (code,g1) /\
  emit_void ASSERT [code] g1 = ((),g2) /\
  emit_op SHL [Lit 56w;code] g2 = (shifted,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
  emit_op ADD [code;Lit 32w] a4 = (request,a5) /\
  compile_alloc_dynamic request a5 = (alloc_ptr,a6) /\
  emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
  emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
  emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
  emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
  compile_create_dispatch buf len value salt rof sc = (result,sb) /\
  fn_has_code sa sb f /\ create_layout sa sb /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions ==>
  create_cut_code {} sm sc /\ create_cut_code {} sc sb /\
  fn_has_code sm sc f /\ fn_has_code sc sb f /\
  g1.cs_current_bb = sm.cs_current_bb /\
  LENGTH g1.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
  sc.cs_current_bb = sm.cs_current_bb /\
  sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc /\
  EVERY (\i. i.inst_id IN frag_ids sm sc /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sc) /\
  (?reg. code = Var reg /\
    (!u. create_operand_at sm u ==>
      create_operand_fetch sm sc f u (mk_inst sm.cs_next_id EXTCODESIZE [target] [reg]) /\
      create_operand_fetch sm sb f u (mk_inst sm.cs_next_id EXTCODESIZE [target] [reg])) /\
    (!u. create_operand_at g1 u ==>
      create_operand_fetch sm sc f u (mk_inst g1.cs_next_id ASSERT [code] []) /\
      create_operand_fetch sm sb f u (mk_inst g1.cs_next_id ASSERT [code] []))) /\
  (case salt_e of NONE => salt = NONE /\ sm = a2
   | SOME e => ?op. salt = SOME op /\
       lower_value compile_expr ce (expr_type e) e a2 = (op,sm)) /\
  !a m s. MEM (a,m) [(sa,a1);(a1,a2);(a2,sm);(sm,sc)] /\
    create_operand_at a s ==>
    (!ms. create_operand_focus_scope a m E C f s ms ==>
          create_operand_focus_scope a sb E C f s ms) /\
    (!ms r. exit_result r /\ create_operand_full_scope a m E C f s ms r ==>
            create_operand_full_scope a sb E C f s ms r) /\
    (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
       create_operand_focus_scope m sb E C f t right ==>
       create_operand_focus_scope a sb E C f s (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
       create_operand_full_scope m sb E C f t right r ==>
       create_operand_full_scope a sb E C f s (left ++ right) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all copy_prepare_scope_layout >> strip_tac >>
  drule copy_salt_scope_code >> strip_tac >>
  drule_then assume_tac copy_dispatch_closed_cut >>
  `create_cut_code {} sa a1 /\ create_cut_code {} a1 a2` by
    (map_every (fn qs => qspecl_then qs mp_tac (cj 2 create_operand_cut_code))
       [[`ce`,`expr_type target_e`,`target_e`,`sa`],
        [`ce`,`expr_type value_e`,`value_e`,`a1`]] >> simp[]) >>
  `create_cut_code {} sa a2 /\ create_cut_code {} sa sm /\
   create_cut_code {} a1 sb /\ create_cut_code {} a2 sb /\
   create_cut_code {} sm sb` by
    metis_tac[create_cut_code_join] >>
  `cs_extends sa a1 /\ cs_extends sa a2 /\ cs_extends sa sm /\
   cs_extends a1 sb /\ cs_extends a2 sb /\ cs_extends sm sb /\
   cs_extends sm sc /\ cs_extends sc sb` by fs[create_cut_code_def] >>
  `fn_has_code a1 sb f /\ fn_has_code a2 sb f /\ fn_has_code sm sb f` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sm sc f /\ fn_has_code sc sb f` by metis_tac[fn_has_code_split] >>
  `create_layout a1 sb /\ create_layout a2 sb /\ create_layout sm sb` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (qexists_tac `reg` >> simp[] >> irule copy_guard_installed >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >> irule copy_scope_split_joins >>
  first_assum (irule_at Any) >> simp[] >> metis_tac[]
QED
