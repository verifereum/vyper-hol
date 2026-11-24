(* Scope the administrative materialization at the witnesses selected by the
   full IfExp arm proof. *)
Theory entryCreateIfExpArm
Ancestors
  bodyFullIfExpPrepare bodyFullIfExpObserve
  entryCreateIfExpWidenSeq entryCreateIfExpTypedStore
  entryCreateIntervalLayout entryCreatePathScope createSizeLocationCode
  createSizeTypedCopyCode bodyFullAllocGeneric abiBufferAllocationCode
  bytesCopyCode entryCreateFocusSpec entryCreateCompletedCut
  abiEncoderProps exprLoweringProps fragExec venomState pair list
  createSizeCutRegion createSizePrefixReplay createMarkedPath
  createSizeCutCode venomExecProofs venomExecSemantics relation context
  abiEncoder exprLowering compileEnv

Definition ifexp_arm_scope_def:
  ifexp_arm_scope E C f a b s t <=>
    (create_layout a b ==>
       create_operand_at a s /\ create_operand_full_scope a b E C f s [] (OK t))
End

Triviality ifexp_alloc_observed_scoped:
  ifexp_observed_alloc (ifexp_arm_scope E) C f
Proof
  simp_tac bool_ss [ifexp_observed_alloc_def,ifexp_arm_scope_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  drule_all ifexp_alloc_selected_site >> strip_tac >> metis_tac[]
QED

Triviality ifexp_bytes_observed_scoped:
  ifexp_observed_bytes_store (ifexp_arm_scope E)
Proof
  simp_tac bool_ss [ifexp_observed_bytes_store_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32)` by simp[] >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`sf`] >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [ifexp_arm_scope_def] >> rpt strip_tac >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  drule_all ifexp_bytes_store_selected_site >> strip_tac >> metis_tac[]
QED

(* Embed the left run by its visited region, not just by its endpoint. *)
Triviality ifexp_arm_prefix_left:
  create_cut_code {} a m /\ create_cut_code {} m b /\
  create_layout a b /\ fn_has_code a m f /\ create_operand_at a s /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a m E C f s ms t ==>
  create_expr_prefix a b E C f s ms t
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\
   a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  drule_all create_cut_region_rules >> strip_tac >>
  `!bb. lookup_block m.cs_current_bb f.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  `create_cut_region a m s` by fs[create_operand_at_def] >>
  `!u chunk v. create_cut_region a m u /\ create_prefix_step a m E C f u chunk v ==>
       create_cut_region a m v /\ create_prefix_step a b E C f u chunk v` by
    (rpt gen_tac >> strip_tac >> fs[create_prefix_step_def] >>
     `~create_operand_at m u` by fs[create_operand_at_def] >>
     `~create_operand_at b u` by metis_tac[create_layout_left_stop] >>
     fs[create_operand_at_def, frag_ids_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a m E C f)) x y ==>
      create_cut_region a m (FST x) ==>
      create_cut_region a m (FST y) /\
      RTC (create_marked_edge (create_prefix_step a b E C f)) x y` suffices_by
    (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  simp_tac bool_ss [FORALL_PROD,FST,SND,create_marked_edge_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_assum `!u chunk v. create_cut_region a m u /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `create_cut_region a m _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 2 RTC_RULES) >> first_assum (irule_at Any) >>
  simp[create_marked_edge_def] >> metis_tac[]
QED

Triviality ifexp_arm_scope_join:
  create_cut_code {} a m /\ create_cut_code {} m b /\
  create_layout a b /\ fn_has_code a m f /\ create_operand_at a s /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_full_scope a m E C f s [] (OK u) /\
  create_operand_full_scope m b E C f u [] (OK t) ==>
  create_operand_full_scope a b E C f s [] (OK t)
Proof
  simp_tac bool_ss [create_operand_full_scope_def,exec_result_case_def] >> strip_tac >>
  drule_all ifexp_arm_prefix_left >> strip_tac >>
  `create_expr_prefix a b E C f u [] t` by
    (irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
     simp[create_prefix_step_def, create_cut_code_def, frag_ids_def] >>
     fs[create_cut_code_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >> metis_tac[create_expr_prefix_append,APPEND_NIL]
QED

Triviality ifexp_arm_widening_code:
  compile_alloc_buffer n a = (buf,b) /\
  unwrap_value cenv vv b = (src,c) /\
  (compile_store_bytestring src buf.buf_operand c = ((),d) \/
   compile_store_memory_typed cenv buf.buf_operand t src sty c = ((),d)) ==>
  create_cut_code {} a b /\ create_cut_code {} b c /\ create_cut_code {} c d
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  `create_cut_code {} a (SND (compile_alloc_buffer n a))` by
    simp[NoAsms,compile_alloc_buffer_def,create_cut_code_bind,
         create_cut_code_emit_op,create_cut_targets_def] >>
  `create_cut_code {} b (SND (unwrap_value cenv vv b))` by simp[create_unwrap_cut_code] >>
  `create_cut_code {} a b /\ create_cut_code {} b c` by metis_tac[SND] >>
  simp[] >> strip_tac
  >- (rename1 `compile_store_bytestring src dst c = ((),d)` >>
      `create_cut_code {} c (SND (compile_store_bytestring src dst c))` suffices_by simp[] >>
      rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
      rpt (irule create_cut_code_bind >> simp_tac bool_ss [] >> conj_tac) >>
      simp[create_cut_code_emit_op,create_cut_code_emit_void,create_cut_targets_def]) >>
  metis_tac[create_store_memory_typed_cut_code,SND]
QED

Triviality ifexp_widening_observed_scoped:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  ifexp_observed_widening (ifexp_arm_scope E) C f
Proof
  simp_tac bool_ss [ifexp_observed_widening_def,ifexp_arm_scope_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  `create_cut_code {} a b /\ create_cut_code {} b c /\ create_cut_code {} c d` by
    (irule ifexp_arm_widening_code >> rpt (first_assum (irule_at Any)) >> metis_tac[]) >>
  `create_cut_code {} b d` by metis_tac[create_cut_code_join] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ cs_extends b d` by
    fs[create_cut_code_def] >>
  `fn_has_code a b f /\ fn_has_code b c f` by metis_tac[fn_has_code_split] >>
  `create_layout a b /\ create_layout b c /\ create_layout c d /\ create_layout b d` by
    metis_tac[create_layout_subinterval,cs_extends_refl,cs_extends_trans] >>
  rpt (qpat_x_assum `create_layout _ _ ==> _` (drule_then strip_assume_tac)) >>
  `create_operand_full_scope b d E C f u [] (OK w)` by
    (irule ifexp_arm_scope_join >> asm_rewrite_tac[] >> qexistsl [`c`,`v`] >> simp[]) >>
  `create_operand_full_scope a d E C f s [] (OK w)` by
    (irule ifexp_arm_scope_join >> asm_rewrite_tac[] >> qexistsl [`b`,`u`] >> simp[]) >>
  asm_rewrite_tac[]
QED
