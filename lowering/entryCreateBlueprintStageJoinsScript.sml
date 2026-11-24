(* Scope joins on the actual blueprint compiler cuts. These facts do not
   execute any instruction, including ASSERT and the owning CREATE. *)
Theory entryCreateBlueprintStageJoins
Ancestors
  entryCreateRegionLift entryCreatePendingScope entryCreateIntervalLayout
  entryCreatePathScope entryCreateFocusSpec entryCreateCompletedCut
  entryCreateOperandReplay createSizePrefixReplay abiEncoderProps bodySim
  createSizeCutCode createSizeCutRegion
  createSizeItinerary createSizeResultCheckCode createSizeCutEntry createSizeDispatch
  builtinCreate emitHelper emitHelperProps fragExec exprLoweringProps exprLowering
  context compileEnv venomInst list rich_list arithmetic pred_set pair

Theorem blueprint_right_step[local]:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E C f u marks v ==>
  create_prefix_step a b E C f u marks v
Proof
  simp[create_prefix_step_def, frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem blueprint_right_full_append[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E C f s left u /\
  create_operand_full_scope m b E C f u right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono, blueprint_right_step,
            create_expr_prefix_append, APPEND_ASSOC]
QED

Theorem blueprint_right_focus_append[local]:
  a.cs_next_id <= m.cs_next_id /\ body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_cut_region m b u /\
  create_expr_prefix a b E C f s left u /\ create_operand_focus_scope m b E C f u right ==>
  create_operand_focus_scope a b E C f s (left ++ right)
Proof
  strip_tac >> irule create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule create_operand_focus_scope_lift >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >> simp[] >>
  metis_tac[blueprint_right_step]
QED

(* No strict growth is required at m: an empty constructor, absent salt or
   folded offset can have the very same compiler cut as its input. *)
Theorem blueprint_stage_scope_split:
  create_cut_code {} a m /\ create_cut_code {} m b /\ fn_has_code a b f /\
  create_layout a b /\ body_inv tops C ce cx /\ MEM f C.ctx_functions ==>
  fn_has_code a m f /\ fn_has_code m b f /\
  frag_ids a m SUBSET frag_ids a b /\
  (!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) /\
  (!u i. create_cut_region a m u /\ create_operand_fetch a m f u i ==>
         create_operand_fetch a b f u i) /\
  (!s. create_operand_at a s ==>
    (!marks. create_operand_focus_scope a m E C f s marks ==>
             create_operand_focus_scope a b E C f s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
               create_operand_full_scope a b E C f s marks r) /\
    (!left u. create_expr_prefix a m E C f s left u ==>
              create_expr_prefix a b E C f s left u) /\
    (!left u right. create_expr_prefix a m E C f s left u /\ create_operand_at m u /\
                    create_operand_focus_scope m b E C f u right ==>
                    create_operand_focus_scope a b E C f s (left ++ right)) /\
    (!left u right r. create_expr_prefix a m E C f s left u /\
                      create_operand_full_scope m b E C f u right r ==>
                      create_operand_full_scope a b E C f s (left ++ right) r))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
   m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `fn_has_code a m f /\ fn_has_code m b f` by metis_tac[fn_has_code_split] >>
  `frag_ids a m SUBSET frag_ids a b` by
    (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  simp[] >> conj_tac
  >- (fs[SUBSET_DEF] >> simp[create_operand_fetch_def] >> metis_tac[]) >>
  qx_gen_tac `s` >> strip_tac >>
  `create_cut_region a m s` by metis_tac[create_operand_at_def, cj 1 create_cut_region_rules] >>
  `!left u. create_expr_prefix a m E C f s left u ==> create_expr_prefix a b E C f s left u` by
    metis_tac[create_left_prefix_lift_at] >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- metis_tac[create_left_focus_lift_at]
  >- metis_tac[create_left_terminal_lift_at]
  >- (`create_cut_region m b u` by metis_tac[create_operand_at_def, cj 1 create_cut_region_rules] >>
      metis_tac[blueprint_right_focus_append]) >>
  metis_tac[blueprint_right_full_append]
QED

Theorem blueprint_itinerary_code_band[local]:
  !cuts a b. create_itinerary_code a cuts b ==> create_cut_code {} a b
Proof
  Induct >> simp[create_itinerary_code_def] >> metis_tac[create_cut_code_join]
QED

Theorem blueprint_args_itinerary_last[local]:
  create_blueprint_args_itinerary ce raw later es a prep buf len b ==>
  LAST (a::prep) = b
Proof
  simp[create_blueprint_args_itinerary_def] >> rpt strip_tac >>
  simp[] >> pure_once_rewrite_tac[GSYM APPEND] >> simp[]
QED

Theorem blueprint_append_itinerary_last[local]:
  create_blueprint_append_itinerary target off code buf len f app out total_op ==>
  app <> []
Proof
  Cases_on `len = Lit 0w` >> simp[create_blueprint_append_itinerary_def] >>
  rpt strip_tac >> gvs[]
QED

(* Compress the constructor and append sub-itineraries, without guessing
   their lengths or requiring a strict change of PC at the keyword cuts. *)
Theorem blueprint_itinerary_stage_bands[local]:
  create_itinerary_code sa (a :: (prep ++ [c;d;e;f] ++ app)) sc /\
  create_blueprint_args_itinerary ce raw later es a prep buf len b ==>
  create_cut_code {} sa a /\ create_cut_code {} a b /\
  create_cut_code {} b c /\ create_cut_code {} c d /\
  create_cut_code {} d e /\ create_cut_code {} e f /\
  create_cut_code {} f sc /\ LAST (f::app) = sc
Proof
  simp[create_itinerary_code_def] >> strip_tac >>
  rename1 `create_itinerary_code a prep b0` >>
  `b0 = b` by metis_tac[blueprint_args_itinerary_last, create_itinerary_code_relations] >>
  gvs[] >>
  metis_tac[blueprint_itinerary_code_band, create_itinerary_code_relations]
QED

Theorem blueprint_bands_to_exit[local]:
  !cuts a z.
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    create_cut_code {} (LAST (a::cuts)) z ==>
    create_cut_code {} a z
Proof
  Induct >> simp[FRONT_CONS] >> metis_tac[create_cut_code_join]
QED

Theorem blueprint_installed_bands[local]:
  !cuts a z fn.
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    create_cut_code {} (LAST (a::cuts)) z /\
    fn_has_code a z fn /\ create_layout a z ==>
    LIST_REL (\p q. create_cut_code {} p q /\ create_cut_code {} q z /\
                     fn_has_code p z fn /\ create_layout p z)
             (FRONT (a::cuts)) cuts
Proof
  Induct >> simp[FRONT_CONS] >> rpt gen_tac >> strip_tac >>
  `create_cut_code {} h z` by metis_tac[blueprint_bands_to_exit] >>
  simp[] >> first_x_assum irule >> simp[] >>
  fs[create_cut_code_def] >>
  metis_tac[fn_has_code_split,create_layout_subinterval,cs_extends_refl]
QED

Theorem blueprint_dispatch_cut_code[local]:
  create_size_dispatch_tail rof sc sd created bufop len value salt result sb ==>
  create_cut_code {} sc sd /\ create_cut_code {} sd sb
Proof
  Cases_on `salt` >> simp[create_size_dispatch_tail_def] >> strip_tac >>
  `create_cut_code {} sd sb` by metis_tac[create_result_check_cut_code,SND] >>
  simp[]
  >- (`create_cut_code {} sc (SND (emit_op CREATE [value;bufop;len] sc))`
        suffices_by simp[] >> irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
  rename1 `emit_op CREATE2 [value;bufop;len;x] sc = (created,sd)` >>
  `create_cut_code {} sc (SND (emit_op CREATE2 [value;bufop;len;x] sc))`
    suffices_by simp[] >> irule create_cut_code_emit_op >> simp[create_cut_targets_def]
QED

(* Supply exactly the code, installation and layout premises of
   blueprint_stage_scope_split, at each actual stage through the append.
   Apply this to the ordinary and shadow itineraries independently. *)
Theorem blueprint_stage_scope_joins_at:
  create_itinerary_code sa (a :: (prep ++ [c;d;e;f] ++ app)) sc /\
  create_blueprint_args_itinerary ce raw later es a prep args_buf args_len b /\
  create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
  fn_has_code sa sb fn /\ create_layout sa sb ==>
  LIST_REL (\p q. create_cut_code {} p q /\ create_cut_code {} q sb /\
                   fn_has_code p sb fn /\ create_layout p sb)
           [sa;a;b;c;d;e;f] [a;b;c;d;e;f;sc]
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_itinerary_stage_bands >> strip_tac >>
  drule blueprint_dispatch_cut_code >> strip_tac >>
  qspecl_then [`[a;b;c;d;e;f;sc]`,`sa`,`sb`,`fn`] mp_tac blueprint_installed_bands >>
  simp[FRONT_DEF] >> metis_tac[create_cut_code_join]
QED

Theorem blueprint_stage_scope_joins:
  create_blueprint_itinerary ce raw salted args sa cuts value salt bufop len /\
  create_itinerary_code sa cuts sc /\
  create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
  fn_has_code sa sb fn /\ create_layout sa sb ==>
  ?target_e value_e rest suffix later target a prep args_buf args_len b c d off e code f app.
    args = target_e::value_e::rest /\ (if salted then 2 else 1) <= LENGTH rest /\
    suffix = (if salted then TL rest else rest) /\
    later = value_e :: TAKE (if salted then 2 else 1) rest /\
    lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a) /\
    create_blueprint_args_itinerary ce raw later (TL suffix) a prep args_buf args_len b /\
    lower_value compile_expr ce (expr_type value_e) value_e b = (value,c) /\
    create_itinerary_salt ce (if salted then SOME (HD rest) else NONE) c salt d /\
    create_blueprint_offset_run ce (HD suffix) d off e /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value (HD suffix)))
      target off e = (code,f) /\
    create_blueprint_append_itinerary target off code args_buf args_len f app bufop len /\
    cuts = a :: (prep ++ [c;d;e;f] ++ app) /\ sc = LAST app /\
    LIST_REL (\p q. create_cut_code {} p q /\ create_cut_code {} q sb /\
                     fn_has_code p sb fn /\ create_layout p sb)
             [sa;a;b;c;d;e;f] [a;b;c;d;e;f;sc]
Proof
  simp[create_blueprint_itinerary_def] >> strip_tac >>
  `create_itinerary_code sa (a :: (prep ++ [c;d;e;f] ++ app)) sc` by metis_tac[] >>
  drule_all blueprint_stage_scope_joins_at >> strip_tac >>
  `sc = LAST app` by
    (drule_all blueprint_itinerary_stage_bands >> strip_tac >>
     `app <> []` by metis_tac[blueprint_append_itinerary_last] >> Cases_on `app` >> gvs[]) >>
  qexistsl_tac [`target_e`,`value_e`,`rest`,`target`,`a`,`prep`,`args_buf`,`args_len`,
                `b`,`c`,`d`,`off`,`e`,`code`,`f`,`app`] >>
  fs[]
QED

(* At slot three the check has not reached its normal exit. The ASSERT
   fetched there is inside the outer region as well, even on failure. *)
Theorem blueprint_check_assert_cut:
  create_cut_code {} a m /\ create_cut_code {} m b /\ create_layout a b /\
  fn_has_code a b fn /\
  m.cs_current_bb = a.cs_current_bb /\
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  MAP (\i. i.inst_opcode) (emitted_insts a m) =
    (if lit then [EXTCODESIZE; SUB; SGT; ASSERT] else [EXTCODESIZE; GT; SUB; ASSERT]) /\
  EVERY (\i. i.inst_id IN frag_ids a m /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts a m) /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts + 3 ==>
  create_cut_region a m s /\ ~create_operand_at m s /\ ~create_operand_at b s /\
  ?i. i.inst_opcode = ASSERT /\ create_operand_fetch a m fn s i /\
      create_operand_fetch a b fn s i
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH (emitted_insts a m) = 4` by
    (qpat_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH : opcode list -> num``) >>
     Cases_on `lit` >> simp[]) >>
  `create_cut_region a m s /\ ~create_operand_at m s` by
    (simp[create_cut_region_def,create_operand_at_def]) >>
  `cs_extends a m /\ cs_extends m b` by fs[create_cut_code_def] >>
  `~create_operand_at b s` by metis_tac[create_layout_left_stop] >>
  `fn_has_code a m fn` by metis_tac[fn_has_code_split] >>
  `frag_ids a m SUBSET frag_ids a b` by
    (fs[create_cut_code_def,frag_ids_def,SUBSET_DEF] >> decide_tac) >>
  simp[] >> drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `3` mp_tac) >> simp[] >> strip_tac >>
  `EL 3 (MAP (\i. i.inst_opcode) (emitted_insts a m)) = ASSERT` by
    (Cases_on `lit` >> fs[]) >>
  `EL 3 (MAP (\i. i.inst_opcode) (emitted_insts a m)) =
     (EL 3 (emitted_insts a m)).inst_opcode` by
    (qpat_assum `LENGTH (emitted_insts _ _) = 4`
       (fn th => simp[NoAsms,th,listTheory.EL_MAP])) >>
  qexists_tac `EL 3 (emitted_insts a m)` >>
  fs[EVERY_EL,SUBSET_DEF,create_operand_fetch_def] >> metis_tac[DECIDE ``3n < 4``]
QED

(* This fetch is owned by the dispatch segment. At precisely this PC the
   append has reached its cut, so an append step at this fetch is excluded. *)
Theorem blueprint_append_dispatch_cut:
  create_cut_code {} a sc /\
  create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
  fn_has_code a sb fn /\ create_layout a sb /\ create_operand_at sc s ==>
  ~create_operand_at sb s /\
  ?i. i.inst_opcode = (if salt = NONE then CREATE else CREATE2) /\
      i.inst_id NOTIN frag_ids a sc /\
      create_operand_fetch sc sd fn s i /\ create_operand_fetch sc sb fn s i /\
      ~create_operand_fetch a sc fn s i
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule blueprint_dispatch_cut_code >> strip_tac >>
  `create_cut_code {} sc sb` by metis_tac[create_cut_code_join] >>
  `cs_extends a sc /\ cs_extends sc sd /\ cs_extends sd sb /\ cs_extends sc sb` by
    fs[create_cut_code_def] >>
  `create_layout sc sb` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `fn_has_code sc sd fn` by metis_tac[fn_has_code_mid] >>
  Cases_on `salt` >> fs[create_size_dispatch_tail_def] >>
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
  `create_cut_region sc sd s` by
    metis_tac[create_operand_at_def,cj 1 create_cut_region_rules] >>
  `~create_operand_at sd s` by fs[create_operand_at_def] >>
  `~create_operand_at sb s` by metis_tac[create_layout_left_stop] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction _ _ = SOME i` >>
  `sc.cs_next_id < sb.cs_next_id` by (fs[create_cut_code_def] >> decide_tac) >>
  simp[] >> qexists_tac `i` >>
  fs[create_operand_fetch_def,create_operand_at_def,frag_ids_def] >>
  simp[Abbr `i`,mk_inst_def] >> metis_tac[]
QED

(* The append layout can be used without importing its producer. Its
   installed instructions stop before the dispatch PC. *)
Theorem blueprint_append_installed_slots:
  create_cut_code {} a sc /\ create_cut_code {} sc sb /\ fn_has_code a sb fn /\
  sc.cs_current_bb = a.cs_current_bb /\
  sc.cs_current_insts = a.cs_current_insts ++ emitted_insts a sc /\
  MAP (\i. i.inst_opcode) (emitted_insts a sc) =
    (if len = Lit 0w then [ADD; DALLOCA; EXTCODECOPY]
     else [ADD; DALLOCA; EXTCODECOPY; ADD; MCOPY]) ==>
  ?bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       LENGTH sc.cs_current_insts = LENGTH a.cs_current_insts +
                                    (if len = Lit 0w then 3 else 5) /\
       !j. j < (if len = Lit 0w then 3 else 5) ==>
           get_instruction bb (LENGTH a.cs_current_insts + j) =
             SOME (EL j (emitted_insts a sc)) /\
           LENGTH a.cs_current_insts + j < LENGTH sc.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_has_code a sc fn` by (fs[create_cut_code_def] >> metis_tac[fn_has_code_split]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH (emitted_insts a sc) = (if len = Lit 0w then 3 else 5)` by
    (qpat_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH : opcode list -> num``) >>
     Cases_on `len = Lit 0w` >> simp[]) >>
  qexists_tac `bb` >> simp[]
QED
