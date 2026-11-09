(* Label-preservation and block-stream shape facts about the lowered
   runtime unit's entry code, for the s1-entry-return pieces. *)
Theory externalEntryShape
Ancestors
  list rich_list loweringShapeDefs loweringShapeRules loweringShapeProps
  moduleLoweringProps compileEnv loweringStateRelDefs context emitHelper emitHelperProps fragExec
  exprLowering stmtLowering moduleLowering vyperCompiler compileVyper
  abiEncoder supportedProgram supportedNames supportedStmtTraverse
  supportedExprTraverse supportedTargets unitShapeDefs venomInst vyperAST
  cfgNormSim exprCallBounds
Libs
  monadsyntax dep_rewrite wordsLib

(* Chronological streams retain the first occurrence of an open block. *)
Theorem cs_extends_block_stream_labels:
  !sa sb. cs_extends sa sb ==>
    ?bb tail.
      all_blocks sb = REVERSE sa.cs_blocks ++ bb::tail /\
      bb.bb_label = sa.cs_current_bb /\
      isPREFIX sa.cs_current_insts bb.bb_instructions /\
      MAP (\b. b.bb_label) tail = added_labels sa sb
Proof
  rpt gen_tac >> simp[cs_extends_def] >> strip_tac >>
  Cases_on `new = []`
  >- (gvs[] >>
      qexistsl_tac [`<| bb_label := sb.cs_current_bb;
                        bb_instructions := sb.cs_current_insts |>`, `[]`] >>
      simp[all_blocks_def, added_labels_def]) >>
  `?h t. REVERSE new = h::t` by
    (Cases_on `REVERSE new` >> gvs[]) >>
  `new = REVERSE t ++ [h]` by metis_tac[REVERSE_REVERSE, REVERSE_DEF] >>
  gvs[LAST_APPEND_NOT_NIL] >>
  qexistsl_tac [`h`, `t ++ [<| bb_label := sb.cs_current_bb;
                             bb_instructions := sb.cs_current_insts |>]`] >>
  simp[all_blocks_def, added_labels_def, REVERSE_APPEND, DROP_LENGTH_APPEND,
       DROP_APPEND, LENGTH_MAP, DROP_LENGTH_TOO_LONG] >>
  `1 - SUC (LENGTH t) = 0` by decide_tac >> simp[]
QED

Theorem cs_extends_finished_lookup:
  !sa sb lbl bb.
    cs_extends sa sb /\
    lookup_block lbl (REVERSE sa.cs_blocks) = SOME bb ==>
    lookup_block lbl (all_blocks sb) = SOME bb
Proof
  rpt strip_tac >> drule cs_extends_block_stream_labels >> strip_tac >>
  gvs[lookup_block_APPEND]
QED

Theorem cs_extends_open_lookup:
  !sa sb.
    cs_extends sa sb /\
    ~MEM sa.cs_current_bb
      (MAP (\b. b.bb_label) (REVERSE sa.cs_blocks)) ==>
    ?bb. lookup_block sa.cs_current_bb (all_blocks sb) = SOME bb /\
         isPREFIX sa.cs_current_insts bb.bb_instructions
Proof
  rpt strip_tac >> drule cs_extends_block_stream_labels >> strip_tac >>
  `lookup_block sa.cs_current_bb (REVERSE sa.cs_blocks) = NONE` by
    simp[lookup_block_NONE] >>
  qexists_tac `bb` >> simp[lookup_block_APPEND] >>
  simp[lookup_block_def, FIND_thm]
QED

Theorem compile_state_ok_all_blocks_distinct:
  !st. compile_state_ok st ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks st))
Proof
  simp[compile_state_ok_def, all_blocks_def, MAP_REVERSE,
       ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MEM_MAP] >>
  metis_tac[]
QED

Theorem cs_extends_fn_has_code:
  !sa sd se func.
    compile_state_ok sd /\ cs_extends sd se /\
    func.fn_blocks = all_blocks se ==> fn_has_code sa sd func
Proof
  rpt strip_tac >> simp[fn_has_code_def] >> conj_tac
  >- (rpt strip_tac >>
      `MEM bb sd.cs_blocks` by
        metis_tac[emitted_blocks_def, MEM_TAKE] >>
      irule cs_extends_finished_lookup >>
      qexists_tac `sd` >> simp[] >>
      irule venomExecProofsTheory.MEM_lookup_block >>
      fs[compile_state_ok_def, MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
  irule cs_extends_open_lookup >>
  fs[compile_state_ok_def, MAP_REVERSE]
QED

(* Label-only extension does not constrain the instructions of the open block. *)
Theorem cs_extends_labels:
  !a b. cs_extends a b ==>
    MAP (\bb. bb.bb_label) (all_blocks b) =
      MAP (\bb. bb.bb_label) (all_blocks a) ++ added_labels a b
Proof
  rpt strip_tac >> drule cs_extends_block_stream_labels >> strip_tac >>
  gvs[all_blocks_def, MAP_APPEND]
QED

Theorem added_labels_trans:
  !a b c. cs_extends a b /\ cs_extends b c ==>
    added_labels a c = added_labels a b ++ added_labels b c
Proof
  rpt strip_tac >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  qpat_assum `cs_extends a b` (mp_tac o MATCH_MP cs_extends_labels) >>
  qpat_assum `cs_extends b c` (mp_tac o MATCH_MP cs_extends_labels) >>
  qpat_assum `cs_extends a c` (mp_tac o MATCH_MP cs_extends_labels) >>
  rpt disch_tac >> metis_tac[APPEND_ASSOC, APPEND_11]
QED

Theorem cs_extends_labels_trans:
  !a b c P.
    cs_extends a b /\ cs_extends b c /\
    EVERY P (added_labels a b) /\ EVERY P (added_labels b c) ==>
    cs_extends a c /\ EVERY P (added_labels a c)
Proof
  rpt strip_tac
  >- metis_tac[cs_extends_trans] >>
  drule_all added_labels_trans >> simp[]
QED

Theorem comp_bind_labels:
  !m k P.
    (!s. cs_extends s (SND (m s)) /\
         EVERY P (added_labels s (SND (m s)))) /\
    (!x s. cs_extends s (SND (k x s)) /\
           EVERY P (added_labels s (SND (k x s)))) ==>
    !s. cs_extends s (SND (comp_bind m k s)) /\
        EVERY P (added_labels s (SND (comp_bind m k s)))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[comp_bind_def] >> pairarg_tac >> gvs[] >>
  irule cs_extends_labels_trans >> qexists_tac `cs'` >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem application_labels:
  !s p k P.
    (cs_extends s (SND p) /\ EVERY P (added_labels s (SND p))) /\
    (!x t. cs_extends t (SND (k (x,t))) /\
           EVERY P (added_labels t (SND (k (x,t))))) ==>
    cs_extends s (SND (k p)) /\ EVERY P (added_labels s (SND (k p)))
Proof
  rpt gen_tac >> PairCases_on `p` >> simp[] >> strip_tac >>
  irule cs_extends_labels_trans >> qexists_tac `p1` >> simp[]
QED

Theorem pair_case_labels:
  !s p k P.
    (cs_extends s (SND p) /\ EVERY P (added_labels s (SND p))) /\
    (!x t. cs_extends t (SND (k x t)) /\ EVERY P (added_labels t (SND (k x t)))) ==>
    cs_extends s (SND ((\(x,t). k x t) p)) /\
    EVERY P (added_labels s (SND ((\(x,t). k x t) p)))
Proof
  rpt gen_tac >> PairCases_on `p` >> simp[] >> strip_tac >>
  irule cs_extends_labels_trans >> qexists_tac `p1` >> simp[]
QED

Theorem added_labels_new_block:
  !lbl s v t. new_block lbl s = (v,t) ==> added_labels s t = [lbl]
Proof
  rpt gen_tac >> simp[new_block_def] >> strip_tac >>
  gvs[] >> simp[added_labels_def, all_blocks_def, MAP_APPEND] >>
  once_rewrite_tac[DROP_APPEND] >> simp[]
QED

Theorem added_labels_emit:
  !inst s v t. emit inst s = (v,t) ==> added_labels s t = []
Proof
  rpt gen_tac >> simp[emit_def] >> strip_tac >>
  gvs[added_labels_def, all_blocks_def, MAP_APPEND, LENGTH_MAP]
QED

Theorem added_labels_fresh_var:
  !s v t. fresh_var s = (v,t) ==> added_labels s t = []
Proof
  rpt gen_tac >> simp[fresh_var_def] >> strip_tac >>
  gvs[added_labels_def, all_blocks_def, MAP_APPEND, LENGTH_MAP]
QED

Theorem added_labels_fresh_label:
  !sfx s v t. fresh_label sfx s = (v,t) ==> added_labels s t = []
Proof
  rpt gen_tac >> simp[fresh_label_def] >> strip_tac >>
  gvs[added_labels_def, all_blocks_def, MAP_APPEND, LENGTH_MAP]
QED

Theorem comp_return_labels:
  !x s P. cs_extends s (SND (comp_return x s)) /\
    EVERY P (added_labels s (SND (comp_return x s)))
Proof
  simp[comp_return_def, cs_extends_refl, added_labels_def, all_blocks_def,
       MAP_APPEND] >> once_rewrite_tac[DROP_APPEND] >>
  simp[DROP_LENGTH_TOO_LONG]
QED

Theorem new_block_labels:
  !lbl s v t P. new_block lbl s = (v,t) /\ P lbl ==>
    cs_extends s t /\ EVERY P (added_labels s t)
Proof
  rpt strip_tac
  >- metis_tac[cs_extends_new_block] >>
  drule added_labels_new_block >> simp[]
QED

Theorem emit_labels:
  !inst s v t P. emit inst s = (v,t) ==>
    cs_extends s t /\ EVERY P (added_labels s t)
Proof
  rpt strip_tac
  >- metis_tac[cs_extends_emit] >>
  drule added_labels_emit >> simp[]
QED

Theorem fresh_var_labels:
  !s v t P. fresh_var s = (v,t) ==>
    cs_extends s t /\ EVERY P (added_labels s t)
Proof
  rpt strip_tac
  >- metis_tac[cs_extends_fresh_var] >>
  drule added_labels_fresh_var >> simp[]
QED

Theorem fresh_label_labels:
  !sfx s v t P. fresh_label sfx s = (v,t) ==>
    cs_extends s t /\ EVERY P (added_labels s t)
Proof
  rpt strip_tac
  >- metis_tac[cs_extends_fresh_label] >>
  drule added_labels_fresh_label >> simp[]
QED

Theorem invalid_expr_call_labels:
  !ty s P. cs_extends s (SND (invalid_expr_call ty s)) /\
    EVERY P (added_labels s (SND (invalid_expr_call ty s)))
Proof
  rpt gen_tac >>
  simp[invalid_expr_call_def, emit_inst_def, comp_bind_def,
       fresh_id_def, emit_def] >>
  conj_tac
  >- (irule cs_extends_same_block >> simp[]) >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem expr_child_callback_labels:
  !bound f P.
    (!ce ty e s. expr_size e < bound ==>
      cs_extends s (SND (f ce ty e s)) /\
      EVERY P (added_labels s (SND (f ce ty e s)))) ==>
    !ce ty e s.
      cs_extends s (SND (expr_child_callback bound f ce ty e s)) /\
      EVERY P (added_labels s (SND (expr_child_callback bound f ce ty e s)))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  Cases_on `expr_size e < bound` >> simp[invalid_expr_call_labels]
QED

Theorem builtin_child_callback_labels:
  !bound f P.
    (!ce rt ty bi args s. list_size expr_size args < bound ==>
      cs_extends s (SND (f ce rt ty bi args s)) /\
      EVERY P (added_labels s (SND (f ce rt ty bi args s)))) ==>
    !ce rt ty bi args s.
      cs_extends s (SND (builtin_child_callback bound f ce rt ty bi args s)) /\
      EVERY P (added_labels s
        (SND (builtin_child_callback bound f ce rt ty bi args s)))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size args < bound` >> simp[invalid_expr_call_labels]
QED

Theorem type_child_callback_labels:
  !bound f P.
    (!ce vt ty tb rt args s. list_size expr_size args < bound ==>
      cs_extends s (SND (f ce vt ty tb rt args s)) /\
      EVERY P (added_labels s (SND (f ce vt ty tb rt args s)))) ==>
    !ce vt ty tb rt args s.
      cs_extends s (SND (type_child_callback bound f ce vt ty tb rt args s)) /\
      EVERY P (added_labels s
        (SND (type_child_callback bound f ce vt ty tb rt args s)))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size args < bound` >> simp[invalid_expr_call_labels]
QED

(* Label-only sequencing interfaces used by compiler body proofs. *)
Theorem comp_ignore_bind_labels:
  !m k P.
    (!s. cs_extends s (SND (m s)) /\
         EVERY P (added_labels s (SND (m s)))) /\
    (!s. cs_extends s (SND (k s)) /\
         EVERY P (added_labels s (SND (k s)))) ==>
    !s. cs_extends s (SND (comp_ignore_bind m k s)) /\
        EVERY P (added_labels s (SND (comp_ignore_bind m k s)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[comp_ignore_bind_def] >> irule comp_bind_labels >> simp[]
QED

Theorem uncurry_labels:
  !f P.
    (!x y s. cs_extends s (SND (f x y s)) /\
             EVERY P (added_labels s (SND (f x y s)))) ==>
    !xy s. cs_extends s (SND (UNCURRY f xy s)) /\
           EVERY P (added_labels s (SND (UNCURRY f xy s)))
Proof
  rpt strip_tac >> PairCases_on `xy` >> simp[]
QED

Theorem fresh_id_labels:
  !s P. cs_extends s (SND (fresh_id s)) /\
    EVERY P (added_labels s (SND (fresh_id s)))
Proof
  rpt gen_tac >> simp[fresh_id_def] >> conj_tac
  >- (irule cs_extends_same_block >> simp[]) >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem fresh_label_prefix:
  !suffix (s:compile_state) lbl t. fresh_label suffix s = (lbl,t) ==>
    isPREFIX "@" lbl
Proof
  rpt strip_tac >> gvs[compileEnvTheory.fresh_label_def,
    fresh_label_output_def]
QED

Theorem emit_op_labels:
  !opc ops s P. cs_extends s (SND (emit_op opc ops s)) /\
    EVERY P (added_labels s (SND (emit_op opc ops s)))
Proof
  rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> conj_tac
  >- (irule cs_extends_same_block >> simp[]) >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem emit_void_labels:
  !opc ops s P. cs_extends s (SND (emit_void opc ops s)) /\
    EVERY P (added_labels s (SND (emit_void opc ops s)))
Proof
  rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >> conj_tac
  >- (irule cs_extends_same_block >> simp[]) >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem emit_inst_labels:
  !opc ops outs s P. cs_extends s (SND (emit_inst opc ops outs s)) /\
    EVERY P (added_labels s (SND (emit_inst opc ops outs s)))
Proof
  rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> conj_tac
  >- (irule cs_extends_same_block >> simp[]) >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem fresh_vars_labels:
  !n s P. cs_extends s (SND (fresh_vars n s)) /\
    EVERY P (added_labels s (SND (fresh_vars n s)))
Proof
  Induct >> simp[fresh_vars_def, comp_return_labels] >> rpt gen_tac >>
  irule comp_bind_labels >> reverse conj_tac
  >- (simp[fresh_var_def] >> rpt strip_tac
      >- (irule cs_extends_same_block >> simp[]) >>
      simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  rpt gen_tac >> BETA_TAC >> irule comp_bind_labels >> simp[comp_return_labels]
QED

Theorem emit_multi_op_labels:
  !opc ops n s P. cs_extends s (SND (emit_multi_op opc ops n s)) /\
    EVERY P (added_labels s (SND (emit_multi_op opc ops n s)))
Proof
  rpt gen_tac >> simp[emit_multi_op_def] >>
  irule comp_bind_labels >> simp[fresh_vars_labels] >>
  rpt gen_tac >> irule comp_ignore_bind_labels >>
  simp[emit_inst_labels, comp_return_labels]
QED


Theorem compile_external_fn_bodies_label_shape:
  !fns.
    EVERY external_fn_shape_ok fns ==>
    shape_step F (\l. compiler_label l \/ MEM l (MAP FST fns))
      (\st. T) (compile_external_fn_bodies fns) (\x st. T)
Proof
  Induct >> simp_tac std_ss [listTheory.EVERY_DEF]
  >- (pure_rewrite_tac[compile_external_fn_bodies_def] >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  pure_rewrite_tac[external_fn_shape_ok_def] >> strip_tac >>
  pure_rewrite_tac[compile_external_fn_bodies_def] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule shape_step_conseq >>
              qexistsl_tac [`\l. compiler_label l \/ MEM l (MAP FST fns)`,
                           `\st. T`, `\u st. T`] >>
              simp[] >> metis_tac[]) >>
          irule shape_step_conseq >>
          qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
          simp[] >> irule compile_external_function_body_shape >> simp[]) >>
      irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. T`, `\u st. T`] >>
      simp[] >> irule compile_entry_checks_shape) >>
  ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def] >>
  irule jump_label_ok_not_internal >> simp[jump_label_ok_def]
QED

Theorem compile_external_fn_bodies_label_absent:
  !fns sd sa lbl.
    EVERY external_fn_shape_ok fns /\ shape_state sd /\
    compile_external_fn_bodies fns sd = ((), sa) /\
    ~MEM lbl (MAP FST fns) /\ ~compiler_label lbl /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd)) ==>
    shape_state sa /\
    EVERY (\l. compiler_label l \/ MEM l (MAP FST fns)) (added_labels sd sa) /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sa))
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_fn_bodies_label_shape >>
  rewrite_tac[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  fs[shape_extends_def] >>
  drule cs_extends_block_stream_labels >> strip_tac >>
  `lbl <> sd.cs_current_bb` by
    (qpat_x_assum `~MEM lbl (MAP _ (all_blocks sd))` mp_tac >>
     simp[all_blocks_def]) >>
  `~MEM lbl (MAP (\b. b.bb_label) tail)` by
    (simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  gvs[all_blocks_def, MAP_APPEND, MEM_MAP] >> metis_tac[]
QED


Theorem runtime_fallback_suffix_shape:
  !fallback_fn fb.
    fallback_shape_ok fallback_fn /\ jump_label_ok fb ==>
    shape_step F jump_label_ok (\st. T)
      (do new_block fb;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_ce,fb_pay,fb_nr,fb_key,fb_ut,fb_iv,fb_body,fb_rt) =>
               compile_fallback_body fb_ce fb_pay fb_nr fb_key fb_ut fb_iv fb_body fb_rt)
       od) (\x st. T)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_ignore_bind >> qexists_tac `\x st. T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule runtime_fallback_shape >> simp[]) >>
  ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def]
QED


(* compile_generate_runtime_shape, also naming the entry code's state. *)
Theorem compile_generate_runtime_entry_shape:
  !selectors external_fns internal_fns fallback_fn bucket_count
   fn_metadata_bytes dense_buckets entry_info st1.
    compile_generate_runtime selectors external_fns internal_fns fallback_fn
      Linear bucket_count fn_metadata_bytes dense_buckets entry_info
      (initial_compile_state "__entry") = ((), st1) /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) ==>
    shape_state st1 /\
    ?entry_blocks segs entry_st.
      (do fallback_lbl <- fresh_label "fallback";
          compile_selector_dispatch_linear
            (MAP (\(sel, lbl, z). (sel, lbl)) selectors) fallback_lbl;
          compile_external_fn_bodies external_fns;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body, fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ty)
       od) (initial_compile_state "__entry") = ((),entry_st) /\
      entry_blocks = all_blocks entry_st /\
      all_blocks st1 = entry_blocks ++ FLAT segs /\ 
      entry_blocks <> [] /\ (HD entry_blocks).bb_label = "__entry" /\
      EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry_blocks)) /\
      EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions)
        entry_blocks /\
      LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_entry_prefix_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `shape_step F jump_label_ok (\st. T) prefix _` >>
  `compile_generate_runtime selectors external_fns internal_fns fallback_fn
     Linear bucket_count fn_metadata_bytes dense_buckets entry_info =
   comp_ignore_bind prefix
     (comp_bind (compile_internal_fn_bodies internal_fns) (\x. comp_return ()))`
    by simp[compile_generate_runtime_def, Abbr `prefix`,
            comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (prefix_result, entry_st)` >>
  Cases_on `prefix_result` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >>
  simp[shape_step_def] >>
  disch_then drule >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  drule runtime_entry_blocks_shape >> strip_tac >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  gvs[] >>
  rename1 `LIST_REL internal_segment_ok _ runtime_segs` >>
  qexists_tac `runtime_segs` >> simp[]
QED

(* Successful packaging exposes the first delimiter prefix independently
   of the contents of the later internal function segments. *)
Theorem package_internal_blocks_entry_prefix:
  !name has_ret_buf rc rest prefix bb suffix entry_blocks functions.
    ~MEM name (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = name /\
    package_internal_blocks ((name, has_ret_buf, rc)::rest)
      (prefix ++ bb::suffix) = SOME (entry_blocks, functions) ==>
    entry_blocks = prefix
Proof
  rpt strip_tac >>
  drule_all split_blocks_at_append_delimiter >> strip_tac >>
  gvs[Once package_internal_blocks_def, AllCaseEqs()]
QED


(* Label-only immutable access boundaries do not constrain instructions. *)
Theorem compile_ptr_load_labels:
  !is_ctor imm loc op s P.
    cs_extends s (SND (compile_ptr_load is_ctor imm loc op s)) /\
    EVERY P (added_labels s (SND (compile_ptr_load is_ctor imm loc op s)))
Proof
  rpt gen_tac >> Cases_on `loc` >> Cases_on `imm` >> Cases_on `is_ctor` >>
  simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
       emit_op_labels, comp_return_labels] >>
  irule comp_bind_labels >> simp[emit_op_labels, comp_return_labels]
QED

Theorem compile_ptr_store_labels:
  !is_ctor imm loc op v s P.
    cs_extends s (SND (compile_ptr_store is_ctor imm loc op v s)) /\
    EVERY P (added_labels s (SND (compile_ptr_store is_ctor imm loc op v s)))
Proof
  rpt gen_tac >> Cases_on `loc` >> Cases_on `imm` >> Cases_on `is_ctor` >>
  simp[contextTheory.compile_ptr_store_def, contextTheory.compile_imm_store_word_def,
       emit_void_labels] >>
  irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels]
QED

Theorem compile_lit_byte_offset_labels:
  !op off s P.
    cs_extends s (SND (compile_lit_byte_offset op off s)) /\
    EVERY P (added_labels s (SND (compile_lit_byte_offset op off s)))
Proof
  rpt gen_tac >> simp[contextTheory.compile_lit_byte_offset_def] >>
  IF_CASES_TAC >> simp[comp_return_labels] >>
  Cases_on `op` >> simp[comp_return_labels, emit_op_labels]
QED

Theorem compile_imm_copy_to_memory_labels:
  !n is_ctor imm src dst off s P.
    cs_extends s (SND (compile_imm_copy_to_memory is_ctor imm src dst n off s)) /\
    EVERY P (added_labels s
      (SND (compile_imm_copy_to_memory is_ctor imm src dst n off s)))
Proof
  Induct >> rpt gen_tac >>
  simp[contextTheory.compile_imm_copy_to_memory_def, comp_return_labels] >>
  irule comp_bind_labels >> simp[compile_lit_byte_offset_labels] >>
  rpt gen_tac >> irule comp_bind_labels >>
  simp[GSYM contextTheory.compile_ptr_load_def, compile_ptr_load_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[compile_lit_byte_offset_labels] >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> simp[emit_void_labels]
QED

Theorem compile_imm_store_word_labels:
  !imm off v s P.
    cs_extends s (SND (compile_imm_store_word imm off v s)) /\
    EVERY P (added_labels s (SND (compile_imm_store_word imm off v s)))
Proof
  Cases >> simp[contextTheory.compile_imm_store_word_def, emit_void_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels]
QED

Theorem compile_imm_store_words_labels:
  !n imm src dst off s P.
    cs_extends s (SND (compile_imm_store_words imm src dst n off s)) /\
    EVERY P (added_labels s (SND (compile_imm_store_words imm src dst n off s)))
Proof
  Induct >> rpt gen_tac >>
  simp[contextTheory.compile_imm_store_words_def, comp_return_labels] >>
  irule comp_bind_labels >> simp[compile_lit_byte_offset_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[compile_lit_byte_offset_labels] >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> simp[compile_imm_store_word_labels]
QED

Theorem compile_alloc_buffer_labels:
  !size s P. cs_extends s (SND (compile_alloc_buffer size s)) /\
    EVERY P (added_labels s (SND (compile_alloc_buffer size s)))
Proof
  rpt gen_tac >> simp[contextTheory.compile_alloc_buffer_def] >>
  irule comp_bind_labels >> simp[emit_op_labels, comp_return_labels]
QED

Theorem compile_zero_words_labels:
  !base n s P. cs_extends s (SND (compile_zero_words base n s)) /\
    EVERY P (added_labels s (SND (compile_zero_words base n s)))
Proof
  Induct_on `n` >> simp[builtinSimpleTheory.compile_zero_words_def,
                         comp_return_labels] >> rpt gen_tac >>
  irule comp_ignore_bind_labels >> simp[] >>
  gen_tac >> irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels]
QED

Theorem compile_select_labels:
  !cmp a b s P. cs_extends s (SND (compile_select cmp a b s)) /\
    EVERY P (added_labels s (SND (compile_select cmp a b s)))
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_select_def, LET_THM,
                     pairTheory.UNCURRY_DEF] >>
  irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_invert_labels:
  !v ty cenv s P. cs_extends s (SND (compile_invert v ty cenv s)) /\
    EVERY P (added_labels s (SND (compile_invert v ty cenv s)))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_invert_def, emit_op_labels]
QED

Theorem compile_env_var_labels:
  !item s P. cs_extends s (SND (compile_env_var item s)) /\
    EVERY P (added_labels s (SND (compile_env_var item s)))
Proof
  rpt gen_tac >> Cases_on `item` >> simp[compile_env_var_def, emit_op_labels] >>
  irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_clamp_labels:
  !val_op ty s P. cs_extends s (SND (compile_clamp val_op ty s)) /\
    EVERY P (added_labels s (SND (compile_clamp val_op ty s)))
Proof
  rpt gen_tac >> simp[compile_clamp_def, LET_THM, pairTheory.UNCURRY] >>
  IF_CASES_TAC >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels] >>
       rpt gen_tac >> BETA_TAC)
QED

Theorem clamp_and_return_labels:
  !res ty s P. cs_extends s (SND (clamp_and_return res ty s)) /\
    EVERY P (added_labels s (SND (clamp_and_return res ty s)))
Proof
  rpt gen_tac >> simp[clamp_and_return_def] >>
  irule comp_ignore_bind_labels >> simp[compile_clamp_labels, comp_return_labels]
QED

Theorem wrap_truncate_labels:
  !res ty s P. cs_extends s (SND (wrap_truncate res ty s)) /\
    EVERY P (added_labels s (SND (wrap_truncate res ty s)))
Proof
  rpt gen_tac >> simp[wrap_truncate_def] >>
  IF_CASES_TAC >> simp[comp_return_labels] >>
  IF_CASES_TAC >> simp[emit_op_labels, comp_return_labels]
QED

Theorem compile_safe_add_labels:
  !x y ty s P. cs_extends s (SND (compile_safe_add x y ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_add x y ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_add_def, LET_THM] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[clamp_and_return_labels] >> IF_CASES_TAC >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, comp_return_labels]
QED

Theorem compile_safe_sub_labels:
  !x y ty s P. cs_extends s (SND (compile_safe_sub x y ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_sub x y ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_sub_def, LET_THM] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[clamp_and_return_labels] >> IF_CASES_TAC >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, comp_return_labels]
QED

Theorem compile_safe_decimal_div_labels:
  !x y divisor ty s P.
    cs_extends s (SND (compile_safe_decimal_div x y divisor ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_decimal_div x y divisor ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_decimal_div_def] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels] >> gen_tac >>
  irule comp_bind_labels >> simp[emit_op_labels, clamp_and_return_labels]
QED

Theorem compile_safe_mod_labels:
  !x y ty s P. cs_extends s (SND (compile_safe_mod x y ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_mod x y ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_mod_def] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels] >> gen_tac >>
  IF_CASES_TAC >> simp[emit_op_labels]
QED

Theorem compile_mul_overflow_check_labels:
  !x y res is_signed bits s P.
    cs_extends s (SND (compile_mul_overflow_check x y res is_signed bits s)) /\
    EVERY P (added_labels s
      (SND (compile_mul_overflow_check x y res is_signed bits s)))
Proof
  rpt gen_tac >> simp[compile_mul_overflow_check_def, LET_THM] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  simp[emit_void_labels] >>
  gen_tac >> IF_CASES_TAC >> simp[comp_return_labels] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >>
       rpt gen_tac >> BETA_TAC)
QED

Theorem compile_safe_mul_labels:
  !x y ty s P. cs_extends s (SND (compile_safe_mul x y ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_mul x y ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_mul_def, LET_THM] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >>
      simp[compile_mul_overflow_check_labels, comp_return_labels]) >>
  gen_tac >> irule comp_bind_labels >> reverse conj_tac
  >- (gen_tac >> IF_CASES_TAC >> simp[emit_op_labels, comp_return_labels]) >>
  rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >>
  simp[clamp_and_return_labels, comp_return_labels]
QED

Theorem compile_safe_div_labels:
  !x y ty s P. cs_extends s (SND (compile_safe_div x y ty s)) /\
    EVERY P (added_labels s (SND (compile_safe_div x y ty s)))
Proof
  rpt gen_tac >> simp[compile_safe_div_def] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels] >> gen_tac >>
  IF_CASES_TAC >> simp[emit_op_labels] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >>
  IF_CASES_TAC
  >- (rpt (irule comp_bind_labels >> simp[emit_op_labels] >>
            rpt gen_tac >> BETA_TAC) >>
      irule comp_ignore_bind_labels >> simp[emit_void_labels, comp_return_labels]) >>
  IF_CASES_TAC >> simp[clamp_and_return_labels, comp_return_labels]
QED

Theorem compile_neg_labels:
  !v ty s P. cs_extends s (SND (compile_neg v ty s)) /\
    EVERY P (added_labels s (SND (compile_neg v ty s)))
Proof
  rpt gen_tac >> simp[compile_neg_def, LET_THM, pairTheory.UNCURRY] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, emit_op_labels]
QED

Theorem compile_builtin_abs_labels:
  !v s P. cs_extends s (SND (compile_builtin_abs v s)) /\
    EVERY P (added_labels s (SND (compile_builtin_abs v s)))
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_builtin_abs_def] >>
  rpt (irule comp_bind_labels >> simp[emit_op_labels] >> rpt gen_tac >> BETA_TAC) >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, compile_select_labels]
QED

Theorem compile_compare_labels:
  !op x y ty s P. cs_extends s (SND (compile_compare op x y ty s)) /\
    EVERY P (added_labels s (SND (compile_compare op x y ty s)))
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[compile_compare_def, LET_THM, emit_op_labels] >>
  Cases_on `is_uint256 ty` >> simp[emit_op_labels] >>
  FIRST [irule comp_ignore_bind_labels >> simp[emit_inst_labels, comp_return_labels],
         irule comp_bind_labels >> simp[emit_op_labels]]
QED

Theorem compile_safe_pow_labels:
  !x y ty base_literal exp_literal s P.
    cs_extends s (SND (compile_safe_pow x y ty base_literal exp_literal s)) /\
    EVERY P (added_labels s
      (SND (compile_safe_pow x y ty base_literal exp_literal s)))
Proof
  rpt gen_tac >> Cases_on `base_literal` >> Cases_on `exp_literal` >>
  simp[compile_safe_pow_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels, comp_return_labels,
            compile_clamp_labels])
QED

Theorem compile_binop_labels:
  !op x y ty base_literal exp_literal s P.
    cs_extends s (SND (compile_binop op x y ty base_literal exp_literal s)) /\
    EVERY P (added_labels s
      (SND (compile_binop op x y ty base_literal exp_literal s)))
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[compile_binop_def, LET_THM, compile_safe_add_labels,
       compile_safe_sub_labels, compile_safe_mul_labels, compile_safe_div_labels,
       compile_safe_mod_labels, compile_safe_decimal_div_labels,
       compile_safe_pow_labels, compile_compare_labels, emit_op_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_inst_labels, emit_void_labels,
            comp_return_labels, wrap_truncate_labels, compile_select_labels,
            compile_safe_decimal_div_labels, compile_safe_div_labels])
QED

Theorem store_multi_results_labels:
  !buf results offset s P.
    cs_extends s (SND (store_multi_results buf results offset s)) /\
    EVERY P (added_labels s (SND (store_multi_results buf results offset s)))
Proof
  Induct_on `results` >> simp[store_multi_results_def, comp_return_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> simp[emit_void_labels]
QED

Theorem compile_store_words_labels:
  !buf vs offset s P.
    cs_extends s (SND (compile_store_words buf vs offset s)) /\
    EVERY P (added_labels s (SND (compile_store_words buf vs offset s)))
Proof
  Induct_on `vs` >> simp[compile_store_words_def, comp_return_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> reverse conj_tac
  >- (gen_tac >> IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels]) >>
  rpt gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >> simp[emit_void_labels]
QED

Theorem compile_store_byte_chunks_labels:
  !data_ptr bs offset s P.
    cs_extends s (SND (compile_store_byte_chunks data_ptr bs offset s)) /\
    EVERY P (added_labels s (SND (compile_store_byte_chunks data_ptr bs offset s)))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> conj_tac
  >- simp[compile_store_byte_chunks_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  simp[compile_store_byte_chunks_def, LET_THM] >>
  irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> simp[emit_void_labels] >>
  first_x_assum (qspecl_then
    [`TAKE 32 (v4::v5 ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (v4::v5 ++ REPLICATE 31 0w))`] mp_tac) >>
  simp[]
QED

Theorem compile_bytelike_literal_labels:
  !bs max_len s P.
    cs_extends s (SND (compile_bytelike_literal bs max_len s)) /\
    EVERY P (added_labels s (SND (compile_bytelike_literal bs max_len s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_bytelike_literal_def, LET_THM] >>
  BETA_TAC >> irule comp_bind_labels >> simp[compile_alloc_buffer_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  conj_tac >- simp[emit_void_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[compile_store_byte_chunks_labels, comp_return_labels]
QED

Theorem compile_blobhash_labels:
  !n s P. cs_extends s (SND (compile_blobhash n s)) /\
    EVERY P (added_labels s (SND (compile_blobhash n s)))
Proof
  simp[builtinMiscTheory.compile_blobhash_def, emit_op_labels]
QED

Theorem compile_addmod_labels:
  !a b c s P. cs_extends s (SND (compile_addmod a b c s)) /\
    EVERY P (added_labels s (SND (compile_addmod a b c s)))
Proof
  rpt gen_tac >> simp[builtinMathTheory.compile_addmod_def] >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, emit_op_labels]
QED

Theorem compile_mulmod_labels:
  !a b c s P. cs_extends s (SND (compile_mulmod a b c s)) /\
    EVERY P (added_labels s (SND (compile_mulmod a b c s)))
Proof
  rpt gen_tac >> simp[builtinMathTheory.compile_mulmod_def] >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, emit_op_labels]
QED

Theorem compile_pow_mod256_labels:
  !x y s P. cs_extends s (SND (compile_pow_mod256 x y s)) /\
    EVERY P (added_labels s (SND (compile_pow_mod256 x y s)))
Proof
  simp[builtinMathTheory.compile_pow_mod256_def, emit_op_labels]
QED

Theorem compile_builtin_calldatasize_labels:
  !s P. cs_extends s (SND (compile_builtin_calldatasize s)) /\
    EVERY P (added_labels s (SND (compile_builtin_calldatasize s)))
Proof
  simp[builtinSimpleTheory.compile_builtin_calldatasize_def, emit_op_labels]
QED

Theorem compile_builtin_len_labels:
  !ic imm ptr loc s P.
    cs_extends s (SND (compile_builtin_len ic imm ptr loc s)) /\
    EVERY P (added_labels s (SND (compile_builtin_len ic imm ptr loc s)))
Proof
  simp[builtinSimpleTheory.compile_builtin_len_def, compile_ptr_load_labels]
QED

Theorem compile_bytestring_hash_labels:
  !ptr s P.
    cs_extends s (SND (compile_bytestring_hash ptr s)) /\
    EVERY P (added_labels s (SND (compile_bytestring_hash ptr s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_bytestring_hash_def] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_floor_labels:
  !v d s P. cs_extends s (SND (compile_floor v d s)) /\
    EVERY P (added_labels s (SND (compile_floor v d s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_floor_def] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> simp[compile_select_labels, emit_op_labels]
QED

Theorem compile_ceil_labels:
  !v d s P. cs_extends s (SND (compile_ceil v d s)) /\
    EVERY P (added_labels s (SND (compile_ceil v d s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ceil_def] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> simp[compile_select_labels, emit_op_labels]
QED

Theorem compile_blockhash_labels:
  !n s P. cs_extends s (SND (compile_blockhash n s)) /\
    EVERY P (added_labels s (SND (compile_blockhash n s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_blockhash_def] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_ignore_bind_labels >> conj_tac >- simp[emit_void_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, emit_op_labels]
QED

Theorem compile_literal_vv_labels:
  !ty l s P. cs_extends s (SND (compile_literal_vv ty l s)) /\
    EVERY P (added_labels s (SND (compile_literal_vv ty l s)))
Proof
  rpt gen_tac >> Cases_on `l`
  >~ [`BoolL b`] >- (Cases_on `b` >>
      simp[compile_literal_vv_def, comp_return_labels])
  >~ [`IntL n`] >- simp[compile_literal_vv_def, comp_return_labels]
  >~ [`DecimalL n`] >- simp[compile_literal_vv_def, comp_return_labels]
  >~ [`StringL str`] >- (simp[compile_literal_vv_def] >>
      irule comp_bind_labels >>
      simp[comp_return_labels, compile_bytelike_literal_labels])
  >> Cases_on `ty` >>
  simp[compile_literal_vv_def, comp_return_labels] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[comp_return_labels] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[comp_return_labels] >>
  irule comp_bind_labels >>
  simp[comp_return_labels, compile_bytelike_literal_labels]
QED

Theorem compile_name_vv_labels:
  !cenv ty id s P. cs_extends s (SND (compile_name_vv cenv ty id s)) /\
    EVERY P (added_labels s (SND (compile_name_vv cenv ty id s)))
Proof
  rpt gen_tac >> Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[compile_name_vv_def, comp_return_labels]
  >- (irule comp_ignore_bind_labels >>
      simp[emit_inst_labels, comp_return_labels])
  >> rename1 `SOME loc` >> Cases_on `loc` >>
  simp[comp_return_labels] >>
  irule comp_ignore_bind_labels >>
  simp[emit_inst_labels, comp_return_labels]
QED

(* Hashing helpers only allocate buffers and emit instructions: none opens a block. *)
Theorem compile_keccak256_bytes_labels:
  !ptr s P. cs_extends s (SND (compile_keccak256_bytes ptr s)) /\
    EVERY P (added_labels s (SND (compile_keccak256_bytes ptr s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_keccak256_bytes_def] >>
  irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_keccak256_bytesm_labels:
  !v m s P. cs_extends s (SND (compile_keccak256_bytesm v m s)) /\
    EVERY P (added_labels s (SND (compile_keccak256_bytesm v m s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_keccak256_bytesm_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_keccak256_word_labels:
  !v s P. cs_extends s (SND (compile_keccak256_word v s)) /\
    EVERY P (added_labels s (SND (compile_keccak256_word v s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_keccak256_word_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_method_id_hash_labels:
  !ty v s P. cs_extends s (SND (compile_method_id_hash ty v s)) /\
    EVERY P (added_labels s (SND (compile_method_id_hash ty v s)))
Proof
  ho_match_mp_tac builtinHashingTheory.compile_method_id_hash_ind >>
  simp[builtinHashingTheory.compile_method_id_hash_def,
       compile_keccak256_bytes_labels, compile_keccak256_bytesm_labels]
QED

Theorem compile_method_id_runtime_labels:
  !ty v b s P. cs_extends s (SND (compile_method_id_runtime ty v b s)) /\
    EVERY P (added_labels s (SND (compile_method_id_runtime ty v b s)))
Proof
  rpt gen_tac >> Cases_on `b` >>
  rewrite_tac[builtinHashingTheory.compile_method_id_runtime_def, COND_CLAUSES] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_method_id_hash_labels, compile_alloc_buffer_labels,
            comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_sha256_bytes_labels:
  !ptr s P. cs_extends s (SND (compile_sha256_bytes ptr s)) /\
    EVERY P (added_labels s (SND (compile_sha256_bytes ptr s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_sha256_bytes_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_sha256_bytesm_labels:
  !v m s P. cs_extends s (SND (compile_sha256_bytesm v m s)) /\
    EVERY P (added_labels s (SND (compile_sha256_bytesm v m s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_sha256_bytesm_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_sha256_word_labels:
  !v s P. cs_extends s (SND (compile_sha256_word v s)) /\
    EVERY P (added_labels s (SND (compile_sha256_word v s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinHashingTheory.compile_sha256_word_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_ecrecover_labels:
  !h v r sig s P. cs_extends s (SND (compile_ecrecover h v r sig s)) /\
    EVERY P (added_labels s (SND (compile_ecrecover h v r sig s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecrecover_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_ecadd_labels:
  !x1 y1 x2 y2 s P. cs_extends s (SND (compile_ecadd x1 y1 x2 y2 s)) /\
    EVERY P (added_labels s (SND (compile_ecadd x1 y1 x2 y2 s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecadd_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_ecmul_labels:
  !x y k s P. cs_extends s (SND (compile_ecmul x y k s)) /\
    EVERY P (added_labels s (SND (compile_ecmul x y k s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecmul_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_assert_slice_bounds_labels:
  !start len src s P.
    cs_extends s (SND (compile_assert_slice_bounds start len src s)) /\
    EVERY P (added_labels s (SND (compile_assert_slice_bounds start len src s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_assert_slice_bounds_def] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[emit_void_labels, emit_op_labels])
QED

Theorem compile_bytestring_src_labels:
  !ptr s P. cs_extends s (SND (compile_bytestring_src ptr s)) /\
    EVERY P (added_labels s (SND (compile_bytestring_src ptr s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_bytestring_src_def] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels])
QED

Theorem compile_slice_data_labels:
  !src_len src_data start len size s P.
    cs_extends s (SND (compile_slice_data src_len src_data start len size s)) /\
    EVERY P (added_labels s
      (SND (compile_slice_data src_len src_data start len size s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_slice_data_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_assert_slice_bounds_labels, compile_alloc_buffer_labels,
            comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_slice_out_buf_labels:
  !size s P. cs_extends s (SND (compile_slice_out_buf size s)) /\
    EVERY P (added_labels s (SND (compile_slice_out_buf size s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_slice_out_buf_def] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, comp_return_labels, emit_op_labels])
QED

Theorem compile_slice_calldata_labels:
  !start len size s P.
    cs_extends s (SND (compile_slice_calldata start len size s)) /\
    EVERY P (added_labels s (SND (compile_slice_calldata start len size s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_slice_calldata_def] >>
  irule comp_bind_labels >> reverse conj_tac
  >- simp[compile_slice_out_buf_labels] >>
  Cases >> rpt gen_tac >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_assert_slice_bounds_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_slice_code_labels:
  !start len size s P.
    cs_extends s (SND (compile_slice_code start len size s)) /\
    EVERY P (added_labels s (SND (compile_slice_code start len size s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_slice_code_def] >>
  irule comp_bind_labels >> reverse conj_tac
  >- simp[compile_slice_out_buf_labels] >>
  Cases >> rpt gen_tac >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_assert_slice_bounds_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_slice_extcode_labels:
  !addr start len buf data s P.
    cs_extends s (SND (compile_slice_extcode addr start len buf data s)) /\
    EVERY P (added_labels s (SND (compile_slice_extcode addr start len buf data s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_slice_extcode_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_assert_slice_bounds_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_extract32_load_labels:
  !src data start s P.
    cs_extends s (SND (compile_extract32_load src data start s)) /\
    EVERY P (added_labels s (SND (compile_extract32_load src data start s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_extract32_load_def] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[compile_assert_slice_bounds_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_as_wei_value_decimal_labels:
  !v scale divisor s P.
    cs_extends s (SND (compile_as_wei_value_decimal v scale divisor s)) /\
    EVERY P (added_labels s (SND (compile_as_wei_value_decimal v scale divisor s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_as_wei_value_int_labels:
  !v scale signed s P.
    cs_extends s (SND (compile_as_wei_value_int v scale signed s)) /\
    EVERY P (added_labels s (SND (compile_as_wei_value_int v scale signed s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_as_wei_value_int_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem load_bytestring_as_word_labels:
  !v opc s P. cs_extends s (SND (load_bytestring_as_word v opc s)) /\
    EVERY P (added_labels s (SND (load_bytestring_as_word v opc s)))
Proof
  rpt gen_tac >> rewrite_tac[load_bytestring_as_word_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels])
QED

Theorem compile_clamp_basetype_labels:
  !v ty s P. cs_extends s (SND (compile_clamp_basetype v ty s)) /\
    EVERY P (added_labels s (SND (compile_clamp_basetype v ty s)))
Proof
  ho_match_mp_tac compile_clamp_basetype_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[compile_clamp_basetype_def, comp_return_labels, clamp_and_return_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, clamp_and_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_int_clamp_labels:
  !is_signed out_b v s P.
    cs_extends s (SND (compile_int_clamp is_signed out_b v s)) /\
    EVERY P (added_labels s (SND (compile_int_clamp is_signed out_b v s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_int_clamp_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_type_convert_labels:
  !v conv s P. cs_extends s (SND (compile_type_convert v conv s)) /\
    EVERY P (added_labels s (SND (compile_type_convert v conv s)))
Proof
  rpt gen_tac >> Cases_on `conv` >>
  simp[compile_type_convert_def, LET_THM, comp_return_labels, emit_op_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac,
              irule uncurry_labels, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, compile_alloc_buffer_labels, load_bytestring_as_word_labels,
            compile_int_clamp_labels, comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_builtin_empty_complex_labels:
  !size lw s P.
    cs_extends s (SND (compile_builtin_empty_complex size lw s)) /\
    EVERY P (added_labels s (SND (compile_builtin_empty_complex size lw s)))
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_builtin_empty_complex_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, compile_alloc_buffer_labels, compile_zero_words_labels,
            comp_return_labels, emit_void_labels])
QED

Theorem compile_keccak256_key_labels:
  !key b s P. cs_extends s (SND (compile_keccak256_key key b s)) /\
    EVERY P (added_labels s (SND (compile_keccak256_key key b s)))
Proof
  rpt gen_tac >> simp[compile_keccak256_key_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_mapping_subscript_labels:
  !base key s P. cs_extends s (SND (compile_mapping_subscript base key s)) /\
    EVERY P (added_labels s (SND (compile_mapping_subscript base key s)))
Proof
  rpt gen_tac >> simp[compile_mapping_subscript_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, compile_alloc_buffer_labels, comp_return_labels,
            emit_void_labels, emit_op_labels])
QED

Theorem compile_tuple_subscript_labels:
  !base offset s P. cs_extends s (SND (compile_tuple_subscript base offset s)) /\
    EVERY P (added_labels s (SND (compile_tuple_subscript base offset s)))
Proof
  simp[compile_tuple_subscript_def, emit_op_labels]
QED

Theorem compile_array_subscript_labels:
  !base idx dyn count scale size signed loader s P.
    (!op st. cs_extends st (SND (loader op st)) /\
      EVERY P (added_labels st (SND (loader op st)))) ==>
    cs_extends s
      (SND (compile_array_subscript base idx dyn count scale size signed loader s)) /\
    EVERY P (added_labels s
      (SND (compile_array_subscript base idx dyn count scale size signed loader s)))
Proof
  rpt gen_tac >> disch_tac >> simp[compile_array_subscript_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_list_membership_in_labels:
  !needle ops s P. cs_extends s (SND (compile_list_membership_in needle ops s)) /\
    EVERY P (added_labels s (SND (compile_list_membership_in needle ops s)))
Proof
  recInduct compile_list_membership_in_ind >> rpt gen_tac >>
  simp[compile_list_membership_in_def, comp_return_labels, emit_op_labels] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  irule comp_bind_labels >> reverse conj_tac >- simp[emit_op_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_bind_labels >> simp[emit_op_labels]
QED

Theorem compile_list_membership_notin_labels:
  !needle ops s P. cs_extends s (SND (compile_list_membership_notin needle ops s)) /\
    EVERY P (added_labels s (SND (compile_list_membership_notin needle ops s)))
Proof
  recInduct compile_list_membership_notin_ind >> rpt gen_tac >>
  simp[compile_list_membership_notin_def, comp_return_labels] >>
  conj_tac >> rpt gen_tac >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[emit_op_labels])
QED

(* Unlike ordinary bind, this rule retains the provenance of a fresh label. *)
Theorem fresh_label_bind_labels:
  !suffix k.
    (!lbl s. isPREFIX "@" lbl ==>
      cs_extends s (SND (k lbl s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (k lbl s)))) ==>
    !s. cs_extends s (SND (comp_bind (fresh_label suffix) k s)) /\
      EVERY (isPREFIX "@")
        (added_labels s (SND (comp_bind (fresh_label suffix) k s)))
Proof
  rpt gen_tac >> disch_tac >> gen_tac >> simp[comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule fresh_label_prefix >> disch_tac >>
  drule fresh_label_labels >>
  disch_then (qspec_then `isPREFIX "@"` strip_assume_tac) >>
  irule cs_extends_labels_trans >> qexists_tac `cs'` >>
  simp[] >> first_x_assum (qspecl_then [`a`, `cs'`] mp_tac) >>
  (impl_tac >- (Cases_on `a` >> gvs[])) >> simp[]
QED

Theorem new_block_action_labels:
  !lbl s P. P lbl ==>
    cs_extends s (SND (new_block lbl s)) /\
    EVERY P (added_labels s (SND (new_block lbl s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `new_block lbl s` >> simp[] >>
  irule new_block_labels >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem fresh_var_action_labels:
  !s P. cs_extends s (SND (fresh_var s)) /\
    EVERY P (added_labels s (SND (fresh_var s)))
Proof
  rpt gen_tac >> Cases_on `fresh_var s` >> simp[] >>
  drule fresh_var_labels >> simp[]
QED


Theorem compile_array_membership_loop_labels:
  !needle arr len size offset loader is_in s.
    (!op st. cs_extends st (SND (loader op st)) /\
      EVERY (isPREFIX "@") (added_labels st (SND (loader op st)))) ==>
    cs_extends s
      (SND (compile_array_membership_loop needle arr len size offset loader is_in s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_array_membership_loop needle arr len size offset loader is_in s)))
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[compile_array_membership_loop_def, LET_THM] >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac,
              disch_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels,
            emit_inst_labels, fresh_var_action_labels])
QED

Theorem compile_var_array_membership_labels:
  !cenv needle arr ty is_in s.
    cs_extends s (SND (compile_var_array_membership cenv needle arr ty is_in s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_var_array_membership cenv needle arr ty is_in s)))
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[compile_var_array_membership_def, LET_THM] >>
  TRY (rename1 `case sz of Fixed _ => _ | Dynamic _ => _` >>
       Cases_on `sz` >> simp[]) >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_inst_labels,
            compile_ptr_load_labels, compile_array_membership_loop_labels])
QED

Theorem compile_uint2str_labels:
  !v digits size s.
    cs_extends s (SND (compile_uint2str v digits size s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_uint2str v digits size s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinStringsTheory.compile_uint2str_def] >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, compile_alloc_buffer_labels, emit_void_labels,
            emit_op_labels, emit_inst_labels, fresh_var_action_labels])
QED

Theorem as_stack_val_labels:
  !ty p s P.
    cs_extends s (SND p) /\ EVERY P (added_labels s (SND p)) ==>
    cs_extends s (SND (as_stack_val ty p)) /\
    EVERY P (added_labels s (SND (as_stack_val ty p)))
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem as_ptr_val_labels:
  !ty loc p s P.
    cs_extends s (SND p) /\ EVERY P (added_labels s (SND p)) ==>
    cs_extends s (SND (as_ptr_val ty loc p)) /\
    EVERY P (added_labels s (SND (as_ptr_val ty loc p)))
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_ptr_val_def]
QED

Theorem compile_word_copy_loop_labels:
  !src dst wc ll sl ic s.
    cs_extends s (SND (compile_word_copy_loop src dst wc ll sl ic s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_word_copy_loop src dst wc ll sl ic s)))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_word_copy_loop_def, LET_THM] >>
  BETA_TAC >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac,
              IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels,
            emit_inst_labels, fresh_var_action_labels,
            compile_ptr_load_labels, compile_ptr_store_labels])
QED

Theorem compile_storage_to_memory_labels:
  !slot buf wc s.
    cs_extends s (SND (compile_storage_to_memory slot buf wc s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_storage_to_memory slot buf wc s)))
Proof
  simp[contextTheory.compile_storage_to_memory_def, compile_word_copy_loop_labels]
QED

Theorem compile_transient_to_memory_labels:
  !slot buf wc s.
    cs_extends s (SND (compile_transient_to_memory slot buf wc s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_transient_to_memory slot buf wc s)))
Proof
  simp[contextTheory.compile_transient_to_memory_def, compile_word_copy_loop_labels]
QED

Theorem compile_code_to_memory_labels:
  !off dst wc s.
    cs_extends s (SND (compile_code_to_memory off dst wc s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_code_to_memory off dst wc s)))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_code_to_memory_def] >>
  IF_CASES_TAC >- simp[comp_return_labels] >>
  irule comp_ignore_bind_labels >>
  simp[compile_word_copy_loop_labels, comp_return_labels]
QED

Theorem compile_ensure_in_memory_labels:
  !ptr loc bytes wc ic imm s.
    cs_extends s (SND (compile_ensure_in_memory ptr loc bytes wc ic imm s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_ensure_in_memory ptr loc bytes wc ic imm s)))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ensure_in_memory_def, comp_return_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_op_labels, emit_void_labels,
            compile_alloc_buffer_labels, compile_storage_to_memory_labels,
            compile_transient_to_memory_labels, compile_imm_copy_to_memory_labels])
QED

Theorem unwrap_value_labels:
  !cenv vv s.
    cs_extends s (SND (unwrap_value cenv vv s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (unwrap_value cenv vv s)))
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def, comp_return_labels] >>
  IF_CASES_TAC >- simp[compile_ptr_load_labels] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[LET_THM, comp_return_labels, compile_ensure_in_memory_labels]
QED

Theorem compile_store_bytestring_labels:
  !v dst s P.
    cs_extends s (SND (compile_store_bytestring v dst s)) /\
    EVERY P (added_labels s (SND (compile_store_bytestring v dst s)))
Proof
  rpt gen_tac >>
  simp[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_copy_memory_labels:
  !dst src sz s P.
    cs_extends s (SND (compile_copy_memory dst src sz s)) /\
    EVERY P (added_labels s (SND (compile_copy_memory dst src sz s)))
Proof
  rpt gen_tac >> Cases_on `sz` >>
  simp[contextTheory.compile_copy_memory_def, comp_return_labels, emit_void_labels]
QED

Theorem compile_copy_memory_dynamic_labels:
  !dst src len s P.
    cs_extends s (SND (compile_copy_memory_dynamic dst src len s)) /\
    EVERY P (added_labels s (SND (compile_copy_memory_dynamic dst src len s)))
Proof
  simp[contextTheory.compile_copy_memory_dynamic_def, emit_void_labels]
QED

Theorem compile_with_byte_offset_labels:
  !base off s P.
    cs_extends s (SND (compile_with_byte_offset base off s)) /\
    EVERY P (added_labels s (SND (compile_with_byte_offset base off s)))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels]
QED

Theorem typed_memory_family_labels:
  (!cenv dst dt src st s.
    cs_extends s (SND (compile_store_memory_typed cenv dst dt src st s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_store_memory_typed cenv dst dt src st s)))) /\
  (!cenv dst src dts sts doff soff s.
    cs_extends s (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)))) /\
  (!cenv dst dt src st count s.
    cs_extends s (SND (compile_copy_sarray_typed cenv dst dt src st count s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_copy_sarray_typed cenv dst dt src st count s)))) /\
  (!cenv dst dt cap src st s.
    cs_extends s (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)))) /\
  (!cenv dst src dfs sfs doff soff s.
    cs_extends s (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s))))
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind >>
  rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume typed_memory_family_labels[fields_nil]:
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[comp_return_labels]
QED
Resume typed_memory_family_labels[fields_mismatch]:
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[comp_return_labels]
QED
Resume typed_memory_family_labels[struct_nil]:
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[comp_return_labels]
QED
Resume typed_memory_family_labels[fields_cons]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_with_byte_offset_labels])
QED
Resume typed_memory_family_labels[sarray]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  IF_CASES_TAC >- simp[compile_copy_memory_labels] >>
  gvs[] >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_inst_labels,
            fresh_var_action_labels])
QED
Resume typed_memory_family_labels[dynarray]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st` >>
  gvs[] >> once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac,
              IF_CASES_TAC >> gvs[]] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_inst_labels, emit_void_labels,
            fresh_var_action_labels, compile_copy_memory_dynamic_labels])
QED
Resume typed_memory_family_labels[struct_cons]:
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP sfs name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >>
  gvs[AllCaseEqs()] >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[compile_with_byte_offset_labels])
QED
Resume typed_memory_family_labels[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> simp[] >>
      irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      simp[compile_store_bytestring_labels]) >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st` >>
      TRY (rename1 `compile_store_memory_typed cenv dst (ArrayT dt db) src (ArrayT st sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      simp[LET_THM, compile_copy_memory_labels] >> metis_tac[]) >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> simp[emit_void_labels]
QED
Finalise typed_memory_family_labels

Theorem compile_store_memory_labels:
  !cenv src dst dt st s.
    cs_extends s (SND (compile_store_memory cenv src dst dt st s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_store_memory cenv src dst dt st s)))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_store_memory_def] >>
  rpt IF_CASES_TAC >>
  simp[emit_void_labels, compile_store_bytestring_labels,
       typed_memory_family_labels, compile_copy_memory_labels]
QED

Theorem compile_abi_encode_static_labels:
  !dst src s P.
    cs_extends s (SND (compile_abi_encode_static dst src s)) /\
    EVERY P (added_labels s (SND (compile_abi_encode_static dst src s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_encode_static_def] >>
  BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_encode_static_info_labels:
  !dst src info s P.
    cs_extends s (SND (compile_abi_encode_static_info dst src info s)) /\
    EVERY P (added_labels s (SND (compile_abi_encode_static_info dst src info s)))
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abiEncoderTheory.compile_abi_encode_static_info_def,
       compile_abi_encode_static_labels, comp_return_labels, emit_void_labels] >>
  irule comp_ignore_bind_labels >> simp[emit_void_labels, comp_return_labels]
QED

Theorem compile_abi_zero_pad_labels:
  !ptr len count s P.
    cs_extends s (SND (compile_abi_zero_pad ptr len count s)) /\
    EVERY P (added_labels s (SND (compile_abi_zero_pad ptr len count s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_zero_pad_def] >>
  BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_int_clamp_labels:
  !v bits signed s P.
    cs_extends s (SND (compile_abi_int_clamp v bits signed s)) /\
    EVERY P (added_labels s (SND (compile_abi_int_clamp v bits signed s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_int_clamp_def, LET_THM] >>
  BETA_TAC >> IF_CASES_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_bytes_clamp_labels:
  !v m s P.
    cs_extends s (SND (compile_abi_bytes_clamp v m s)) /\
    EVERY P (added_labels s (SND (compile_abi_bytes_clamp v m s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_bytes_clamp_def, LET_THM] >>
  BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_clamp_basetype_labels:
  !v clamp s P.
    cs_extends s (SND (compile_abi_clamp_basetype v clamp s)) /\
    EVERY P (added_labels s (SND (compile_abi_clamp_basetype v clamp s)))
Proof
  rpt gen_tac >> Cases_on `clamp` >>
  simp[abiEncoderTheory.compile_abi_clamp_basetype_def, comp_return_labels,
       compile_abi_int_clamp_labels, compile_abi_bytes_clamp_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_decode_static_labels:
  !src dst opc clamp s P.
    (!v t. cs_extends t (SND (clamp v t)) /\
           EVERY P (added_labels t (SND (clamp v t)))) ==>
    cs_extends s (SND (compile_abi_decode_static src dst opc clamp s)) /\
    EVERY P (added_labels s (SND (compile_abi_decode_static src dst opc clamp s)))
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[abiEncoderTheory.compile_abi_decode_static_def] >>
  BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_dec_addr_labels:
  !bop pos s P.
    cs_extends s (SND (compile_abi_dec_addr bop pos s)) /\
    EVERY P (added_labels s (SND (compile_abi_dec_addr bop pos s)))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_abi_dec_addr_def] >>
  IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels]
QED

Theorem compile_abi_decode_range_check_labels:
  !sop eop hi s P.
    cs_extends s (SND (compile_abi_decode_range_check sop eop hi s)) /\
    EVERY P (added_labels s (SND (compile_abi_decode_range_check sop eop hi s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_decode_range_check_def] >>
  BETA_TAC >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels])
QED

Theorem compile_getelemptr_abi_labels:
  !src dyn off opc bop hi s P.
    cs_extends s (SND (compile_getelemptr_abi src dyn off opc bop hi s)) /\
    EVERY P (added_labels s (SND (compile_getelemptr_abi src dyn off opc bop hi s)))
Proof
  rpt gen_tac >> Cases_on `hi = Lit 0w` >> Cases_on `dyn` >>
  simp[abiEncoderTheory.compile_getelemptr_abi_def] >> BETA_TAC >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels,
            compile_abi_dec_addr_labels])
QED

Theorem compile_abi_decode_dyn_elem_ptr_labels:
  !opc bop elem src hi sz s P.
    cs_extends s (SND (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz s)) /\
    EVERY P (added_labels s (SND (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def] >>
  BETA_TAC >> Cases_on `hi = Lit 0w` >> simp[] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels,
            compile_abi_dec_addr_labels, compile_abi_decode_range_check_labels])
QED

Theorem compile_abi_encode_dyn_static_loop_labels:
  !dst src info asz msz len s.
    cs_extends s (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len s)))
Proof
  rpt gen_tac >> rewrite_tac[abiEncoderTheory.compile_abi_encode_dyn_static_loop_def] >>
  BETA_TAC >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_op_labels, emit_void_labels,
            emit_inst_labels, fresh_var_action_labels, compile_alloc_buffer_labels,
            compile_abi_encode_static_info_labels])
QED

Theorem compile_extcodesize_check_labels:
  !addr s P.
    cs_extends s (SND (compile_extcodesize_check addr s)) /\
    EVERY P (added_labels s (SND (compile_extcodesize_check addr s)))
Proof
  rpt gen_tac >> rewrite_tac[exprLoweringTheory.compile_extcodesize_check_def] >>
  BETA_TAC >> irule comp_bind_labels >> simp[emit_op_labels, emit_void_labels]
QED

Theorem compile_return_value_decode_labels:
  !minsz maxsz s P.
    cs_extends s (SND (compile_return_value_decode minsz maxsz s)) /\
    EVERY P (added_labels s (SND (compile_return_value_decode minsz maxsz s)))
Proof
  rpt gen_tac >> rewrite_tac[exprLoweringTheory.compile_return_value_decode_def] >>
  BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels, compile_select_labels])
QED

Theorem compile_materialize_vv_labels:
  !cenv ty vv s.
    cs_extends s (SND (compile_materialize_vv cenv ty vv s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_materialize_vv cenv ty vv s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_materialize_vv_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, compile_alloc_buffer_labels,
            unwrap_value_labels, compile_store_memory_labels])
QED

Theorem compile_snapshot_vv_labels:
  !cenv copy vv s.
    cs_extends s (SND (compile_snapshot_vv cenv copy vv s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_snapshot_vv cenv copy vv s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_snapshot_vv_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, unwrap_value_labels,
            compile_materialize_vv_labels])
QED

Theorem compile_store_abi_tuple_labels:
  !cenv buf off elems s P.
    cs_extends s (SND (compile_store_abi_tuple cenv buf off elems s)) /\
    EVERY P (added_labels s (SND (compile_store_abi_tuple cenv buf off elems s)))
Proof
  ho_match_mp_tac compile_store_abi_tuple_ind >> rpt conj_tac
  >- simp[compile_store_abi_tuple_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> rewrite_tac[compile_store_abi_tuple_def] >>
  rpt gen_tac >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels, compile_copy_memory_labels])
QED

Theorem compile_abi_encode_child_branches_labels:
  (~dyn ==> !dst s.
    cs_extends s (SND (compile_abi_encode_to_buf dst child_ptr info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst child_ptr info s)))) ==>
  (dyn ==> !dst s.
    cs_extends s (SND (compile_abi_encode_to_buf dst child_ptr info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst child_ptr info s)))) ==>
  !dst off dynptr s.
    cs_extends s (SND (compile_abi_encode_child dst child_ptr info dyn off dynptr s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_child dst child_ptr info dyn off dynptr s)))
Proof
  ntac 2 disch_tac >> Cases_on `dyn` >> gvs[] >> rpt gen_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >> simp[] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_encode_child_body_labels:
  (!dst. ~dyn ==> !s.
    cs_extends s (SND (compile_abi_encode_to_buf dst child_ptr info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst child_ptr info s)))) ==>
  (!dst. dyn ==> !s.
    cs_extends s (SND (compile_abi_encode_to_buf dst child_ptr info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst child_ptr info s)))) ==>
  !dst off dp s.
    cs_extends s (SND
      (do sl <- emit_op ADD [dst; Lit (n2w off)];
          if ~dyn then compile_abi_encode_to_buf sl child_ptr info
          else do d <- emit_op MLOAD [dp];
                  cd <- emit_op ADD [dst; d];
                  n <- compile_abi_encode_to_buf cd child_ptr info;
                  emit_void MSTORE [sl; d];
                  nd <- emit_op ADD [d; n];
                  emit_void MSTORE [dp; nd]; comp_return n od
       od s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND
      (do sl <- emit_op ADD [dst; Lit (n2w off)];
          if ~dyn then compile_abi_encode_to_buf sl child_ptr info
          else do d <- emit_op MLOAD [dp];
                  cd <- emit_op ADD [dst; d];
                  n <- compile_abi_encode_to_buf cd child_ptr info;
                  emit_void MSTORE [sl; d];
                  nd <- emit_op ADD [d; n];
                  emit_void MSTORE [dp; nd]; comp_return n od
       od s)))
Proof
  ntac 2 disch_tac >> Cases_on `dyn` >> gvs[] >> rpt gen_tac >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels])
QED

Theorem compile_abi_encode_complex_step_labels:
  (!cp s.
    cs_extends s (SND (compile_abi_encode_child dst cp info dyn hoff dp s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_child dst cp info dyn hoff dp s)))) ==>
  (!s.
    cs_extends s (SND (compile_abi_encode_complex_elems dst src elems (soff + msz) (hoff + asz) dp s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_complex_elems dst src elems (soff + msz) (hoff + asz) dp s)))) ==>
  !s.
    cs_extends s (SND
      (do es <- emit_op ADD [src; Lit (n2w soff)];
          compile_abi_encode_child dst es info dyn hoff dp;
          compile_abi_encode_complex_elems dst src elems (msz + soff) (asz + hoff) dp
       od s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND
      (do es <- emit_op ADD [src; Lit (n2w soff)];
          compile_abi_encode_child dst es info dyn hoff dp;
          compile_abi_encode_complex_elems dst src elems (msz + soff) (asz + hoff) dp
       od s)))
Proof
  ntac 2 disch_tac >> rpt gen_tac >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels]) >>
  last_x_assum (qspec_then `s` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem compile_abi_encode_labels:
  (!dst cp info dyn off dp s.
    cs_extends s (SND (compile_abi_encode_child dst cp info dyn off dp s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_child dst cp info dyn off dp s)))) /\
  (!dst src info s.
    cs_extends s (SND (compile_abi_encode_to_buf dst src info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst src info s)))) /\
  (!dst src elems soff hoff dp s.
    cs_extends s (SND (compile_abi_encode_complex_elems dst src elems soff hoff dp s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_complex_elems dst src elems soff hoff dp s)))) /\
  (!dst src info asz msz len s.
    cs_extends s (SND (compile_abi_encode_dyn_loop dst src info asz msz len s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_dyn_loop dst src info asz msz len s))))
Proof
  ho_match_mp_tac abiEncoderTheory.compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty_tuple"
  >- suspend "tuple"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume compile_abi_encode_labels[child]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  irule compile_abi_encode_child_body_labels >> simp[]
QED
Resume compile_abi_encode_labels[word]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[compile_abi_encode_static_labels]
QED
Resume compile_abi_encode_labels[bytes]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels, compile_abi_zero_pad_labels])
QED
Resume compile_abi_encode_labels[copy]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[LET_THM] >> irule comp_ignore_bind_labels >>
  simp[emit_void_labels, comp_return_labels]
QED

Resume compile_abi_encode_labels[array]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels, compile_alloc_buffer_labels, LET_THM]) >>
  IF_CASES_TAC >> gvs[]
  >- simp[compile_abi_encode_dyn_static_loop_labels] >>
  first_x_assum irule
QED

Resume compile_abi_encode_labels[empty_tuple]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[comp_return_labels]
QED
Resume compile_abi_encode_labels[tuple]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[LET_THM] >> IF_CASES_TAC >> gvs[] >> rpt gen_tac >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_op_labels, emit_void_labels, compile_alloc_buffer_labels]) >>
  first_x_assum irule
QED
Resume compile_abi_encode_labels[nil]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  simp[comp_return_labels]
QED
Resume compile_abi_encode_labels[cons]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >>
  gen_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule compile_abi_encode_complex_step_labels >> simp[arithmeticTheory.ADD_COMM]
QED
Resume compile_abi_encode_labels[loop]:
  rpt gen_tac >> strip_tac >>
  `!dst src s. cs_extends s (SND (compile_abi_encode_to_buf dst src info s)) /\
     EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_to_buf dst src info s)))`
    by (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!i_ptr i_ptr_alloc dyn_ptr dyn_ptr_alloc dst src. _` kall_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_encode_child_def] >> BETA_TAC >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_op_labels, emit_void_labels,
            emit_inst_labels, compile_alloc_buffer_labels])
QED
Finalise compile_abi_encode_labels

(* Walk a decoder body: binds, guards, and the straight-line helpers. *)
val dec_labels_tac =
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, IF_CASES_TAC] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_op_labels, emit_void_labels,
            compile_abi_dec_addr_labels, compile_abi_decode_range_check_labels,
            compile_alloc_buffer_labels]);

Theorem compile_abi_decode_labels:
  (!dst src lop bop hi info s.
    cs_extends s (SND (compile_abi_decode_to_buf dst src lop bop hi info s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_decode_to_buf dst src lop bop hi info s)))) /\
  (!dst src lop bop hi elems ao vo s.
    cs_extends s (SND (compile_abi_decode_complex_elems dst src lop bop hi elems ao vo s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_decode_complex_elems dst src lop bop hi elems ao vo s)))) /\
  (!dst src lop bop hi info asz msz ip cnt s.
    cs_extends s (SND (compile_abi_decode_dyn_loop dst src lop bop hi info asz msz ip cnt s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_decode_dyn_loop dst src lop bop hi info asz msz ip cnt s))))
Proof
  ho_match_mp_tac abiEncoderTheory.compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "tuple"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume compile_abi_decode_labels[word]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  irule comp_bind_labels >> conj_tac
  >- (rpt gen_tac >> BETA_TAC >> irule compile_abi_decode_static_labels >>
      simp[compile_abi_clamp_basetype_labels]) >>
  simp[compile_abi_dec_addr_labels]
QED
Resume compile_abi_decode_labels[nil]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  simp[comp_return_labels]
QED
Resume compile_abi_decode_labels[cons]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  simp[LET_THM] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_getelemptr_abi_labels, emit_op_labels]) >>
  first_x_assum (qspec_then `dec_info_needs_offset info` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED
Resume compile_abi_decode_labels[bytes]:
  rpt gen_tac >> once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  dec_labels_tac >> Cases_on `lop` >> simp[emit_void_labels]
QED
Resume compile_abi_decode_labels[tuple]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  simp[LET_THM] >> IF_CASES_TAC >> gvs[] >> rpt gen_tac >>
  dec_labels_tac >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume compile_abi_decode_labels[array]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >> BETA_TAC >>
  dec_labels_tac >> gvs[] >>
  TRY (Cases_on `lop` >> simp[emit_void_labels] >> NO_TAC) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED
Resume compile_abi_decode_labels[loop]:
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `dec_info_needs_offset info` mp_tac) >> simp[] >>
  disch_tac >>
  once_rewrite_tac[abiEncoderTheory.compile_abi_decode_to_buf_def] >>
  simp[LET_THM] >> BETA_TAC >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, comp_return_labels, emit_op_labels, emit_void_labels, emit_inst_labels,
            compile_abi_dec_addr_labels]) >>
  IF_CASES_TAC >> simp[compile_abi_decode_dyn_elem_ptr_labels, comp_return_labels]
QED
Finalise compile_abi_decode_labels

Theorem compile_struct_lit_labels:
  !cfn cenv ty fields buf off s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_struct_lit cfn cenv ty fields buf off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_struct_lit cfn cenv ty fields buf off s)))
Proof
  Induct_on `fields`
  >- simp[compile_struct_lit_def, comp_return_labels] >>
  rpt gen_tac >> Cases_on `h` >> disch_tac >>
  once_rewrite_tac[compile_struct_lit_def] >> simp[LET_THM] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, unwrap_value_labels, compile_store_memory_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_make_array_elems_labels:
  !cfn cenv es elem_ty elem_size has_lw buf off s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_make_array_elems cfn cenv es elem_ty elem_size has_lw buf off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_make_array_elems cfn cenv es elem_ty elem_size has_lw buf off s)))
Proof
  Induct_on `es`
  >- simp[compile_make_array_elems_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >>
  once_rewrite_tac[compile_make_array_elems_def] >> simp[LET_THM] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, unwrap_value_labels, compile_store_memory_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_make_array_labels:
  !cfn cenv es elem_ty elem_size has_lw buf s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_make_array cfn cenv es elem_ty elem_size has_lw buf s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_make_array cfn cenv es elem_ty elem_size has_lw buf s)))
Proof
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_make_array_def] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (Cases_on `has_lw` >> simp[emit_void_labels, comp_return_labels]) >>
  simp[compile_make_array_elems_labels]
QED

Theorem lower_value_labels:
  !cfn cenv ty e s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (lower_value cfn cenv ty e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (lower_value cfn cenv ty e s)))
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[lower_value_def] >>
  irule comp_bind_labels >> simp[unwrap_value_labels]
QED

Theorem compile_multi_exprs_labels:
  !cfn cenv es s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_multi_exprs cfn cenv es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_multi_exprs cfn cenv es s)))
Proof
  Induct_on `es`
  >- simp[compile_multi_exprs_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_multi_exprs_def] >>
  simp[LET_THM] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, lower_value_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_abi_encode_args_labels:
  !cfn cenv es s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_abi_encode_args cfn cenv es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_abi_encode_args cfn cenv es s)))
Proof
  Induct_on `es`
  >- simp[compile_abi_encode_args_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_abi_encode_args_def] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       TRY IF_CASES_TAC >>
       simp[comp_return_labels, compile_materialize_vv_labels, unwrap_value_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_concat_labels:
  !cfn cenv es data_ptr infos offset_op s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_concat cfn cenv es data_ptr infos offset_op s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_concat cfn cenv es data_ptr infos offset_op s)))
Proof
  recInduct compile_concat_ind >> rpt conj_tac
  >- (rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_concat_def] >> simp[comp_return_labels])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
      Cases_on `is_bs` >> gvs[] >>
      once_rewrite_tac[compile_concat_def] >> simp[LET_THM] >> BETA_TAC >>
      rpt (FIRST [irule comp_bind_labels >> conj_tac,
                  irule comp_ignore_bind_labels >> conj_tac] >>
           rpt gen_tac >> BETA_TAC >>
           simp[comp_return_labels, emit_op_labels, emit_void_labels, lower_value_labels]) >>
      first_x_assum irule >> simp[]) >>
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_concat_def] >> simp[comp_return_labels]
QED

Theorem compile_attribute_labels:
  !cfn cenv ret_ty ty base_e field s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_attribute cfn cenv ret_ty ty base_e field s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_attribute cfn cenv ret_ty ty base_e field s)))
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[compile_attribute_def] >>
  BETA_TAC >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[LET_THM, emit_op_labels, comp_return_labels])
QED

Theorem compile_acc_labels:
  !cfn cenv addr_e item s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_acc cfn cenv addr_e item s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_acc cfn cenv addr_e item s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `item` >>
  once_rewrite_tac[compile_acc_def] >> simp[lower_value_labels] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, emit_op_labels, emit_inst_labels]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_multi_vvs_labels:
  !cfn cenv es s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_multi_vvs cfn cenv es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_multi_vvs cfn cenv es s)))
Proof
  Induct_on `es`
  >- simp[compile_multi_vvs_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_multi_vvs_def] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_make_tuple_labels:
  !cfn cenv es buf off s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_make_tuple cfn cenv es buf off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_make_tuple cfn cenv es buf off s)))
Proof
  Induct_on `es`
  >- simp[compile_make_tuple_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >>
  once_rewrite_tac[compile_make_tuple_def] >> simp[LET_THM] >> BETA_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, unwrap_value_labels, compile_store_memory_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_subscript_labels:
  !cfn cenv ret_ty ty base_e idx_e s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e s)))
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[compile_subscript_def] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> simp[LET_THM] >>
  Cases_on `place_type cenv base_e`
  >- (simp[] >>
      rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
           simp[comp_return_labels, lower_value_labels, compile_mapping_subscript_labels]) >>
      IF_CASES_TAC >> simp[compile_keccak256_key_labels, comp_return_labels]) >>
  rename1 `place_type cenv base_e = ValPT bt` >> Cases_on `bt` >> simp[LET_THM] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, lower_value_labels, compile_tuple_subscript_labels,
            compile_array_subscript_labels, compile_ptr_load_labels])
QED

Theorem compile_get_target_ptr_labels:
  !cfn bt cenv s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_get_target_ptr cfn cenv bt s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_get_target_ptr cfn cenv bt s)))
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac >> disch_tac >>
  once_rewrite_tac[compile_get_target_ptr_def]
  >- (rename1 `FLOOKUP cenv.ce_vars id` >>
      Cases_on `FLOOKUP cenv.ce_vars id` >> simp[comp_return_labels] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME loc` >>
      Cases_on `loc` >> simp[comp_return_labels])
  >- (simp[LET_THM] >>
      rename1 `FLOOKUP cenv.ce_module_vars id` >>
      Cases_on `FLOOKUP cenv.ce_module_vars id` >> simp[comp_return_labels] >>
      rename1 `FLOOKUP cenv.ce_module_vars id = SOME loc` >>
      Cases_on `loc` >> simp[comp_return_labels])
  >- (irule comp_bind_labels >> reverse conj_tac
      >- (first_x_assum irule >> simp[] ) >>
      rpt gen_tac >> simp[LET_THM] >>
      Cases_on `SND (SND x)` >> simp[LET_THM]
      >- (rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
               simp[lower_value_labels, compile_array_subscript_labels,
                    compile_ptr_load_labels, comp_return_labels])) >>
      rename1 `SND (SND x) = SOME pt` >> Cases_on `pt` >> simp[LET_THM] >>
      rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
           simp[lower_value_labels, compile_array_subscript_labels,
                compile_ptr_load_labels, compile_mapping_subscript_labels,
                comp_return_labels]) >>
      IF_CASES_TAC >> simp[compile_keccak256_key_labels, comp_return_labels]) >>
  irule comp_bind_labels >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  rpt gen_tac >> simp[LET_THM] >>
  irule comp_bind_labels >> simp[emit_op_labels, comp_return_labels]
QED

Theorem compile_dynarray_pop_labels:
  !base_op ws es is_ctor imm loc s.
    cs_extends s (SND (compile_dynarray_pop base_op ws es is_ctor imm loc s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_dynarray_pop base_op ws es is_ctor imm loc s)))
Proof
  rpt gen_tac >> simp[compile_dynarray_pop_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[emit_op_labels, emit_void_labels, compile_ptr_load_labels,
            compile_ptr_store_labels])
QED

Theorem compile_default_return_path_labels:
  !cenv return_type default_ty buf_op result_op default_op addr_op skip_check
    min_return_size max_return_size ret_dec_info s.
    cs_extends s (SND (compile_default_return_path cenv return_type default_ty
      buf_op result_op default_op addr_op skip_check min_return_size
      max_return_size ret_dec_info s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_default_return_path cenv return_type default_ty
        buf_op result_op default_op addr_op skip_check min_return_size
        max_return_size ret_dec_info s)))
Proof
  rpt gen_tac >> simp[compile_default_return_path_def, LET_THM] >>
  rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
              irule comp_bind_labels >> conj_tac >> rpt gen_tac,
              irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
       BETA_TAC >> simp[emit_op_labels, emit_inst_labels,
         compile_store_memory_labels, compile_return_value_decode_labels,
         compile_abi_decode_labels, comp_return_labels])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[]) >>
  IF_CASES_TAC >> simp[comp_return_labels, compile_extcodesize_check_labels]
QED

Theorem compile_stage_intcall_args_labels:
  !cenv vals flags tys s.
    cs_extends s (SND (compile_stage_intcall_args cenv vals flags tys s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_stage_intcall_args cenv vals flags tys s)))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- simp[compile_stage_intcall_args_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> gen_tac >>
  once_rewrite_tac[compile_stage_intcall_args_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[unwrap_value_labels, compile_alloc_buffer_labels, comp_return_labels]) >>
  IF_CASES_TAC >> simp[emit_void_labels] >>
  IF_CASES_TAC >> simp[emit_void_labels] >>
  simp[compile_store_memory_labels, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, pairTheory.ELIM_UNCURRY, compile_store_bytestring_labels]
QED

Theorem ext_call_gas_opt_labels:
  !gas_opt a s.
    cs_extends a s /\ EVERY (isPREFIX "@") (added_labels a s) ==>
    cs_extends a (SND (case gas_opt of NONE => emit_op GAS [] s | SOME g => (g,s))) /\
    EVERY (isPREFIX "@")
      (added_labels a (SND (case gas_opt of NONE => emit_op GAS [] s | SOME g => (g,s))))
Proof
  Cases >> rpt gen_tac >> disch_tac >> simp[] >>
  irule cs_extends_labels_trans >> qexists_tac `s` >> simp[emit_op_labels]
QED

Theorem compile_ext_call_kwarg_labels:
  !cfn cenv rt k e s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_ext_call_kwarg cfn cenv rt k e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_ext_call_kwarg cfn cenv rt k e s)))
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[LET_THM] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[compile_materialize_vv_labels, lower_value_labels, comp_return_labels])
QED

Theorem compile_ext_call_kwargs_labels:
  !ks es cfn cenv rt s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_ext_call_kwargs cfn cenv rt ks es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_ext_call_kwargs cfn cenv rt ks es s)))
Proof
  Induct_on `ks` >> Cases_on `es` >> rpt gen_tac >> disch_tac >>
  once_rewrite_tac[compile_ext_call_kwargs_def] >> simp[comp_return_labels] >>
  irule comp_bind_labels >> reverse conj_tac >- simp[compile_ext_call_kwarg_labels] >>
  rpt gen_tac >> PairCases_on `x` >> simp[] >>
  irule comp_bind_labels >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  rpt gen_tac >> PairCases_on `x` >> simp[comp_return_labels]
QED

Theorem compile_extcall_store_values_labels:
  !cenv vals buf off s.
    cs_extends s (SND (compile_extcall_store_values cenv vals buf off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_extcall_store_values cenv vals buf off s)))
Proof
  Induct_on `vals`
  >- simp[compile_extcall_store_values_def, comp_return_labels] >>
  rpt gen_tac >> PairCases_on `h` >>
  once_rewrite_tac[compile_extcall_store_values_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[emit_op_labels, unwrap_value_labels]) >>
  IF_CASES_TAC >> simp[emit_void_labels] >>
  IF_CASES_TAC >> simp[emit_void_labels, compile_store_bytestring_labels]
QED

Theorem compile_extcall_store_args_labels:
  !cfn cenv es tys buf off s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_extcall_store_args cfn cenv es tys buf off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_extcall_store_args cfn cenv es tys buf off s)))
Proof
  Induct_on `es`
  >- simp[compile_extcall_store_args_def, comp_return_labels] >>
  rpt gen_tac >> disch_tac >> Cases_on `tys` >>
  once_rewrite_tac[compile_extcall_store_args_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[lower_value_labels, emit_void_labels]) >>
  IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels, emit_void_labels] >>
  IF_CASES_TAC >> simp[compile_store_bytestring_labels, emit_void_labels]
QED

Theorem compile_external_call_kwargs_labels:
  !cenv addr_op arg_vals arg_types args_mem_size args_abi_size method_id_val
    return_abi_size min_return_size ret_mem_bytes use_staticcall call_value gas_op
    skip_check has_default default_op return_type default_ty args_enc_info ret_dec_info s.
    cs_extends s (SND (compile_external_call_kwargs cenv addr_op arg_vals arg_types
      args_mem_size args_abi_size method_id_val return_abi_size min_return_size
      ret_mem_bytes use_staticcall call_value gas_op skip_check has_default default_op
      return_type default_ty args_enc_info ret_dec_info s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_external_call_kwargs cenv addr_op arg_vals arg_types
        args_mem_size args_abi_size method_id_val return_abi_size min_return_size
        ret_mem_bytes use_staticcall call_value gas_op skip_check has_default default_op
        return_type default_ty args_enc_info ret_dec_info s)))
Proof
  rpt gen_tac >> simp[compile_external_call_kwargs_def, LET_THM] >>
  rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
              irule comp_bind_labels >> conj_tac >> rpt gen_tac,
              irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
       BETA_TAC >> simp[LET_THM, emit_op_labels, emit_inst_labels, emit_void_labels,
         compile_alloc_buffer_labels, compile_extcall_store_values_labels,
         compile_abi_encode_labels, compile_abi_decode_labels,
         compile_return_value_decode_labels, comp_return_labels])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[])
  >~ [`new_block`] >- (irule new_block_action_labels >> simp[]) >>
  IF_CASES_TAC >> simp[comp_return_labels, emit_op_labels,
                       compile_extcodesize_check_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[LET_THM, compile_alloc_buffer_labels,
         compile_extcall_store_values_labels, emit_op_labels,
         compile_abi_encode_labels, comp_return_labels]) >>
  IF_CASES_TAC >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[compile_alloc_buffer_labels,
         compile_default_return_path_labels, compile_return_value_decode_labels,
         compile_abi_decode_labels, comp_return_labels])
QED

Theorem compile_msg_data_to_memory_labels:
  !s. cs_extends s (SND (compile_msg_data_to_memory s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_msg_data_to_memory s)))
Proof
  gen_tac >> simp[builtinSystemTheory.compile_msg_data_to_memory_def, compile_alloc_dynamic_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[emit_op_labels, emit_void_labels, comp_return_labels])
QED

Theorem compile_raw_call_outbuf_labels:
  !n s. cs_extends s (SND (compile_raw_call_outbuf n s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_raw_call_outbuf n s)))
Proof
  rpt gen_tac >> simp[builtinSystemTheory.compile_raw_call_outbuf_def] >> IF_CASES_TAC >> simp[LET_THM] >>
  rpt (irule comp_bind_labels >> conj_tac >> rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, emit_op_labels, comp_return_labels])
QED

Theorem compile_raw_call_finish_labels:
  !addr dp dl gas value call_ty n rof out_val out_ptr s.
    cs_extends s (SND (compile_raw_call_finish addr dp dl gas value call_ty n rof out_val out_ptr s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_raw_call_finish addr dp dl gas value call_ty n rof out_val out_ptr s)))
Proof
  rpt gen_tac >> simp[builtinSystemTheory.compile_raw_call_finish_def, LET_THM] >>
  irule comp_bind_labels >> reverse conj_tac
  >- (Cases_on `call_ty` >> simp[emit_op_labels]) >>
  rpt gen_tac >> BETA_TAC >> Cases_on `rof` >> Cases_on `n > 0` >> simp[LET_THM, comp_return_labels] >>
  rpt (FIRST [irule fresh_label_bind_labels >> rpt gen_tac >> disch_tac,
              irule comp_bind_labels >> conj_tac >> rpt gen_tac,
              irule comp_ignore_bind_labels >> conj_tac >> rpt gen_tac] >>
       BETA_TAC >> simp[emit_op_labels, emit_void_labels, emit_inst_labels,
         compile_alloc_buffer_labels, compile_select_labels, comp_return_labels]) >>
  irule new_block_action_labels >> simp[]
QED

Theorem compile_raw_call_target_labels:
  !cfn cenv ret_ty ty rcf args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty
      (RawCallTarget rcf) args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty
      (RawCallTarget rcf) args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `args` >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM] 
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  Cases_on `t` >> simp[LET_THM]
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >>
       rpt gen_tac >> BETA_TAC >>
       simp[lower_value_labels, emit_op_labels, compile_raw_call_outbuf_labels,
            compile_raw_call_finish_labels, compile_ext_call_kwargs_labels]) >>
  ho_match_mp_tac application_labels >> conj_tac
  >- (irule compile_ext_call_kwargs_labels >> simp[]) >>
  map_every qx_gen_tac [`x`, `t`] >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (Cases_on `x1`
      >- simp[emit_op_labels] >>
      simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt gen_tac >> ho_match_mp_tac application_labels >> conj_tac
  >- simp[compile_raw_call_outbuf_labels] >>
  map_every qx_gen_tac [`y`, `u`] >> PairCases_on `y` >> simp[] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[compile_raw_call_finish_labels] >>
  rpt gen_tac >> IF_CASES_TAC >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_raw_call_calldata_labels:
  !cfn cenv ret_ty ty rcf args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty
      (RawCallCalldataTarget rcf) args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty
      (RawCallCalldataTarget rcf) args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `args` >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM]
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule lower_value_labels >> simp[]) >>
  rpt gen_tac >> ho_match_mp_tac application_labels >> conj_tac
  >- (irule compile_ext_call_kwargs_labels >> simp[]) >>
  map_every qx_gen_tac [`x`, `t`] >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (Cases_on `x1` >- simp[emit_op_labels] >>
      simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt gen_tac >> ho_match_mp_tac application_labels >> conj_tac
  >- simp[compile_raw_call_outbuf_labels] >>
  map_every qx_gen_tac [`y`, `u`] >> PairCases_on `y` >> simp[] >>
  ho_match_mp_tac application_labels >> conj_tac
  >- simp[compile_msg_data_to_memory_labels] >>
  map_every qx_gen_tac [`z`, `v`] >> PairCases_on `z` >> simp[] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[compile_raw_call_finish_labels] >>
  rpt gen_tac >> ho_match_mp_tac application_labels >> conj_tac
  >- simp[emit_void_labels] >>
  rpt gen_tac >> simp[] >> IF_CASES_TAC >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem lower_abi_encode_labels:
  !ensure mid src info maxlen s.
    cs_extends s (SND (lower_abi_encode ensure mid src info maxlen s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (lower_abi_encode ensure mid src info maxlen s)))
Proof
  rpt gen_tac >> Cases_on `mid` >>
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[emit_op_labels, emit_void_labels,
         comp_return_labels, compile_alloc_buffer_labels, cj 2 compile_abi_encode_labels])
QED

Theorem lower_abi_decode_labels:
  !src info minsz maxsz outsz s.
    cs_extends s (SND (lower_abi_decode src info minsz maxsz outsz s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (lower_abi_decode src info minsz maxsz outsz s)))
Proof
  rpt gen_tac >> Cases_on `minsz = maxsz` >>
  simp[builtinAbiTheory.lower_abi_decode_def, LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[emit_op_labels, emit_void_labels,
         comp_return_labels, compile_alloc_buffer_labels, cj 1 compile_abi_decode_labels])
QED

Theorem compile_intcall_labels:
  !cfn cenv ret_ty ty fid args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty
      (IntCall fid) args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty
      (IntCall fid) args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `cenv.ce_func_info (nsid_to_string fid)` >>
  rename1 `cenv.ce_func_info _ = (n, p)` >> PairCases_on `p` >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule compile_multi_vvs_labels >> simp[]) >>
  rpt gen_tac >> ho_match_mp_tac pair_case_labels >> conj_tac
  >- (reverse IF_CASES_TAC
      >- (reverse IF_CASES_TAC
          >- simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG] >>
          ho_match_mp_tac pair_case_labels >> conj_tac
          >- simp[compile_alloc_buffer_labels] >>
          simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
      ho_match_mp_tac pair_case_labels >> conj_tac
      >- simp[compile_alloc_buffer_labels] >>
      simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt gen_tac >> ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[compile_stage_intcall_args_labels] >>
  rpt gen_tac >> IF_CASES_TAC
  >- (Cases_on `return_buf` >> simp[] >>
      rpt (ho_match_mp_tac pair_case_labels >> conj_tac >>
           rpt gen_tac >> simp[emit_op_labels, emit_multi_op_labels,
             store_multi_results_labels]) >>
      simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[emit_void_labels] >>
  rpt gen_tac >> Cases_on `return_buf` >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_extcall_labels:
  !cfn cenv ret_ty ty stat skip sig opts args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty
      (ExtCall stat skip sig opts) args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty
      (ExtCall stat skip sig opts) args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >> PairCases_on `sig` >> Cases_on `args` >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM]
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_multi_vvs_labels]) >>
  ho_match_mp_tac application_labels >> conj_tac
  >- (irule compile_ext_call_kwargs_labels >> simp[]) >>
  map_every qx_gen_tac [`x`, `u`] >> PairCases_on `x` >> simp[] >>
  Cases_on `x2` >> simp[] >>
  TRY (PairCases_on `x` >> simp[] >> all_tac) >>
  (ho_match_mp_tac pair_case_labels >> conj_tac
   >- (Cases_on `x1` >- simp[emit_op_labels] >>
       simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
   rpt gen_tac >>
   ho_match_mp_tac pair_case_labels >> conj_tac
   >- simp[compile_external_call_kwargs_labels] >>
   rpt gen_tac >> IF_CASES_TAC >>
   simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG])
QED

Theorem compile_send_labels:
  !cfn cenv ret_ty ty gas args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty
      (Send gas) args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty
      (Send gas) args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `args` >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM]
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  Cases_on `t` >> simp[LET_THM]
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  reverse IF_CASES_TAC
  >- (ho_match_mp_tac pair_case_labels >> simp[emit_inst_labels,
        cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, emit_op_labels, emit_void_labels])
  >- (Cases_on `t'` >> simp[]
      >- simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG] >>
      Cases_on `t` >> simp[]
      >- (irule lower_value_labels >> simp[]) >>
      simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_check_create_result_labels:
  !result rof s.
    cs_extends s (SND (compile_check_create_result result rof s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_check_create_result result rof s)))
Proof
  rpt gen_tac >> Cases_on `rof` >>
  rewrite_tac[builtinCreateTheory.compile_check_create_result_def] >>
  simp[comp_return_labels] >>
  rpt (FIRST [irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, compile_alloc_buffer_labels, emit_void_labels,
            emit_op_labels, emit_inst_labels])
QED

Theorem compile_create_dispatch_labels:
  !ptr len value salt rof s.
    cs_extends s (SND (compile_create_dispatch ptr len value salt rof s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_create_dispatch ptr len value salt rof s)))
Proof
  rpt gen_tac >> Cases_on `salt` >>
  rewrite_tac[builtinCreateTheory.compile_create_dispatch_def] >> simp[] >>
  irule comp_bind_labels >> simp[emit_op_labels, compile_check_create_result_labels]
QED

Theorem compile_alloc_dynamic_labels:
  !size s P.
    cs_extends s (SND (compile_alloc_dynamic size s)) /\
    EVERY P (added_labels s (SND (compile_alloc_dynamic size s)))
Proof
  simp[contextTheory.compile_alloc_dynamic_def, emit_op_labels]
QED

Theorem compile_create_proxy_buf_labels:
  !target s.
    cs_extends s (SND (compile_create_proxy_buf target s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_create_proxy_buf target s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinCreateTheory.compile_create_proxy_buf_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, compile_alloc_buffer_labels, emit_void_labels,
            emit_op_labels])
QED

Theorem compile_create_blueprint_check_labels:
  !target offset s.
    cs_extends s (SND (compile_create_blueprint_check target offset s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_create_blueprint_check target offset s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinCreateTheory.compile_create_blueprint_check_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels])
QED

Theorem compile_create_copy_labels:
  !target value salt rof s.
    cs_extends s (SND (compile_create_copy target value salt rof s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_create_copy target value salt rof s)))
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `rof` >>
  rewrite_tac[builtinCreateTheory.compile_create_copy_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels,
            compile_alloc_dynamic_labels, compile_check_create_result_labels])
QED

Theorem compile_create_blueprint_append_labels:
  !target value salt offset size ptr len rof s.
    cs_extends s (SND (compile_create_blueprint_append target value salt
      offset size ptr len rof s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_create_blueprint_append target value salt offset size ptr len rof s)))
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `rof` >>
  Cases_on `len = Lit 0w` >>
  rewrite_tac[builtinCreateTheory.compile_create_blueprint_append_def] >> simp[] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_void_labels, emit_op_labels,
            compile_alloc_dynamic_labels, compile_copy_memory_dynamic_labels,
            compile_check_create_result_labels])
QED

Theorem compile_create_salt_labels:
  !cfn cenv opt s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_create_salt cfn cenv opt s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_salt cfn cenv opt s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `opt` >>
  rewrite_tac[compile_create_salt_def] >> simp[comp_return_labels] >>
  irule comp_bind_labels >>
  simp[lower_value_labels, comp_return_labels]
QED

Theorem compile_create_ctor_tuple_labels:
  !cfn cenv args s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_create_ctor_tuple cfn cenv args s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_ctor_tuple cfn cenv args s)))
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[compile_create_ctor_tuple_def] >> simp[LET_THM] >>
  irule comp_bind_labels >> simp[compile_multi_vvs_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_bind_labels >> simp[compile_alloc_buffer_labels] >>
  rpt gen_tac >> BETA_TAC >>
  irule comp_ignore_bind_labels >>
  simp[compile_extcall_store_values_labels, comp_return_labels]
QED

Theorem compile_create_blueprint_args_labels:
  !cfn cenv raw args s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_create_blueprint_args cfn cenv raw args s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_blueprint_args cfn cenv raw args s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `raw`
  >- (Cases_on `args`
      >- (simp[compile_create_blueprint_args_def] >>
          irule comp_ignore_bind_labels >> simp[emit_inst_labels, comp_return_labels]) >>
      rename1 `h::t` >> Cases_on `t` >>
      simp[compile_create_blueprint_args_def] >>
      rpt (FIRST [irule comp_bind_labels >> conj_tac,
                  irule comp_ignore_bind_labels >> conj_tac] >>
           rpt gen_tac >> BETA_TAC >>
           simp[lower_value_labels, emit_op_labels, emit_inst_labels, comp_return_labels])) >>
  Cases_on `args = []` >> simp[compile_create_blueprint_args_def, LET_THM, comp_return_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, compile_create_ctor_tuple_labels,
            cj 2 compile_abi_encode_labels, comp_return_labels])
QED

Theorem compile_create_snapshot_labels:
  !cenv vv ty s.
    cs_extends s (SND (compile_create_snapshot cenv vv ty s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_snapshot cenv vv ty s)))
Proof
  rpt gen_tac >> Cases_on `vv_location vv` >>
  TRY (rename1 `SOME loc` >> Cases_on `loc`) >>
  rewrite_tac[compile_create_snapshot_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, contextTheory.compile_slot_to_memory_def,
            compile_word_copy_loop_labels, compile_imm_copy_to_memory_labels,
            compile_copy_memory_dynamic_labels, emit_op_labels, comp_return_labels])
QED

Theorem compile_raw_create_labels:
  !cfn cenv bytecode value args salt rof s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_raw_create cfn cenv bytecode value args salt rof s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_raw_create cfn cenv bytecode value args salt rof s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `args = []` >>
  rewrite_tac[compile_raw_create_def] >> simp[LET_THM] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_create_snapshot_labels, lower_value_labels, emit_op_labels,
            compile_alloc_buffer_labels, compile_copy_memory_dynamic_labels,
            compile_create_ctor_tuple_labels, cj 2 compile_abi_encode_labels,
            comp_return_labels, compile_create_salt_labels, compile_create_dispatch_labels]) >>
  PairCases_on `x` >> simp[] >>
  irule comp_bind_labels >>
  simp[compile_create_salt_labels, compile_create_dispatch_labels]
QED

Theorem compile_create_call_labels:
  !cfn cenv ck salt rof args s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_create_call cfn cenv ck salt rof args s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_call cfn cenv ck salt rof args s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `args`
  >- (simp[compile_create_call_def] >> irule comp_ignore_bind_labels >>
      simp[emit_inst_labels, comp_return_labels]) >>
  rename1 `h::t` >> Cases_on `t`
  >- (simp[compile_create_call_def] >> irule comp_ignore_bind_labels >>
      simp[emit_inst_labels, comp_return_labels]) >>
  Cases_on `ck` >> Cases_on `salt` >>
  simp[compile_create_call_def, LET_THM] >>
  TRY (IF_CASES_TAC >> simp[]) >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[comp_return_labels, emit_inst_labels, lower_value_labels,
            compile_raw_create_labels, compile_create_proxy_buf_labels,
            compile_create_dispatch_labels, compile_create_copy_labels,
            compile_create_salt_labels, compile_create_blueprint_check_labels,
            compile_create_blueprint_args_labels, compile_create_blueprint_append_labels]) >>
  simp[pairTheory.ELIM_UNCURRY, compile_create_blueprint_append_labels,
       compile_raw_create_labels]
QED

Theorem compile_raw_revert_labels:
  !ptr s P. cs_extends s (SND (compile_raw_revert ptr s)) /\
    EVERY P (added_labels s (SND (compile_raw_revert ptr s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinSystemTheory.compile_raw_revert_def] >>
  irule comp_bind_labels >> simp[emit_op_labels] >>
  rpt gen_tac >> irule comp_bind_labels >> simp[emit_op_labels, emit_inst_labels]
QED

Theorem compile_call_labels:
  !cfn cenv ret_ty ty target args default_ret s.
    (!ce ty e s. cs_extends s (SND (cfn ce ty e s)) /\
      EVERY (isPREFIX "@") (added_labels s (SND (cfn ce ty e s)))) ==>
    cs_extends s (SND (compile_call cfn cenv ret_ty ty target args default_ret s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_call cfn cenv ret_ty ty target args default_ret s)))
Proof
  rpt gen_tac >> disch_tac >> Cases_on `target`
  >- (irule compile_intcall_labels >> simp[])
  >- (irule compile_extcall_labels >> simp[])
  >- (irule compile_send_labels >> simp[])
  >- (irule compile_raw_call_target_labels >> simp[])
  >- (irule compile_raw_call_calldata_labels >> simp[])
  >~ [`RawLog`]
  >- (once_rewrite_tac[compile_call_def] >> simp[LET_THM] >>
      Cases_on `args` >> simp[]
      >- (ho_match_mp_tac application_labels >>
          simp[emit_inst_labels, cs_extends_refl, added_labels_def,
               DROP_LENGTH_TOO_LONG]) >>
      Cases_on `t` >> simp[]
      >- (ho_match_mp_tac application_labels >>
          simp[emit_inst_labels, cs_extends_refl, added_labels_def,
               DROP_LENGTH_TOO_LONG]) >>
      reverse (Cases_on `t'`) >> simp[]
      >- (ho_match_mp_tac application_labels >>
          simp[emit_inst_labels, cs_extends_refl, added_labels_def,
               DROP_LENGTH_TOO_LONG]) >>
      ho_match_mp_tac application_labels >>
      simp[compile_multi_exprs_labels] >> rpt gen_tac >>
      Cases_on `expr_type h' = BaseT (BytesT (Fixed 32))` >> simp[] >>
      rpt (FIRST [CHANGED_TAC (simp[emit_inst_labels, emit_op_labels,
                    emit_void_labels, compile_alloc_buffer_labels,
                    lower_value_labels, cs_extends_refl]),
                  ho_match_mp_tac application_labels, gen_tac]) >>
      simp[added_labels_def, DROP_LENGTH_TOO_LONG])
  >~ [`RawRevert`]
  >- (once_rewrite_tac[compile_call_def] >> simp[LET_THM] >>
      Cases_on `args` >> simp[]
      >- (ho_match_mp_tac application_labels >>
          simp[emit_inst_labels, cs_extends_refl, added_labels_def,
               DROP_LENGTH_TOO_LONG]) >>
      reverse (Cases_on `t`) >> simp[]
      >- (ho_match_mp_tac application_labels >>
          simp[emit_inst_labels, cs_extends_refl, added_labels_def,
               DROP_LENGTH_TOO_LONG]) >>
      ho_match_mp_tac application_labels >> simp[lower_value_labels] >>
      rpt gen_tac >> ho_match_mp_tac application_labels >>
      simp[compile_raw_revert_labels, cs_extends_refl, added_labels_def,
           DROP_LENGTH_TOO_LONG]) >>
  once_rewrite_tac[compile_call_def] >> simp[LET_THM] >>
  ho_match_mp_tac application_labels >>
  simp[emit_inst_labels, compile_create_call_labels, as_stack_val_labels,
       cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem builtin_scalar_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  !bi. (bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
         bi = Ceil \/ bi = Floor \/ (?n. bi = Uint2Str n) \/
         (?n. bi = CalldataSlice n) \/ bi = AddMod \/ bi = MulMod \/
         bi = PowMod256) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_keccak256_word_labels]) >>
  FIRST [irule as_stack_val_labels, irule as_ptr_val_labels] >>
  simp[compile_neg_labels,
       compile_builtin_abs_labels, compile_blockhash_labels, compile_blobhash_labels,
       compile_ceil_labels, compile_floor_labels, compile_uint2str_labels,
       compile_slice_calldata_labels, compile_addmod_labels, compile_mulmod_labels,
       compile_pow_mod256_labels, emit_op_labels]
QED

Theorem builtin_environment_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  !bi. ((?i. bi = Env i) \/ (?i. bi = Acc i) \/ bi = CalldataLen) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >>
  simp[LET_THM] >> irule as_stack_val_labels >>
  simp[compile_env_var_labels, compile_acc_labels, compile_builtin_calldatasize_labels]
QED

Theorem builtin_method_id_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty MethodId args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty MethodId args st)))
Proof
  disch_tac >> Cases_on `method_id_literal (HD args)` >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >>
  simp[LET_THM, compile_literal_vv_labels] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule lower_value_labels >> simp[]) >>
  rpt gen_tac >> IF_CASES_TAC >>
  FIRST [irule as_stack_val_labels, irule as_ptr_val_labels] >>
  simp[compile_method_id_runtime_labels]
QED

Theorem compile_ecadd_points_labels:
  !p1 p2 s. cs_extends s (SND (compile_ecadd_points p1 p2 s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_ecadd_points p1 p2 s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecadd_points_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[compile_alloc_buffer_labels,
         emit_op_labels, emit_void_labels, comp_return_labels])
QED

Theorem compile_ecmul_point_labels:
  !p scalar s. cs_extends s (SND (compile_ecmul_point p scalar s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_ecmul_point p scalar s)))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecmul_point_def] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >> simp[compile_alloc_buffer_labels,
         emit_op_labels, emit_void_labels, comp_return_labels])
QED

Theorem builtin_ec_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  !bi. (bi = ECRecover \/ bi = ECAdd \/ bi = ECMul) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, unwrap_value_labels]) >>
  FIRST [irule as_stack_val_labels, irule as_ptr_val_labels] >>
  simp[compile_ecrecover_labels, compile_ecadd_points_labels, compile_ecmul_point_labels]
QED

Theorem builtin_branching_scalar_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  !bi. (bi = Not \/ bi = Len \/ (?d. bi = AsWeiValue d)) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels]) >>
  rpt IF_CASES_TAC >> irule as_stack_val_labels >>
  simp[compile_invert_labels, emit_op_labels, compile_builtin_len_labels,
       compile_builtin_calldatasize_labels, compile_as_wei_value_decimal_labels,
       compile_as_wei_value_int_labels]
QED

Theorem builtin_concat_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Concat n) args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Concat n) args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_alloc_buffer_labels, emit_op_labels, compile_concat_labels,
            emit_void_labels]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem builtin_makearray_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (MakeArray et bnd) args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty (MakeArray et bnd) args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  Cases_on `et` >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_alloc_buffer_labels]) >>
  irule as_ptr_val_labels >> simp[compile_make_array_labels, compile_make_tuple_labels]
QED

Theorem builtin_hash_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  !bi. (bi = Keccak256 \/ bi = Sha256) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  Cases_on `expr_type (HD args)` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
       TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[])) >>
  rpt IF_CASES_TAC >>
  (ho_match_mp_tac pair_case_labels >> conj_tac
   >- (irule lower_value_labels >> simp[]) >>
   rpt gen_tac >> irule as_stack_val_labels >>
   simp[compile_keccak256_bytes_labels, compile_keccak256_bytesm_labels,
        compile_keccak256_word_labels, compile_sha256_bytes_labels,
        compile_sha256_bytesm_labels, compile_sha256_word_labels])
QED

Theorem compile_bytestring_widen_copy_labels:
  !d v sz s.
    cs_extends s (SND (compile_bytestring_widen_copy d v sz s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_bytestring_widen_copy d v sz s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_bytestring_widen_copy_def] >>
  irule comp_bind_labels >> simp[compile_alloc_buffer_labels] >>
  rpt gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[compile_copy_memory_labels, comp_return_labels]
QED

Theorem type_builtin_convert_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Convert ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Convert ret_ty args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_type_builtin_dispatch_body_def] >> simp[LET_THM] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule lower_value_labels >> simp[]) >>
  rpt gen_tac >> Cases_on `ret_ty` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  simp[GSYM added_labels_def] >> irule as_stack_val_labels >>
  simp[compile_type_convert_labels, compile_bytestring_widen_copy_labels]
QED

Theorem type_builtin_abi_encode_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty
    (AbiEncode ensure mid) ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty (AbiEncode ensure mid) ret_ty args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_type_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_multi_exprs_labels,
            compile_abi_encode_args_labels, compile_alloc_buffer_labels,
            compile_store_abi_tuple_labels, emit_void_labels, unwrap_value_labels]) >>
  irule as_ptr_val_labels >> simp[lower_abi_encode_labels]
QED

Theorem type_builtin_abi_decode_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty
    (AbiDecode n) ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty (AbiDecode n) ret_ty args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_type_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[unwrap_value_labels]) >>
  irule as_ptr_val_labels >> simp[lower_abi_decode_labels]
QED

Theorem type_builtin_constants_labels:
  !tb. (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st)))
Proof
  Cases >> simp[] >> once_rewrite_tac[compile_type_builtin_dispatch_body_def] >>
  simp[LET_THM] >> rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_builtin_empty_complex_labels]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG] >>
  pairarg_tac >> simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem type_builtin_extract32_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Extract32 ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Extract32 ret_ty args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_type_builtin_dispatch_body_def] >> simp[LET_THM] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule lower_value_labels >> simp[]) >>
  rpt gen_tac >> ho_match_mp_tac application_labels >> conj_tac
  >- simp[compile_bytestring_src_labels] >>
  map_every qx_gen_tac [`x`, `s`] >> PairCases_on `x` >> simp[] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_extract32_load_labels]) >>
  irule as_stack_val_labels >> simp[compile_clamp_basetype_labels]
QED

Theorem compile_type_builtin_dispatch_body_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st)))
Proof
  disch_tac >> Cases_on `tb` >>
  simp[type_builtin_convert_labels, type_builtin_constants_labels,
       type_builtin_extract32_labels, type_builtin_abi_encode_labels,
       type_builtin_abi_decode_labels]
QED

Theorem builtin_membership_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND
    (case e of
       Builtin ann (MakeArray et bnd) elems =>
         (let (ops, st') = compile_multi_exprs f cenv elems st in
          if is_in then as_stack_val ret_ty (compile_list_membership_in needle ops st')
          else as_stack_val ret_ty (compile_list_membership_notin needle ops st'))
     | _ =>
         (let (vv, st') = f cenv rhs_ty e st in
          as_stack_val ret_ty
            (compile_var_array_membership cenv needle vv rhs_ty is_in st')))) /\
  EVERY (isPREFIX "@") (added_labels st (SND
    (case e of
       Builtin ann (MakeArray et bnd) elems =>
         (let (ops, st') = compile_multi_exprs f cenv elems st in
          if is_in then as_stack_val ret_ty (compile_list_membership_in needle ops st')
          else as_stack_val ret_ty (compile_list_membership_notin needle ops st'))
     | _ =>
         (let (vv, st') = f cenv rhs_ty e st in
          as_stack_val ret_ty
            (compile_var_array_membership cenv needle vv rhs_ty is_in st')))))
Proof
  disch_tac >> Cases_on `e` >> simp[LET_THM] >>
  TRY (rename1 `Builtin ann tag elems` >> Cases_on `tag` >> simp[LET_THM]) >>
  (ho_match_mp_tac pair_case_labels >> conj_tac
   >- simp[compile_multi_exprs_labels] >>
   rpt gen_tac >> rpt IF_CASES_TAC >> irule as_stack_val_labels >>
   simp[compile_list_membership_in_labels, compile_list_membership_notin_labels,
        compile_var_array_membership_labels])
QED

Theorem builtin_bop_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Bop op) args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Bop op) args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac pair_case_labels >> conj_tac
      >- (irule lower_value_labels >> simp[]) >>
      rpt gen_tac >> irule (SRULE [LET_THM] builtin_membership_labels) >> simp[]) >>
  IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_bytestring_hash_labels, emit_op_labels]) >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >> simp[emit_op_labels]) >>
  irule as_stack_val_labels >> simp[compile_binop_labels, emit_op_labels]
QED

Theorem builtin_slice_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Slice n) args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Slice n) args st)))
Proof
  disch_tac >> once_rewrite_tac[compile_builtin_dispatch_body_def] >> simp[LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_alloc_buffer_labels, emit_void_labels]) >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[lower_value_labels, compile_alloc_buffer_labels, emit_void_labels]) >>
  all_tac >>~- ([`cs_extends _ (SND (as_ptr_val _ _ _))`],
       irule as_ptr_val_labels >> simp[compile_slice_calldata_labels,
            compile_slice_code_labels, compile_slice_data_labels]) >>
  (ho_match_mp_tac application_labels >> conj_tac
   >- simp[compile_slice_out_buf_labels, compile_bytestring_src_labels] >>
   map_every qx_gen_tac [`x`, `s`] >> PairCases_on `x` >> simp[] >>
   rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
        simp[lower_value_labels]) >>
   irule as_ptr_val_labels >> simp[compile_slice_extcode_labels, compile_slice_data_labels])
QED

Theorem compile_builtin_dispatch_body_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st)))
Proof
  disch_tac >> Cases_on `bi` >>
  simp[builtin_scalar_labels, builtin_method_id_labels, builtin_branching_scalar_labels,
       builtin_environment_labels, builtin_hash_labels, builtin_bop_labels,
       builtin_ec_labels, builtin_concat_labels, builtin_makearray_labels, builtin_slice_labels]
QED

Theorem compile_expr_structlit_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_expr_body f g h cenv ty (StructLit ann name fields) st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_expr_body f g h cenv ty (StructLit ann name fields) st)))
Proof
  disch_tac >> once_rewrite_tac[compile_expr_body_def] >> simp[LET_THM] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[compile_alloc_buffer_labels] >>
  rpt gen_tac >> ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule compile_struct_lit_labels >> simp[]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_expr_toplevelname_labels:
  cs_extends st (SND (compile_expr_body f g h cenv ty (TopLevelName ann nsid) st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_expr_body f g h cenv ty (TopLevelName ann nsid) st)))
Proof
  once_rewrite_tac[compile_expr_body_def] >> simp[LET_THM] >>
  Cases_on `FLOOKUP cenv.ce_module_vars nsid`
  >- (simp[] >> ho_match_mp_tac pair_case_labels >>
      simp[emit_inst_labels, cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  all_tac >>~- ([`emit_inst INVALID [] [] st`],
    ho_match_mp_tac pair_case_labels >>
    simp[emit_inst_labels, cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]) >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_expr_pop_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_expr_body f g h cenv ty (Pop ann target) st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_expr_body f g h cenv ty (Pop ann target) st)))
Proof
  disch_tac >> once_rewrite_tac[compile_expr_body_def] >> simp[LET_THM] >>
  ho_match_mp_tac application_labels >> conj_tac
  >- (irule compile_get_target_ptr_labels >> simp[]) >>
  map_every qx_gen_tac [`x`, `s`] >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[compile_dynarray_pop_labels] >>
  simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_addmod_names_labels:
  cs_extends st (SND (compile_addmod_names ce rt at a bt b mt m st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_addmod_names ce rt at a bt b mt m st)))
Proof
  once_rewrite_tac[compile_addmod_names_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_name_vv_labels, unwrap_value_labels]) >>
  irule as_stack_val_labels >> simp[compile_addmod_labels]
QED

Theorem compile_mulmod_names_labels:
  cs_extends st (SND (compile_mulmod_names ce rt at a bt b mt m st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_mulmod_names ce rt at a bt b mt m st)))
Proof
  once_rewrite_tac[compile_mulmod_names_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_name_vv_labels, unwrap_value_labels]) >>
  irule as_stack_val_labels >> simp[compile_mulmod_labels]
QED

Theorem compile_powmod256_names_labels:
  cs_extends st (SND (compile_powmod256_names ce rt at a bt b st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_powmod256_names ce rt at a bt b st)))
Proof
  once_rewrite_tac[compile_powmod256_names_def] >> simp[LET_THM] >>
  rpt (ho_match_mp_tac pair_case_labels >> conj_tac >> rpt gen_tac >>
       simp[compile_name_vv_labels, unwrap_value_labels]) >>
  irule as_stack_val_labels >> simp[compile_pow_mod256_labels]
QED

Theorem fresh_label_pair_labels:
  (!lbl s. isPREFIX "@" lbl ==>
    cs_extends s (SND (k lbl s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (k lbl s)))) ==>
  cs_extends st (SND ((\(lbl,s). k lbl s) (fresh_label suffix st))) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND ((\(lbl,s). k lbl s) (fresh_label suffix st))))
Proof
  disch_tac >> rewrite_tac[GSYM (SRULE [LET_THM] comp_bind_def)] >>
  irule fresh_label_bind_labels >> simp[]
QED

Theorem compile_ifexp_arm_labels:
  !cenv res_ty arm_ty vv s.
    cs_extends s (SND (compile_ifexp_arm cenv res_ty arm_ty vv s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_ifexp_arm cenv res_ty arm_ty vv s)))
Proof
  rpt gen_tac >> rewrite_tac[compile_ifexp_arm_def] >> IF_CASES_TAC
  >- simp[unwrap_value_labels] >>
  rpt (FIRST [irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac] >>
       rpt gen_tac >> BETA_TAC >>
       simp[compile_alloc_buffer_labels, unwrap_value_labels,
            compile_store_memory_labels, comp_return_labels])
QED

Theorem compile_expr_ifexp_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) ==>
  cs_extends st (SND (compile_expr_body f g h cenv ty (IfExp ann c t e) st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_expr_body f g h cenv ty (IfExp ann c t e) st)))
Proof
  disch_tac >> once_rewrite_tac[compile_expr_body_def] >> simp[LET_THM] >>
  ho_match_mp_tac pair_case_labels >> conj_tac
  >- (irule lower_value_labels >> simp[]) >>
  rpt gen_tac >> ho_match_mp_tac pair_case_labels >> conj_tac
  >- simp[fresh_var_action_labels] >>
  rpt gen_tac >>
  rpt (ho_match_mp_tac fresh_label_pair_labels >> rpt gen_tac >> disch_tac) >>
  rpt (ho_match_mp_tac application_labels >> conj_tac
       >- (simp[emit_inst_labels, lower_value_labels, compile_ifexp_arm_labels] >>
           irule new_block_action_labels >> simp[]) >> rpt gen_tac >> simp[]) >>
  IF_CASES_TAC >> simp[cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

val expr_label_case_lift_thms =
  let val tys = [``:'a list``, ``:expr``]
      fun constant ty = Prim_rec.prove_case_const_thm
        {case_def = TypeBase.case_def_of ty,
         nchotomy = TypeBase.nchotomy_of ty}
  in map TypeBase.case_rand_of tys @ map constant tys end;

val expr_builtin_label_case =
  simp([compile_expr_body_def, LET_THM, compile_addmod_names_labels,
        compile_mulmod_names_labels, compile_powmod256_names_labels] @
       expr_label_case_lift_thms);

Theorem compile_expr_builtin_labels:
  (!ce rt t bi es s. cs_extends s (SND (g ce rt t bi es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (g ce rt t bi es s)))) ==>
  cs_extends st (SND (compile_expr_body f g h cenv ty (Builtin ann bi args) st)) /\
  EVERY (isPREFIX "@") (added_labels st
    (SND (compile_expr_body f g h cenv ty (Builtin ann bi args) st)))
Proof
  disch_tac >> Cases_on `bi`
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >- expr_builtin_label_case
  >> expr_builtin_label_case
QED

Theorem compile_expr_body_labels:
  (!ce t e s. cs_extends s (SND (f ce t e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce t e s)))) /\
  (!ce rt t bi es s. cs_extends s (SND (g ce rt t bi es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (g ce rt t bi es s)))) /\
  (!ce vt t tb rt es s. cs_extends s (SND (h ce vt t tb rt es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (h ce vt t tb rt es s)))) ==>
  cs_extends st (SND (compile_expr_body f g h cenv ty e st)) /\
  EVERY (isPREFIX "@") (added_labels st (SND (compile_expr_body f g h cenv ty e st)))
Proof
  strip_tac >> Cases_on `e` >>
  simp[compile_expr_ifexp_labels, compile_expr_structlit_labels,
       compile_expr_toplevelname_labels, compile_expr_pop_labels, compile_expr_builtin_labels] >>
  simp[compile_expr_body_def, LET_THM, compile_literal_vv_labels,
       compile_name_vv_labels, compile_subscript_labels, compile_attribute_labels,
       compile_call_labels, cs_extends_refl] >>
  all_tac >>~- ([`added_labels st st`],
    simp[added_labels_def, DROP_LENGTH_TOO_LONG])
QED

Theorem compile_expr_labels:
  (!cenv ty e st.
    cs_extends st (SND (compile_expr cenv ty e st)) /\
    EVERY (isPREFIX "@") (added_labels st (SND (compile_expr cenv ty e st)))) /\
  (!cenv ret_ty ty bi args st.
    cs_extends st (SND (compile_builtin_dispatch cenv ret_ty ty bi args st)) /\
    EVERY (isPREFIX "@") (added_labels st
      (SND (compile_builtin_dispatch cenv ret_ty ty bi args st)))) /\
  (!cenv vv_ty ty tb ret_ty args st.
    cs_extends st (SND (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st)) /\
    EVERY (isPREFIX "@") (added_labels st
      (SND (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st))))
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> simp[] >>
  all_tac >>~- ([`compile_expr_body _ _ _ _ _ _ _`],
    irule compile_expr_body_labels >> rpt conj_tac
    >- (irule expr_child_callback_labels >> simp[]) 
    >- (irule builtin_child_callback_labels >> simp[]) >>
    irule type_child_callback_labels >> simp[]) >>
  all_tac >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ _ _`],
    irule compile_builtin_dispatch_body_labels >>
    irule expr_child_callback_labels >> simp[]) >>
  irule compile_type_builtin_dispatch_body_labels >>
  irule expr_child_callback_labels >> simp[]
QED

(* Statement actions preserve the fresh-label namespace, independently of
   instruction shape or immutable storage layout. *)
fun stmt_labels_step rws =
  FIRST [ho_match_mp_tac fresh_label_pair_labels,
              irule fresh_label_bind_labels,
              irule new_block_action_labels >>
                rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
              irule comp_bind_labels >> conj_tac,
              irule comp_ignore_bind_labels >> conj_tac,
              FIRST_ASSUM MATCH_ACCEPT_TAC,
              disch_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
       rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
       simp (comp_return_labels :: rws);

fun stmt_labels_chain rws =
  rpt gen_tac >> simp (comp_return_labels :: rws) >>
  rpt (stmt_labels_step rws);

val stmt_labels_rws =
  [emit_op_labels, emit_void_labels, emit_inst_labels, fresh_var_action_labels,
   compile_alloc_buffer_labels, unwrap_value_labels, compile_snapshot_vv_labels,
   compile_store_memory_labels,
   compile_copy_memory_labels, compile_word_copy_loop_labels,
   compile_store_bytestring_labels, compile_keccak256_key_labels,
   compile_mapping_subscript_labels, compile_array_subscript_labels,
   compile_bytelike_literal_labels, typed_memory_family_labels,
   compile_abi_encode_labels, compile_ptr_load_labels,
   compile_imm_store_word_labels, compile_imm_store_words_labels,
   compile_imm_copy_to_memory_labels, compile_expr_labels,
   lower_value_labels, compile_binop_labels];

Theorem stmt_context_helpers_labels:
  (!buf slot n s. cs_extends s (SND (compile_memory_to_storage buf slot n s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_memory_to_storage buf slot n s)))) /\
  (!buf slot n s. cs_extends s (SND (compile_memory_to_transient buf slot n s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_memory_to_transient buf slot n s)))) /\
  (!src dst n loc s. cs_extends s (SND (compile_slot_to_memory src dst n loc s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_slot_to_memory src dst n loc s)))) /\
  (!p b s. cs_extends s (SND (compile_load_memory p b s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_load_memory p b s)))) /\
  (!v b s. cs_extends s (SND (compile_encode_log_topic v b s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_encode_log_topic v b s)))) /\
  (!k t v s. cs_extends s (SND (compile_nonreentrant_unlock k t v s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_nonreentrant_unlock k t v s)))) /\
  (!src dst ew ems t s. cs_extends s (SND (compile_dynarray_to_storage src dst ew ems t s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_dynarray_to_storage src dst ew ems t s))))
Proof
  rpt conj_tac >> rpt gen_tac >>
  once_rewrite_tac[compile_memory_to_storage_def, compile_memory_to_transient_def,
    compile_slot_to_memory_def, compile_load_memory_def, compile_encode_log_topic_def,
    compile_nonreentrant_unlock_def, compile_dynarray_to_storage_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem compile_dynarray_append_labels:
  !cenv b v ws es dt st cap p lo so s.
    cs_extends s (SND (compile_dynarray_append cenv b v ws es dt st cap p lo so s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_dynarray_append cenv b v ws es dt st cap p lo so s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_dynarray_append_def] >>
  simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `compile_word_copy_loop _ _ _ LocMemory dl F` >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem comp_get_labels:
  !s P. cs_extends s (SND (comp_get s)) /\
    EVERY P (added_labels s (SND (comp_get s)))
Proof
  simp[comp_get_def, cs_extends_refl, added_labels_def, DROP_LENGTH_TOO_LONG]
QED

Theorem compile_get_target_ptr_expr_labels:
  !bt cenv s.
    cs_extends s (SND (compile_get_target_ptr compile_expr cenv bt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_get_target_ptr compile_expr cenv bt s)))
Proof
  rpt gen_tac >> irule compile_get_target_ptr_labels >> simp[compile_expr_labels]
QED

val stmt_labels_rws = stmt_labels_rws @
  [stmt_context_helpers_labels, compile_dynarray_append_labels, comp_get_labels,
   compile_get_target_ptr_expr_labels];

Theorem compile_assign_value_labels:
  !cenv d l v p sl dt st da m s.
    cs_extends s (SND (compile_assign_value cenv d l v p sl dt st da m s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_assign_value cenv d l v p sl dt st da m s)))
Proof
  rpt gen_tac >> Cases_on `l` >>
  once_rewrite_tac[compile_assign_value_def]
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >> stmt_labels_chain stmt_labels_rws
QED

Theorem compile_store_at_loc_labels:
  !imm d v l s. cs_extends s (SND (compile_store_at_loc imm d v l s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_store_at_loc imm d v l s)))
Proof
  rpt gen_tac >> Cases_on `l` >>
  TRY (rename1 `SOME loc` >> Cases_on `loc`) >>
  simp[compile_store_at_loc_def, emit_void_labels, compile_imm_store_word_labels]
QED

Theorem compile_reason_message_labels:
  !cenv e s. cs_extends s (SND (compile_reason_message cenv e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_reason_message cenv e s)))
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[compile_reason_message_def, compile_expr_labels] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> Cases_on `lit` >>
  simp[compile_reason_message_def, compile_expr_labels] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_reason_message_def, compile_expr_labels] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem stmt_simple_helpers_labels:
  (!cenv m t sz s. cs_extends s (SND (compile_revert_with_reason cenv m t sz s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_revert_with_reason cenv m t sz s)))) /\
  (!a e r rb b s. cs_extends s (SND (compile_range_bound_checks a e r rb b s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_range_bound_checks a e r rb b s)))) /\
  (!cenv e i sz l a t et s. cs_extends s (SND (compile_iter_elem_copy cenv e i sz l a t et s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_iter_elem_copy cenv e i sz l a t et s)))) /\
  (!cenv id ty s. cs_extends s (SND (declare_local cenv id ty s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (declare_local cenv id ty s)))) /\
  (!cenv id s. cs_extends s (SND (emit_local_alloca cenv id s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (emit_local_alloca cenv id s)))) /\
  (!l s. cs_extends s (SND (emit_jmp_if_not_terminated l s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (emit_jmp_if_not_terminated l s))))
Proof
  rpt conj_tac >> rpt gen_tac >>
  once_rewrite_tac[compile_revert_with_reason_def, compile_range_bound_checks_def,
    compile_iter_elem_copy_def, declare_local_def, emit_local_alloca_def,
    emit_jmp_if_not_terminated_def]
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >- stmt_labels_chain stmt_labels_rws
  >> stmt_labels_chain stmt_labels_rws
QED

Theorem declare_stmt_local_labels:
  !cenv st s. cs_extends s (SND (declare_stmt_local cenv st s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (declare_stmt_local cenv st s)))
Proof
  rpt gen_tac >> Cases_on `st` >>
  simp[declare_stmt_local_def, stmt_simple_helpers_labels, comp_return_labels]
QED

val stmt_labels_rws = stmt_labels_rws @
  [compile_assign_value_labels, compile_store_at_loc_labels,
   compile_reason_message_labels, stmt_simple_helpers_labels, declare_stmt_local_labels];

Theorem stmt_list_helpers_labels:
  (!cenv es s. cs_extends s (SND (compile_log_eval_all cenv es s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_log_eval_all cenv es s)))) /\
  (!xs s. cs_extends s (SND (compile_log_topic_ops xs s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_log_topic_ops xs s)))) /\
  (!cenv xs b off s. cs_extends s (SND (compile_log_store_data cenv xs b off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_log_store_data cenv xs b off s)))) /\
  (!cenv src tys off s. cs_extends s (SND (compile_tuple_load_all cenv src tys off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_tuple_load_all cenv src tys off s)))) /\
  (!cenv tys ts vs s. cs_extends s (SND (compile_tuple_store_all cenv tys ts vs s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_tuple_store_all cenv tys ts vs s)))) /\
  (!cenv b tys off s. cs_extends s (SND (compile_load_tuple_elements cenv b tys off s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_load_tuple_elements cenv b tys off s))))
Proof
  rpt conj_tac
  >- (gen_tac >> Induct >> once_rewrite_tac[compile_log_eval_all_def] >>
      stmt_labels_chain stmt_labels_rws)
  >- (Induct >> once_rewrite_tac[compile_log_topic_ops_def] >>
      stmt_labels_chain stmt_labels_rws)
  >- (gen_tac >> Induct >> once_rewrite_tac[compile_log_store_data_def] >>
      stmt_labels_chain stmt_labels_rws)
  >- (gen_tac >> gen_tac >> Induct >> once_rewrite_tac[compile_tuple_load_all_def] >>
      stmt_labels_chain stmt_labels_rws)
  >- (ho_match_mp_tac compile_tuple_store_all_ind >> rpt conj_tac >>
      rpt gen_tac >> TRY strip_tac >> once_rewrite_tac[compile_tuple_store_all_def] >>
      stmt_labels_chain stmt_labels_rws) >>
  gen_tac >> gen_tac >> Induct >> once_rewrite_tac[compile_load_tuple_elements_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem stmt_return_helpers_labels:
  (!cenv v pc n rt st ets rb s.
    cs_extends s (SND (compile_internal_return cenv v pc n rt st ets rb s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_internal_return cenv v pc n rt st ets rb s)))) /\
  (!cenv ty st v pc s.
    cs_extends s (SND (compile_internal_return_from_env cenv ty st v pc s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_internal_return_from_env cenv ty st v pc s)))) /\
  (!v p r ei m n k t w s.
    cs_extends s (SND (compile_external_return v p r ei m n k t w s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_external_return v p r ei m n k t w s)))) /\
  (!cenv t m tgs src s.
    cs_extends s (SND (compile_tuple_unpack cenv t m tgs src s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_tuple_unpack cenv t m tgs src s))))
Proof
  rpt conj_tac >> rpt gen_tac >>
  once_rewrite_tac[compile_internal_return_def, compile_internal_return_from_env_def,
    compile_external_return_def, compile_tuple_unpack_def]
  >- (stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws) >>
      once_rewrite_tac[compile_internal_return_def] >>
      stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws))
  >- (stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws) >>
      once_rewrite_tac[compile_internal_return_def] >>
      stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws))
  >- (stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws) >>
      once_rewrite_tac[compile_internal_return_def] >>
      stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws))
  >> (stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws) >>
      once_rewrite_tac[compile_internal_return_def] >>
      stmt_labels_chain (stmt_list_helpers_labels :: stmt_labels_rws))
QED

val stmt_labels_rws = stmt_return_helpers_labels :: stmt_list_helpers_labels :: stmt_labels_rws;

(* The literal-endpoint case splits of a range loop's entry, as rewrites
   rather than a split over every pair of expression forms. *)
Theorem range_literal_case_pred:
  !Q start_e end_e f g.
    (!i j. Q (f i j)) /\ Q g ==>
    Q (case (start_e, end_e) of
             (Literal _ (IntL i), Literal _ (IntL j)) => f i j
           | _ => g)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `start_e` >> simp[] >>
  Cases_on `end_e` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem range_literal_case_extends:
  !start_e end_e f g s.
    (!i j s. cs_extends s (SND (f i j s))) /\
    (!s. cs_extends s (SND (g s))) ==>
    cs_extends s (SND ((case (start_e, end_e) of
             (Literal _ (IntL i), Literal _ (IntL j)) => f i j
           | _ => g) s))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`\a. !s. cs_extends s (SND (a s))`, `start_e`, `end_e`, `f`, `g`]
    mp_tac range_literal_case_pred >>
  simp[]
QED

Theorem range_literal_case_labels:
  !start_e end_e f g P s.
    (!i j s. EVERY P (added_labels s (SND (f i j s)))) /\
    (!s. EVERY P (added_labels s (SND (g s)))) ==>
    EVERY P (added_labels s (SND ((case (start_e, end_e) of
             (Literal _ (IntL i), Literal _ (IntL j)) => f i j
           | _ => g) s)))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`\a. !s. EVERY P (added_labels s (SND (a s)))`, `start_e`, `end_e`,
               `f`, `g`]
    mp_tac range_literal_case_pred >>
  simp[]
QED

(* Simp has already reduced the pair case in the goals, so the rewrites
   are taken in that form. *)
val for_labels_rws =
  map (SIMP_RULE bool_ss [pairTheory.pair_case_thm])
    [range_literal_case_extends, range_literal_case_labels] @ stmt_labels_rws;

Theorem compile_stmt_labels:
  (!cenv lctx ty st s. cs_extends s (SND (compile_stmt cenv lctx ty st s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_stmt cenv lctx ty st s)))) /\
  (!cenv lctx ty ss s. cs_extends s (SND (compile_stmts cenv lctx ty ss s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_stmts cenv lctx ty ss s))))
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY (disch_then strip_assume_tac)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >>
      rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      simp (comp_return_labels :: for_labels_rws) >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws >>
      stmt_labels_step for_labels_rws)
  >- (RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >> (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws))
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >- (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
  >> qpat_x_assum `!cs cenv. _ ==> !s. cs_extends _ (SND (compile_stmt _ _ _ _ _)) /\ _`
       (qspec_then `ARB with cs_current_insts := []`
         (assume_tac o SIMP_RULE (srw_ss()) [block_is_terminated_def]))
  >> qpat_x_assum `!cs cenv. _ ==> !s. cs_extends _ (SND (compile_stmts _ _ _ _ _)) /\ _`
       (qspec_then `ARB with cs_current_insts := []`
         (assume_tac o SIMP_RULE (srw_ss()) [block_is_terminated_def]))
  >> (rpt gen_tac >> once_rewrite_tac[compile_stmt_def] >>
      stmt_labels_chain stmt_labels_rws >> simp[pairTheory.ELIM_UNCURRY] >>
      stmt_labels_chain stmt_labels_rws)
QED

Theorem compile_decode_args_labels:
  !cenv args off opc hi adj s.
    cs_extends s (SND (compile_decode_args cenv args off opc hi adj s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_decode_args cenv args off opc hi adj s)))
Proof
  gen_tac >> Induct >> rpt gen_tac
  >- simp[compile_decode_args_def, comp_return_labels] >>
  PairCases_on `h` >> once_rewrite_tac[compile_decode_args_def] >>
  IF_CASES_TAC
  >- stmt_labels_chain (compile_abi_clamp_basetype_labels :: compile_abi_decode_labels :: stmt_labels_rws) >>
  IF_CASES_TAC
  >- stmt_labels_chain (compile_abi_clamp_basetype_labels :: compile_abi_decode_labels :: stmt_labels_rws) >>
  stmt_labels_chain (compile_abi_clamp_basetype_labels :: compile_abi_decode_labels :: stmt_labels_rws)
QED

Theorem compile_register_positional_args_labels:
  !cenv args off s.
    cs_extends s (SND (compile_register_positional_args cenv args off s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_register_positional_args cenv args off s)))
Proof
  Induct_on `args` >> rpt gen_tac
  >- simp[compile_register_positional_args_def, comp_return_labels] >>
  PairCases_on `h` >> once_rewrite_tac[compile_register_positional_args_def] >>
  stmt_labels_chain (compile_decode_args_labels :: stmt_labels_rws)
QED

Theorem compile_nonreentrant_lock_labels:
  !k t v s. cs_extends s (SND (compile_nonreentrant_lock k t v s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_nonreentrant_lock k t v s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_nonreentrant_lock_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem compile_guarded_body_labels:
  !cenv nr k t v body rt s.
    cs_extends s (SND (compile_guarded_body cenv nr k t v body rt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_guarded_body cenv nr k t v body rt s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_guarded_body_def] >>
  stmt_labels_chain (compile_nonreentrant_lock_labels :: compile_stmt_labels :: stmt_labels_rws)
QED

Theorem compile_external_function_body_labels:
  !cenv args nr k t v body rt s.
    cs_extends s (SND (compile_external_function_body cenv args nr k t v body rt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_external_function_body cenv args nr k t v body rt s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_external_function_body_def] >>
  stmt_labels_chain [compile_register_positional_args_labels, compile_guarded_body_labels]
QED

Theorem compile_entry_checks_labels:
  !mincd pay s. cs_extends s (SND (compile_entry_checks mincd pay s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_entry_checks mincd pay s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_entry_checks_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem fresh_namespace_labels_mono:
  !a b P. cs_extends a b /\ EVERY (isPREFIX "@") (added_labels a b) /\
    (!l. isPREFIX "@" l ==> P l) ==>
    cs_extends a b /\ EVERY P (added_labels a b)
Proof
  rpt strip_tac >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem compile_external_fn_bodies_labels:
  !packages P.
    EVERY (\p. P (FST p)) packages /\
    (!l. isPREFIX "@" l ==> P l) ==>
    !s. cs_extends s (SND (compile_external_fn_bodies packages s)) /\
      EVERY P (added_labels s (SND (compile_external_fn_bodies packages s)))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_external_fn_bodies_def, comp_return_labels] >>
  PairCases_on `h` >> simp[EVERY_DEF] >> strip_tac >>
  once_rewrite_tac[compile_external_fn_bodies_def] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule new_block_action_labels >> simp[]) >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule fresh_namespace_labels_mono >>
      simp[compile_entry_checks_labels]) >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule fresh_namespace_labels_mono >>
      simp[compile_external_function_body_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_external_fn_bodies_label_partition:
  !packages s.
    cs_extends s (SND (compile_external_fn_bodies packages s)) /\
    EVERY (\l. MEM l (MAP FST packages) \/ isPREFIX "@" l)
      (added_labels s (SND (compile_external_fn_bodies packages s)))
Proof
  rpt gen_tac >> irule compile_external_fn_bodies_labels >>
  simp[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem compile_external_fn_bodies_preserves_label_absent:
  !packages lbl s.
    ~MEM lbl (MAP FST packages) /\ ~isPREFIX "@" lbl /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    ~MEM lbl (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_external_fn_bodies packages s))))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`packages`, `s`] strip_assume_tac
    compile_external_fn_bodies_label_partition >>
  drule cs_extends_labels >> disch_then SUBST1_TAC >>
  gvs[MEM_APPEND, EVERY_MEM] >> metis_tac[]
QED

(* Fallback bodies add only compiler-generated labels, independently of locations. *)
Theorem compile_fallback_body_labels:
  !cenv pay nr k t v body rt s.
    cs_extends s (SND (compile_fallback_body cenv pay nr k t v body rt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_fallback_body cenv pay nr k t v body rt s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_fallback_body_def] >>
  stmt_labels_chain (compile_guarded_body_labels :: stmt_labels_rws)
QED

Theorem runtime_fallback_suffix_labels:
  !fb fallback P.
    P fb /\ (!l. isPREFIX "@" l ==> P l) ==>
    !s. cs_extends s
      (SND ((do new_block fb;
                case fallback of
                  NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
                | SOME (ce,pay,nr,k,t,v,fbody,rt) =>
                    compile_fallback_body ce pay nr k t v fbody rt
             od) s)) /\
      EVERY P (added_labels s
        (SND ((do new_block fb;
                  case fallback of
                    NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
                  | SOME (ce,pay,nr,k,t,v,fbody,rt) =>
                      compile_fallback_body ce pay nr k t v fbody rt
               od) s)))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule new_block_action_labels >> simp[]) >>
  Cases_on `fallback` >- simp[emit_inst_labels] >>
  PairCases_on `x` >> simp[] >> gen_tac >> irule fresh_namespace_labels_mono >>
  simp[compile_fallback_body_labels]
QED

Theorem compile_internal_param_decls_labels:
  !params idx s.
    cs_extends s (SND (compile_internal_param_decls params idx s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_internal_param_decls params idx s)))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_internal_param_decls_def, comp_return_labels] >>
  PairCases_on `h` >> once_rewrite_tac[compile_internal_param_decls_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem materialize_internal_params_labels:
  !captured ce s.
    cs_extends s (SND (materialize_internal_params ce captured s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (materialize_internal_params ce captured s)))
Proof
  Induct >> rpt gen_tac
  >- simp[materialize_internal_params_def, comp_return_labels] >>
  PairCases_on `h` >> once_rewrite_tac[materialize_internal_params_def] >>
  stmt_labels_chain stmt_labels_rws
QED

Theorem compile_fixed_region_with_id_labels:
  !sz s. cs_extends s (SND (compile_fixed_region_with_id sz s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_fixed_region_with_id sz s)))
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       cs_extends_def, added_labels_def, all_blocks_def,
       DROP_LENGTH_TOO_LONG]
QED

Theorem compile_internal_function_labels:
  !cenv params hr nr k t v ctor il body rt s.
    cs_extends s (SND (compile_internal_function cenv params hr nr k t v ctor il body rt s)) /\
    EVERY (isPREFIX "@") (added_labels s
      (SND (compile_internal_function cenv params hr nr k t v ctor il body rt s)))
Proof
  rpt gen_tac >> once_rewrite_tac[compile_internal_function_def] >>
  stmt_labels_chain
    [compile_internal_param_decls_labels, materialize_internal_params_labels,
     compile_fixed_region_with_id_labels, compile_alloc_buffer_labels,
     compile_nonreentrant_lock_labels, stmt_context_helpers_labels,
     compile_stmt_labels, comp_get_labels, emit_op_labels, emit_inst_labels] >>
  simp[pairTheory.ELIM_UNCURRY] >>
  stmt_labels_chain
    [materialize_internal_params_labels, compile_alloc_buffer_labels,
     compile_nonreentrant_lock_labels, stmt_context_helpers_labels,
     compile_stmt_labels, comp_get_labels, emit_op_labels, emit_inst_labels]
QED

Theorem compile_internal_fn_bodies_labels:
  !packages P.
    EVERY (\p. P (FST p)) packages /\
    (!l. isPREFIX "@" l ==> P l) ==>
    !s. cs_extends s (SND (compile_internal_fn_bodies packages s)) /\
      EVERY P (added_labels s (SND (compile_internal_fn_bodies packages s)))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_internal_fn_bodies_def, comp_return_labels] >>
  PairCases_on `h` >> simp[EVERY_DEF] >> strip_tac >>
  once_rewrite_tac[compile_internal_fn_bodies_def] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule new_block_action_labels >> simp[]) >>
  rpt gen_tac >> irule comp_ignore_bind_labels >> conj_tac
  >- (rpt gen_tac >> irule fresh_namespace_labels_mono >>
      simp[compile_internal_function_labels]) >>
  first_x_assum irule >> simp[]
QED

Theorem compile_internal_fn_bodies_entry_prefix:
  !packages se sf entry functions.
    compile_internal_fn_bodies packages se = ((),sf) /\
    (packages <> [] ==> ~MEM (FST (HD packages))
      (MAP (\bb. bb.bb_label) (all_blocks se))) /\
    package_internal_blocks (internal_fn_descriptors packages) (all_blocks sf) =
      SOME (entry,functions) ==>
    entry = all_blocks se
Proof
  Cases >> rpt gen_tac
  >- simp[compile_internal_fn_bodies_def, internal_fn_descriptors_def,
           package_internal_blocks_def, comp_return_def] >>
  PairCases_on `h` >> strip_tac >>
  Cases_on `new_block h0 se` >> rename1 `_ = (u,sm)` >>
  `cs_extends sm sf` by
    (qpat_x_assum `compile_internal_fn_bodies _ _ = _` mp_tac >>
     once_rewrite_tac[compile_internal_fn_bodies_def] >>
     simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
     `cs_extends sm
       (SND ((do compile_internal_function h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
                 compile_internal_fn_bodies t od) sm)) /\
      EVERY (\l. T)
       (added_labels sm
         (SND ((do compile_internal_function h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
                   compile_internal_fn_bodies t od) sm)))` by
       (irule comp_ignore_bind_labels >> conj_tac
        >- simp[compile_internal_function_labels] >>
        irule compile_internal_fn_bodies_labels >> simp[EVERY_MEM]) >>
     gvs[comp_ignore_bind_def, comp_bind_def]) >>
  drule cs_extends_block_stream_labels >> strip_tac >>
  `REVERSE sm.cs_blocks = all_blocks se /\ sm.cs_current_bb = h0` by
    gvs[new_block_def, all_blocks_def, LET_THM] >>
  gvs[internal_fn_descriptors_def] >>
  irule package_internal_blocks_entry_prefix >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_selector_checks_no_fn_labels:
  !selectors method_id sa sd.
    compile_selector_checks method_id selectors sa = ((), sd) /\
    (!l. l IN bound_labels sa ==> ~isPREFIX "fn_" l) ==>
    !l. l IN bound_labels sd ==> ~isPREFIX "fn_" l
Proof
  Induct_on `selectors`
  >- simp[compile_selector_checks_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_selector_checks_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_inst_def, fresh_var_def,
       fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  strip_tac >> first_x_assum (drule_at Any) >>
  simp[] >> disch_tac >> gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  simp[bound_labels_def, fresh_label_output_def] >>
  fs[bound_labels_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_selector_checks_state_ok:
  !selectors method_id sa sd.
    compile_selector_checks method_id selectors sa = ((), sd) /\
    compile_state_ok sa ==> compile_state_ok sd
Proof
  Induct_on `selectors`
  >- simp[compile_selector_checks_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_selector_checks_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_inst_def, fresh_var_def,
       fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  strip_tac >> qpat_x_assum `compile_state_ok sa` mp_tac >>
  first_x_assum (drule_at Any) >> disch_tac >> strip_tac >>
  first_x_assum irule >>
  qpat_x_assum `compile_selector_checks _ _ _ = _` kall_tac >>
  fs[compile_state_ok_def, bound_labels_def, pred_setTheory.IN_DISJOINT] >>
  simp[fresh_label_output_in_future, fresh_label_output_inj] >>
  conj_tac
  >- (gen_tac >> Cases_on `x IN compiler_labels_future (sa.cs_next_label + 2)` >> simp[] >>
      `x IN compiler_labels_future sa.cs_next_label` by
        (fs[compiler_labels_future_def] >>
         metis_tac[DECIDE ``n + 2 <= k ==> n <= k``]) >>
      `x <> fresh_label_output "next" (sa.cs_next_label + 1) /\
       x <> fresh_label_output "match" sa.cs_next_label` by
        (rpt strip_tac >> gvs[fresh_label_output_in_future]) >>
      metis_tac[]) >>
  `fresh_label_output "next" (sa.cs_next_label + 1) <>
   fresh_label_output "match" sa.cs_next_label` by
    (strip_tac >> drule fresh_label_output_inj >> simp[]) >>
  first_assum (qspec_then `fresh_label_output "next" (sa.cs_next_label + 1)` mp_tac) >>
  first_x_assum (qspec_then `fresh_label_output "match" sa.cs_next_label` mp_tac) >>
  simp[fresh_label_output_in_future]
QED

Theorem compile_selector_dispatch_linear_state_ok:
  !selectors fallback sa sd.
    compile_selector_dispatch_linear selectors fallback sa = ((), sd) /\
    compile_state_ok sa ==> compile_state_ok sd
Proof
  rpt gen_tac >>
  simp[compile_selector_dispatch_linear_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `compile_state_ok cs'` suffices_by simp[compile_state_ok_def, bound_labels_def] >>
  drule compile_selector_checks_state_ok >> disch_then irule >>
  qpat_x_assum `compile_selector_checks _ _ _ = _` kall_tac >>
  fs[compile_state_ok_def, bound_labels_def, pred_setTheory.IN_DISJOINT] >>
  simp[fresh_label_output_in_future] >>
  conj_tac
  >- (gen_tac >> Cases_on `x IN compiler_labels_future (sa.cs_next_label + 1)` >> simp[] >>
      `x IN compiler_labels_future sa.cs_next_label` by
        (fs[compiler_labels_future_def] >>
         metis_tac[DECIDE ``n + 1 <= k ==> n <= k``]) >>
      `x <> fresh_label_output "dispatch" sa.cs_next_label` by
        (strip_tac >> gvs[fresh_label_output_in_future]) >>
      metis_tac[]) >>
  first_x_assum (qspec_then `fresh_label_output "dispatch" sa.cs_next_label` mp_tac) >>
  simp[fresh_label_output_in_future]
QED
Theorem compile_selector_dispatch_linear_no_fn_labels:
  !selectors fallback sa sd.
    compile_selector_dispatch_linear selectors fallback sa = ((), sd) /\
    (!l. l IN bound_labels sa ==> ~isPREFIX "fn_" l) ==>
    !l. l IN bound_labels sd ==> ~isPREFIX "fn_" l
Proof
  rpt gen_tac >>
  simp[compile_selector_dispatch_linear_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[bound_labels_def] >>
  drule compile_selector_checks_no_fn_labels >>
  simp[bound_labels_def, fresh_label_output_def] >>
  disch_tac >> gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  fs[bound_labels_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED


