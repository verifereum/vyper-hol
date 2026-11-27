Theory bodyAbiDecodeGuardedComplexMods
Ancestors
  bodyAbiDecodeGuardedComplexPrefixMods bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeCutNoncrossing bodyFullAbiDecodeCutPath
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeMemberLayout
  abiDecodePtrPrims abiDecoderMemberInfos externalEntryShape loweringShapeRules abiDecoderRange
  fragExec fragGasPath fragGasOriginPtrLoop exprSimAbiGasBridge
  compileEnv emitHelperProps venomState venomInst venomExecSemantics
  words list rich_list finite_map valueEncodingTyping
Libs
  bodyFullAbiDecodeComplexPrefixSyntaxLib[qualified]
  bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyFullAbiDecodeCutPathLib
  bodyAbiDecodeGuardedEffectSyntaxLib

val member_motive = decorate_motive bounded_complex_plus_typed;
val complex_motive = guarded_effect_motive_typed ();
val member_inputs = [``dst:operand``, ``src:operand``, ``opc:opcode``,
  ``base_op:operand``, ``hi:operand``, ``infos:(abi_dec_info # num # num) list``, ``0:num``, ``0:num``];
val complex_inputs = List.take (member_inputs, 5) @ [``DecComplex dyn infos``];
val member = beta (list_mk_comb (member_motive, member_inputs));
val complex = beta (list_mk_comb (complex_motive, complex_inputs));
val span_at = ``ComplexSpan:compile_state -> compile_state -> bool``;
val good_at = ``Reached:compile_state -> venom_state -> bool``;
val outcome_at = ``Selected:compile_state -> exec_result -> bool``;

fun marked tm =
  let
    val (ps,imp) = strip_forall tm
    val (entry,post) = dest_imp imp
    val a = param ps "start" and b = param ps "finish" and s = param ps "s"
  in list_mk_forall (ps, mk_imp
    (``^entry /\ ^span_at ^a ^b /\ ^good_at ^a ^s``,
     extend_post post ``\r. ^outcome_at ^b r``)) end;
val marked_members = marked member;
val marked_complex = marked complex;

(* Same real witnesses in both modes; only the extra observer differs. *)
val header_mark = ``!a b f s r.
  ^span_at a f /\ ^good_at a s /\ cs_extends a b /\ cs_extends b f /\
  b.cs_blocks = a.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
    ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) ==>
  ((!t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts ==> ^good_at b t) /\
   (!t. r = Abort Revert_abort t ==> ^outcome_at f r))``;
val subspan = ``!a b f. ^span_at a f /\ cs_extends a b /\ cs_extends b f /\
  b.cs_blocks = a.cs_blocks ==> ^span_at b f``;

Theorem linked_complex_header_shape[local]:
  emit_op ADD [src;Lit (n2w n)] a = (e,sm) /\
  compile_abi_decode_range_check src e hi sm = ((),b) ==>
  b.cs_blocks = a.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
    ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >> conj_tac
  >- (drule_then strip_assume_tac emit_op_facts >>
      drule_then strip_assume_tac compile_abi_decode_range_check_fragment_shape >> simp[]) >>
  drule_all_then strip_assume_tac abi_decode_complex_header_shape >>
  simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
  qpat_assum `EVERY _ (emitted_insts a b)` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `i` mp_tac) >>
  simp[freshWritesTheory.fresh_write_op_def] >> strip_tac >>
  gvs[venomInstTheory.is_terminator_def]
QED

Theorem complex_effect_bind[local]:
  ^subspan /\ ^header_mark /\ ^marked_members ==> ^marked_complex
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 (mk_asm "subspan")
    (CONJUNCTS_THEN2 (mk_asm "header_mark") (mk_asm "member_ih"))) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `compile_abi_decode_to_buf dst src opc base_op hi (DecComplex dyn infos) start = ((),last)` >>
  mp_tac (BETA_RULE (Q.SPEC `last` abi_decode_complex_prefix_observed_effect_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- suspend "header_reject" >>
  suspend "member_entry"
QED

Resume complex_effect_bind[header_reject]:
  qpat_x_assum `?e sm sb. emit_op _ _ _ = _ /\ _` strip_assume_tac >>
  drule_all_then strip_assume_tac linked_complex_header_shape >>
  asm "header_mark" (qspecl_then [`start`, `sb`, `last`, `s`, `Abort Revert_abort t`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `t` mp_tac o CONJUNCT2) >>
  simp_tac bool_ss [] >> disch_tac >>
  qexistsl [`Abort Revert_abort t`, `Gf`, `tnf`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists `t` >> REFL_TAC
QED

Resume complex_effect_bind[member_entry]:
  `(^input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl [`s`, `start`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at start x ==> _` drule >> simp[]) >>
  qpat_assum `DecComplex dyn infos = type_to_abi_dec_info sf ce ty` (assume_tac o SYM) >>
  drule_all (BETA_RULE abi_decode_typed_member_layout) >>
  disch_then (qx_choose_then `env1` (qx_choose_then `sf1`
    (qx_choose_then `tys1` (qx_choose_then `tvs1`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "layout"))))))) >>
  `abi_decoder_member_infos sf1 ce tys1 = abi_decoder_member_infos sf' ce tys` by
    (qpat_assum `infos = abi_decoder_member_infos sf1 ce tys1`
       (fn th => once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
  pop_assum (mk_asm "infos_eq") >>
  `SUM (MAP (type_memory_bytes ce) tys1) = SUM (MAP (type_memory_bytes ce) tys)` by
    (asm "infos_eq"
       (mp_tac o AP_TERM ``FOLDR (\(_:abi_dec_info,_:num,msz:num) acc. msz+acc) 0``) >>
     rewrite_tac[abi_decode_member_memory_sum]) >>
  `SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys1) =
   SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)` by
    (asm_x "infos_eq"
       (mp_tac o AP_TERM ``FOLDR (\(_:abi_dec_info,asz:num,_:num) acc. asz+acc) 0``) >>
     simp[abi_decoder_member_infos_def, rich_listTheory.FOLDR_MAP, rich_listTheory.SUM_FOLDR]) >>
  `cs_extends start sb` by
    (irule cs_extends_trans >> qexists `sm` >> conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`] compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb last` by
    (mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 compile_abi_decode_labels)) >> simp[]) >>
  drule_all_then strip_assume_tac linked_complex_header_shape >>
  suspend "run_member"
QED

Resume complex_effect_bind[run_member]:
  `Reached sb t` by
    (asm "header_mark" (qspecl_then [`start`, `sb`, `last`, `s`, `OK t`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `t` mp_tac o CONJUNCT1) >> simp_tac bool_ss [] >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_x "subspan" (drule_all_then assume_tac) >>
  asm_x "member_ih"
    (qspecl_then [`env1`, `sf1`, `[]`, `[]`, `tys1`, `tvs1`, `live`, `protected`,
                  `sb`, `last`, `t`, `Gf`, `tnf`, `d`] mp_tac) >>
  (impl_tac >- (gns[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `G'` (qx_choose_then `tn'`
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) (mk_asm "certificate"))))) >>
  qexistsl [`r`, `G'`, `tn'`] >>
  reverse conj_tac >- asm "certificate" ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `horizon` >> strip_tac >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gf`, `t`, `tnf`] >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `obs` >> strip_tac >> drule_all fn_has_code_split >> strip_tac >>
     `gas_path ctx obs s 0 (OK t) /\ gas_path ctx obs t 0 r` by simp[] >>
     drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `_ \/ (?u. r = Abort Revert_abort u)`
    (DISJ_CASES_THEN2 (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))
      (qx_choose_then `u` assume_tac))
  >- (disj1_tac >> qexists `u` >> suspend "normal_join") >>
  disj2_tac >> qexists `u` >> first_assum ACCEPT_TAC
QED

Resume complex_effect_bind[normal_join]:
  `start.cs_next_var <= sb.cs_next_var` by (drule_all abi_decode_complex_header_shape >> simp[]) >>
  `!x. not_fresh_at start x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sb x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists `start` >> simp[]) >>
     qpat_assum `!x. not_fresh_at start x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sb x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\
    i IN tn'.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tnf.t_mem = tn.t_mem` (fn th =>
       qpat_assum `!i. _ /\ _ /\ i IN tn'.t_mem ==> i IN tnf.t_mem`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `abi_decode_guarded_effect s tn u tn'` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnf`, `t`] >> simp[]) >>
  asm_rewrite_tac[] >> suspend "aggregate_robust"
QED

Resume complex_effect_bind[aggregate_robust]:
  rpt strip_tac >>
  asm_x "layout" (qspecl_then [`d`, `u.vs_memory`, `mem`] mp_tac) >>
  (impl_tac >- (
    qx_gen_tac `k` >> qx_gen_tac `child` >> strip_tac >>
    `val_wf (EL k tvs1) child` by
      (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
    qpat_assum `!k. k < LENGTH tvs1 ==> _`
      (qspec_then `k` (irule o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES])) >> simp[])) >>
  disch_then irule >> simp[]
QED

Finalise complex_effect_bind[local]

val std_clause = #complex (guarded_effect_compiler_cases (guarded_effect_length_ind_typed ()));
val cut_clause = #complex (guarded_effect_compiler_cases (guarded_effect_cut_ind ()));

val regular_bind = SIMP_RULE bool_ss [BETA_THM]
  (INST [span_at |-> ``\a:compile_state b:compile_state. T``,
         good_at |-> ``\a:compile_state s:venom_state. T``,
         outcome_at |-> ``\a:compile_state r:exec_result. T``] complex_effect_bind);

Theorem abi_decode_guarded_complex_mods:
  ^std_clause
Proof
  BETA_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "bounded") assume_tac) >>
  simp_tac bool_ss [] >>
  MATCH_MP_TAC (Q.INST [`src` |-> `src_op`, `opc` |-> `load_opc`,
    `hi` |-> `hi_op`, `infos` |-> `elems`, `dyn` |-> `is_dyn_complex`] regular_bind) >>
  rpt gen_tac >> disch_then (mk_asm "entry") >>
  asm "entry" (map_every assume_tac o CONJUNCTS) >>
  asm "bounded" (qspec_then
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (elems:(abi_dec_info # num # num) list)` mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => MATCH_MP_TAC (SPEC_ALL (SIMP_RULE bool_ss [] th))) >>
  asm "entry" ACCEPT_TAC
QED

val cut_span = ``\a b. (^span) a b /\ (^crosses) a b``;
val cut_reached = ``\a s. ?w. (^related) a s w /\
  (^shadow_path) ctx ^cut_fn ^cut_pos shadow_in w``;
val cut_selected = ``(^replay) shadow_in``;
val cut_marks = [span_at |-> cut_span, good_at |-> cut_reached, outcome_at |-> cut_selected];
val cut_bind = BETA_RULE (INST cut_marks complex_effect_bind);
val cut_header = beta (subst cut_marks header_mark);

Theorem linked_complex_cut_header_replay[local]:
  ^outer_layout /\ (^span) a b /\ a.cs_blocks = cut_start.cs_blocks /\
  b.cs_blocks = a.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
    ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  (^related) a s w /\ (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
  ((?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
         t.vs_inst_idx = LENGTH b.cs_current_insts) \/ (?t. r = Abort Revert_abort t)) ==>
  (^replay) w b r
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_start a` by metis_tac[cs_extends_trans] >>
  mp_tac (BETA_RULE (Q.INST [`Q` |-> `\p g tn. p = r`,
    `start` |-> `cut_start`, `final` |-> `cut_finish`, `u` |-> `w`]
    abi_decode_cut_noncrossing_selected)) >>
  gvs[]
QED

Theorem linked_complex_cut_header_mark[local]:
  ^outer_layout ==> ^cut_header
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?w. (~w.vs_halted /\ _) /\ _` (qx_choose_then `w`
    (CONJUNCTS_THEN2 (mk_asm "related") assume_tac)) >>
  `cs_extends b cut_finish` by (irule cs_extends_trans >> qexists `f` >> simp[]) >>
  `((?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
     t.vs_inst_idx = LENGTH b.cs_current_insts) \/ (?t. r = Abort Revert_abort t)) ==>
    (^replay) shadow_in b r` by
      (disch_tac >> BETA_TAC >> irule (BETA_RULE abi_decode_cut_prefix_bind) >>
       qexists `w` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
       MATCH_MP_TAC (BETA_RULE linked_complex_cut_header_replay) >>
       asm "related" (map_every assume_tac o CONJUNCTS) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (mk_asm "replay" o BETA_RULE) >>
  conj_tac >- suspend "normal" >> suspend "reject"
QED

Resume linked_complex_cut_header_mark[normal]:
  qx_gen_tac `t` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "replay" mp_tac >>
  (impl_tac >- (disj1_tac >> qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[] >> disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qexists `v` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume linked_complex_cut_header_mark[reject]:
  qx_gen_tac `t` >> disch_tac >> asm "replay" mp_tac >>
  (impl_tac >- (disj2_tac >> qexists `t` >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Finalise linked_complex_cut_header_mark[local]

val cut_complex_at_seed = Q.INST [`src` |-> `src_op`, `opc` |-> `load_opc`,
  `hi` |-> `hi_op`, `infos` |-> `elems`, `dyn` |-> `is_dyn_complex`] cut_bind;

Theorem abi_decode_guarded_complex_cut_mods:
  ^outer_layout ==> ^cut_clause
Proof
  BETA_TAC >> disch_then (mk_asm "layout") >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "bounded") assume_tac) >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "outer_entry")
    (CONJUNCTS_THEN2 (mk_asm "outer_span")
      (CONJUNCTS_THEN2 (mk_asm "outer_crosses") (mk_asm "outer_related")))) >>
  asm "outer_related" (assume_tac o List.last o CONJUNCTS) >>
  rename1 `frag_relabel_state L cut_start.cs_current_bb shadow_in s` >>
  pop_assum kall_tac >>
  mp_tac cut_complex_at_seed >>
  (impl_tac >- (conj_tac >- suspend "span" >>
      conj_tac >- (asm "layout" (ACCEPT_TAC o MATCH_MP linked_complex_cut_header_mark)) >>
      suspend "member")) >>
  suspend "select"
QED

Resume abi_decode_guarded_complex_cut_mods[span]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_ready b` by (irule cs_extends_trans >> qexists `a` >> simp[]) >>
  rpt conj_tac >> simp[]
QED

Resume abi_decode_guarded_complex_cut_mods[member]:
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "member_entry")
    (CONJUNCTS_THEN2 (mk_asm "member_span") (qx_choose_then `w`
      (CONJUNCTS_THEN2 (mk_asm "related") assume_tac)))) >>
  asm "member_entry" (map_every assume_tac o CONJUNCTS) >>
  asm "bounded" (qspec_then
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (elems:(abi_dec_info # num # num) list)` mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
  disch_then (fn ih => asm "member_entry" (fn entry => asm "member_span" (fn slice =>
    asm "related" (mp_tac o MATCH_MP (SPEC_ALL ih) o CONJ entry o
      CONJ (CONJUNCT1 slice) o CONJ (CONJUNCT2 slice))))) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (CONJUNCTS_THEN2 (mk_asm "typed_post") assume_tac)))) >>
  qexistsl [`r`, `Gf`, `tnf`] >> conj_tac >- asm "typed_post" ACCEPT_TAC >>
  irule (BETA_RULE abi_decode_cut_prefix_bind) >> qexists `w` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_guarded_complex_cut_mods[select]:
  disch_then (fn th => MATCH_MP_TAC (SPEC_ALL th)) >>
  conj_tac >- asm "outer_entry" ACCEPT_TAC >>
  conj_tac >- (conj_tac >- asm "outer_span" ACCEPT_TAC >> asm "outer_crosses" ACCEPT_TAC) >>
  qexists `shadow_in` >> conj_tac >- asm "outer_related" ACCEPT_TAC >> simp[]
QED

Finalise abi_decode_guarded_complex_cut_mods
