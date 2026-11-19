Theory bodyFullAbiDecodeCutComplexBind
Ancestors
  bodyFullAbiDecodeCutPath bodyFullAbiDecodeComplexPrefixObserved
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeMemberLayout
  bodyFullAbiDecodeMemberPrefix valueEncodingTyping
  fragGasOriginPtrLoop fragGasPath fragExec externalEntryShape abiDecodePtrPrims
  abiDecoderMemberInfos abiDecoderCoherence abiEncoder abiDecoderRange
  loweringShapeRules bodyFullAbiDecodeComplexPrefixSlice
  compileEnv words list rich_list finite_map
Libs
  bodyFullAbiDecodeCutPathLib bodyFullAbiDecodeLoopObservedSyntaxLib

val beta = rhs o concl o QCONV (REDEPTH_CONV BETA_CONV);
val good = ``Good:compile_state -> venom_state -> bool``;
val bad = ``Bad:venom_state -> bool``;
val span = ``Span:compile_state -> compile_state -> bool``;
val prefix_span = ``PrefixSpan:compile_state -> compile_state -> bool``;
val member_span = ``MemberSpan:compile_state -> compile_state -> bool``;
val certificate = ``\b r. (!v. r = OK v ==> ^good b v) /\
                            (!v. r = Abort Revert_abort v ==> ^bad v)``;

fun named vars name = valOf (List.find (fn v => fst (dest_var v) = name) vars);
fun mark_with phase_span motive inputs =
  let
    val (vs, implication) = strip_forall (beta (list_mk_comb (motive, inputs)))
    val (pre, post) = dest_imp implication
    val a = named vs "start" and b = named vs "finish" and s = named vs "s"
  in
    list_mk_forall (vs, mk_imp (``^pre /\ ^phase_span ^a ^b /\ ^good ^a ^s``,
      extend_post post ``\outcome. ^certificate ^b outcome``))
  end;

val (finish_q, prefix_imp) = dest_forall (concl (BETA_RULE abi_decode_complex_prefix_observed));
val (prefix_pre, prefix_post) = dest_imp prefix_imp;
val prefix_vars = free_vars prefix_imp;
val prefix_start = named prefix_vars "start";
val prefix_s = named prefix_vars "s";
val prefix_params = map (named prefix_vars)
  ["env", "sf", "ty", "tv", "live", "protected", "start", "s", "G", "tn", "d"] @ [finish_q];
fun decorate_extend tm f =
  let val (vs,body) = strip_exists tm in list_mk_exists (vs, mk_conj (body,f vs)) end;
val (reject_post, normal_post) = dest_disj prefix_post;
fun mark_prefix phase_span = list_mk_forall (prefix_params,
  mk_imp (``^prefix_pre /\ ^phase_span ^prefix_start ^finish_q /\ ^good ^prefix_start ^prefix_s``,
    mk_disj (decorate_extend reject_post (fn vs => ``^bad ^(named vs "t")``),
             decorate_extend normal_post (fn vs => ``^good ^(named vs "sb") ^(named vs "t")``))));
fun mark_members phase_span = mark_with phase_span bounded_complex_plus_typed
  [``dst:operand``, ``src:operand``, ``opc:opcode``, ``base_op:operand``, ``hi:operand``,
   ``infos:(abi_dec_info # num # num) list``, ``0:num``, ``0:num``];
val complex_inputs =
  [``dst:operand``, ``src:operand``, ``opc:opcode``, ``base_op:operand``, ``hi:operand``,
   ``DecComplex dyn infos``];
val marked_complex = mark_with span guarded_plus_typed complex_inputs;

Theorem complex_header_straight[local]:
  emit_op ADD [src;Lit (n2w sz)] a = (e,sm) /\
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
  qpat_x_assum `EVERY _ (emitted_insts a b)` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `i` mp_tac) >>
  simp[freshWritesTheory.fresh_write_op_def] >> strip_tac >>
  gvs[venomInstTheory.is_terminator_def]
QED

(* The prefix is requested on the whole invocation; the member call has
   the same finish and starts after a header that has not closed a block. *)
Theorem complex_marked_bind_on_slices[local]:
  (!a m b. ^span a b /\ cs_extends a m /\ cs_extends m b /\
    m.cs_blocks = a.cs_blocks ==> ^member_span m b) /\
  ^(mark_prefix span) /\ ^(mark_members member_span) ==> ^marked_complex
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 (mk_asm "span")
    (CONJUNCTS_THEN2 (mk_asm "prefix") (mk_asm "member_ih"))) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `compile_abi_decode_to_buf dst src opc base_op hi (DecComplex dyn infos) start = ((),last)` >>
  asm_x "prefix"
    (qspecl_then [`env`, `sf`, `ty`, `tv`, `live`, `protected`, `start`,
                  `s`, `G`, `tn`, `d`, `last`] mp_tac) >>
  (impl_tac >- (gns[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (qexistsl [`Abort Revert_abort t`, `Gf`, `tnf`] >> simp[]) >>
  `(^input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl [`s`, `start`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at start x ==> _` drule >> simp[]) >>
  qpat_assum `DecComplex dyn infos = type_to_abi_dec_info sf ce ty`
    (assume_tac o SYM) >>
  drule_all (BETA_RULE abi_decode_typed_member_layout) >>
  disch_then (qx_choose_then `env1` (qx_choose_then `sf1`
    (qx_choose_then `tys1` (qx_choose_then `tvs1`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "layout"))))))) >>
  `abi_decoder_member_infos sf1 ce tys1 = abi_decoder_member_infos sf' ce tys` by
    gvs[] >>
  pop_assum (mk_asm "infos_eq") >>
  `SUM (MAP (type_memory_bytes ce) tys1) = SUM (MAP (type_memory_bytes ce) tys)` by
    (asm "infos_eq"
       (mp_tac o AP_TERM ``FOLDR (\(_:abi_dec_info,_:num,msz:num) acc. msz+acc) 0``) >>
     rewrite_tac[abi_decode_member_memory_sum]) >>
  `SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys1) =
   SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)` by
    (asm_x "infos_eq"
       (mp_tac o AP_TERM ``FOLDR (\(_:abi_dec_info,asz:num,_:num) acc. asz+acc) 0``) >>
     simp[abi_decoder_member_infos_def, rich_listTheory.FOLDR_MAP,
          rich_listTheory.SUM_FOLDR]) >>
  `cs_extends start sb` by
    (irule cs_extends_trans >> qexists `sm` >>
     conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`]
       compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb last` by
    (mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 compile_abi_decode_labels)) >> simp[]) >>
  `sb.cs_blocks = start.cs_blocks` by
    (drule_all_then strip_assume_tac complex_header_straight >> simp[]) >>
  asm_x "span" (drule_all_then strip_assume_tac) >>
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
  qpat_x_assum `(?u. r = OK u /\ _) \/ _`
    (DISJ_CASES_THEN2
      (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))
      (qx_choose_then `u` assume_tac))
  >- (disj1_tac >> qexists `u` >>
      `start.cs_next_var <= sb.cs_next_var` by
        (drule_all abi_decode_complex_header_shape >> simp[]) >>
      `!x. not_fresh_at start x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)` by
        (qx_gen_tac `x` >> strip_tac >>
         `not_fresh_at sb x` by (irule freshWritesTheory.not_fresh_at_mono >> metis_tac[]) >>
         qpat_assum `!x. not_fresh_at start x ==> _` (qspec_then `x` mp_tac) >>
         qpat_assum `!x. not_fresh_at sb x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
      `!i. output_base <= i /\ i < output_base+output_cap /\
        i IN tn'.t_mem ==> i IN tn.t_mem` by
        (qpat_assum `tnf.t_mem = tn.t_mem` (fn th =>
           qpat_assum `!i. _ /\ _ /\ i IN tn'.t_mem ==> i IN tnf.t_mem`
             (ACCEPT_TAC o REWRITE_RULE [th]))) >>
      asm_rewrite_tac[] >> suspend "aggregate_robust") >>
  disj2_tac >> qexists `u` >> simp[]
QED

Resume complex_marked_bind_on_slices[aggregate_robust]:
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

Finalise complex_marked_bind_on_slices[local]

val marked_prefix = mark_prefix span;
val marked_members = mark_members span;

Theorem abi_decode_complex_marked_bind:
  (!a m b. ^span a b /\ cs_extends a m /\ cs_extends m b ==>
    ^span a m /\ ^span m b) /\ ^marked_prefix /\ ^marked_members ==>
  ^marked_complex
Proof
  strip_tac >> MATCH_MP_TAC (Q.INST [`MemberSpan` |-> `Span`] complex_marked_bind_on_slices) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* The cut and observer are fixed through the two phases. A successful
   header has not changed the block history, so on a crossing invocation
   the member call is itself crossing. *)
val crossing = ``\a b.
  cs_extends outer_start ready /\ cs_extends ready a /\
  cs_extends a b /\ cs_extends b final /\
  a.cs_blocks = outer_start.cs_blocks /\ b.cs_blocks <> outer_start.cs_blocks``;
val cursor = ``(^shadow_cursor) L outer_start``;
val related = ``\b (v:venom_state) w. ~w.vs_halted /\
  (w.vs_current_bb,w.vs_inst_idx) = ^cursor b /\
  exprSimAbiGasBridge$frag_relabel_state L outer_start.cs_current_bb w v``;
val trace = ``(^shadow_path) ctx shadow_fn Kcut``;
val replay = ``\u b r. (^shadow_result) ctx shadow_fn Kcut L outer_start.cs_current_bb u (^cursor b) r``;
val accept = ``\b v. ?w. ^related b v w /\ ^trace u0 w``;
val reject = ``\(v:venom_state). ?w k. exprSimAbiGasBridge$frag_relabel_state L outer_start.cs_current_bb w v /\
                         run_from k ctx shadow_fn u0 = Abort Revert_abort w``;
val before_adapter = ``!a b v w r.
  cs_extends outer_start ready /\ cs_extends ready a /\
  cs_extends a b /\ cs_extends b final /\
  a.cs_blocks = outer_start.cs_blocks /\ b.cs_blocks = outer_start.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
             ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  ~v.vs_halted /\ v.vs_current_bb = a.cs_current_bb /\
  v.vs_inst_idx = LENGTH a.cs_current_insts /\ ^related a v w /\
  (!obs. fn_has_code a b obs ==> gas_path ctx obs v 0 r) /\
  ((?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts) \/
   (?t. r = Abort Revert_abort t)) ==> ^replay w b r``;

fun cut_crossing motive inputs =
  let
    val (vs, impl) = strip_forall (beta (list_mk_comb (motive, inputs)))
    val (pre, post) = dest_imp impl
    val a = named vs "start" and b = named vs "finish" and s = named vs "s"
    val u = ``shadow_in:venom_state``
  in
    list_mk_forall (vs @ [u], mk_imp (``^pre /\ ^crossing ^a ^b /\ ^related ^a ^s ^u``,
      extend_post post ``\r. ^replay ^u ^b r``))
  end;
val member_inputs = List.take (complex_inputs, 5) @
  [``infos:(abi_dec_info # num # num) list``, ``0:num``, ``0:num``];
val member_cut = cut_crossing bounded_complex_plus_typed member_inputs;
val complex_cut = cut_crossing guarded_plus_typed complex_inputs;
val exact_prefix = close_statement (concl (BETA_RULE abi_decode_complex_prefix_observed_slice));
val cut_marks = [good |-> accept, bad |-> reject, span |-> crossing, member_span |-> crossing];
val cut_bind = BETA_RULE (INST cut_marks complex_marked_bind_on_slices);

Theorem abi_decode_cut_complex_from_prefix:
  ^exact_prefix ==> ^before_adapter ==> ^member_cut ==> ^complex_cut
Proof
  BETA_TAC >> disch_then (mk_asm "prefix") >> disch_then (mk_asm "adapter") >>
  disch_then (mk_asm "cut_ih") >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "outer_entry")
    (CONJUNCTS_THEN2 (mk_asm "outer_span") (mk_asm "outer_related"))) >>
  asm "outer_related" (CONJUNCTS_THEN2 (K all_tac)
    (CONJUNCTS_THEN2 (K all_tac) assume_tac)) >>
  rename1 `exprSimAbiGasBridge$frag_relabel_state L outer_start.cs_current_bb shadow_in s` >>
  pop_assum kall_tac >> mp_tac (Q.INST [`u0` |-> `shadow_in`] cut_bind) >>
  (impl_tac >- (conj_tac >- (rpt gen_tac >> strip_tac >> simp[] >>
                            irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
                conj_tac >- suspend "prefix" >> suspend "members")) >>
  suspend "result"
QED

Resume abi_decode_cut_complex_from_prefix[prefix]:
  asm_x "cut_ih" kall_tac >>
  map_every qx_gen_tac [`env1`, `sf1`, `ty1`, `tv1`, `live1`, `protected1`,
                        `a`, `v`, `Ga`, `tna`, `da`, `b`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "entry")
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) (qx_choose_then `w`
      (CONJUNCTS_THEN2 (mk_asm "related") assume_tac)))) >>
  asm "entry" (map_every assume_tac o CONJUNCTS) >>
  asm_x "prefix" (fn producer => asm "entry" (mp_tac o MATCH_MP (SPEC_ALL producer))) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `e` (qx_choose_then `sm` (qx_choose_then `sb`
          (map_every assume_tac o CONJUNCTS)))))))))
    (foldr (fn (q,k) => qx_choose_then q k)
      (fn th => mk_asm "normal" th >> map_every assume_tac (CONJUNCTS th))
      [`env2`, `sf2`, `tys2`, `tvs2`, `e`, `sm`, `sb`, `t`, `Gf`, `tnf`]))
  >- suspend "prefix_reject" >> suspend "prefix_normal"
QED

Resume abi_decode_cut_complex_from_prefix[prefix_reject]:
  drule_all_then strip_assume_tac complex_header_straight >>
  `cs_extends sb final` by (irule cs_extends_trans >> qexists `b` >> simp[]) >>
  `(^replay) w sb (Abort Revert_abort t)` by
    (BETA_TAC >> asm "adapter"
       (qspecl_then [`a`, `sb`, `v`, `w`, `Abort Revert_abort t`] mp_tac) >>
     asm "related" (map_every assume_tac o CONJUNCTS) >>
     (impl_tac >- gns[]) >> disch_then ACCEPT_TAC) >>
  `(^replay) shadow_in sb (Abort Revert_abort t)` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_cut_prefix_bind) >> qexists `w` >> gns[]) >>
  disj1_tac >> qexistsl [`t`, `Gf`, `tnf`] >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  qexistsl [`e`, `sm`, `sb`] >> simp[]
QED

Resume abi_decode_cut_complex_from_prefix[prefix_normal]:
  drule_all_then strip_assume_tac complex_header_straight >>
  `cs_extends a sb` by
    (irule cs_extends_trans >> qexists `sm` >> conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`]
       compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb final` by
    (irule cs_extends_trans >> qexists `b` >> simp[] >>
     mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 compile_abi_decode_labels)) >> simp[]) >>
  `(^replay) w sb (OK t)` by
    (BETA_TAC >> asm "adapter" (qspecl_then [`a`, `sb`, `v`, `w`, `OK t`] mp_tac) >>
     asm "related" (map_every assume_tac o CONJUNCTS) >>
     (impl_tac >- gns[]) >> disch_then ACCEPT_TAC) >>
  `(^replay) shadow_in sb (OK t)` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_cut_prefix_bind) >> qexists `w` >> gns[]) >>
  disj2_tac >> qexistsl [`env2`, `sf2`, `tys2`, `tvs2`, `e`, `sm`, `sb`, `t`, `Gf`, `tnf`] >>
  conj_tac >- asm "normal" ACCEPT_TAC >> pop_assum mp_tac >> simp[] >>
  disch_then (qx_choose_then `end_shadow` (map_every assume_tac o CONJUNCTS)) >>
  qexists `end_shadow` >> simp[]
QED

Resume abi_decode_cut_complex_from_prefix[members]:
  asm_x "adapter" kall_tac >> asm_x "prefix" kall_tac >>
  map_every qx_gen_tac [`env1`, `sf1`, `tys0`, `tvs0`, `tys1`, `tvs1`, `live1`,
                        `protected1`, `a`, `b`, `v`, `Ga`, `tna`, `da`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "member_entry")
    (CONJUNCTS_THEN2 (mk_asm "member_span") (qx_choose_then `w`
      (CONJUNCTS_THEN2 (mk_asm "related") assume_tac)))) >>
  asm_x "cut_ih" (fn ih =>
    asm "member_entry" (fn entry => asm "member_span" (fn slice =>
      asm "related" (mp_tac o MATCH_MP (SPEC_ALL ih) o CONJ entry o CONJ slice)))) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (CONJUNCTS_THEN2 (mk_asm "typed_post") assume_tac)))) >>
  `(^replay) shadow_in b r` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_cut_prefix_bind) >> qexists `w` >> simp[]) >>
  qexistsl [`r`, `Gf`, `tnf`] >> conj_tac >- asm "typed_post" ACCEPT_TAC >>
  pop_assum mp_tac >> BETA_TAC >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume abi_decode_cut_complex_from_prefix[result]:
  asm_x "adapter" kall_tac >> asm_x "prefix" kall_tac >> asm_x "cut_ih" kall_tac >>
  `(\u0. ^accept) shadow_in start s` by
    (BETA_TAC >> qexists `shadow_in` >> conj_tac
     >- asm "outer_related" ACCEPT_TAC >> simp[]) >>
  pop_assum (mk_asm "seed" o BETA_RULE) >>
  disch_then (fn producer => asm "outer_entry" (fn entry =>
    asm "outer_span" (fn slice =>
      asm "seed" (mp_tac o MATCH_MP (SPEC_ALL producer) o CONJ entry o CONJ slice)))) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (CONJUNCTS_THEN2 (mk_asm "typed_post") (CONJUNCTS_THEN2
      (mk_asm "ok_mark") (mk_asm "revert_mark")))))) >>
  qexistsl [`r`, `Gf`, `tnf`] >> conj_tac >- asm "typed_post" ACCEPT_TAC >>
  asm "typed_post" (DISJ_CASES_THEN2 (qx_choose_then `t` (assume_tac o CONJUNCT1))
    (qx_choose_then `t` assume_tac) o List.last o CONJUNCTS)
  >- (asm_x "ok_mark" (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `end_shadow` (map_every assume_tac o CONJUNCTS)) >>
      qexists `end_shadow` >> simp[]) >>
  asm_x "revert_mark" (qspec_then `t` mp_tac) >> simp[]
QED

Finalise abi_decode_cut_complex_from_prefix
