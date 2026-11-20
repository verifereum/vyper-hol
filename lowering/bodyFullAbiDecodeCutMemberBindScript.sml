Theory bodyFullAbiDecodeCutMemberBind
Ancestors
  robustCopyTransportPtr exprSimProps exprSimMemoryTransport
  abiCanonicalHeadSize bodyPtrDefs pred_set
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeMemberPrefix valueEncodingTyping
  fragGasOriginPtrLoop fragGasPath fragExec externalEntryShape abiDecodePtrPrims
  abiDecoderMemberInfos abiDecoderCoherence abiEncoder
  compileEnv words list rich_list finite_map bodyFullAbiDecodeCutPath
  exprSimAbiGasBridge abiEncoderObserver relation bodyFullAbiDecodeCutNoncrossing
  exprSimAbiDecodeCompositePrefix abiDecoderReentryPointer abiDecoderVarSequence
  abiDecoderContract loweringShapeRules emitHelperProps venomInstProps
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyFullAbiDecodeCutPathLib

val good = ``Good : compile_state -> venom_state -> bool``;
val bad = ``Bad : venom_state -> bool``;
val span = ``Span : compile_state -> compile_state -> bool``;
val beta = rhs o concl o QCONV (REDEPTH_CONV BETA_CONV);
fun named name vs = valOf (List.find (fn v => fst (dest_var v) = name) vs);
fun append_conj tm extra =
  case total dest_conj tm of
    NONE => mk_conj (tm, extra)
  | SOME (l,r) => mk_conj (l, append_conj r extra);
fun modify_subgoal f tm =
  let val (args,body) = strip_exists tm
  in list_mk_exists (args, f args body) end;

fun marked_motive motive =
  let
    val (args,body) = strip_abs (beta motive)
    val (params,imp) = strip_forall body
    val (entry,post) = dest_imp imp
    val a = named "start" params and b = named "finish" params
    val s = named "s" params
    fun mark_result _ core =
      let val (phys,tail) = dest_conj core
          val (path,outcome) = dest_conj tail
          val (ok,abort) = dest_disj outcome
          val ok' = modify_subgoal (fn (v::_) => fn p => append_conj p ``^good ^b ^v``) ok
          val abort' = modify_subgoal (fn (v::_) => fn p => append_conj p ``^bad ^v``) abort
      in mk_conj (phys, mk_conj (path,mk_disj (ok',abort'))) end
  in
    list_mk_abs (args,list_mk_forall (params,
      mk_imp (append_conj entry ``^span ^a ^b /\ ^good ^a ^s``,
              modify_subgoal mark_result post)))
  end;

val marked_guarded = marked_motive guarded_plus_typed;
val marked_member = marked_motive bounded_complex_plus_typed;
val hereditary_span = ``!a m b. ^span a b /\ cs_extends a m /\ cs_extends m b ==>
                                  ^span a m /\ ^span m b``;

(* Derive both prefix contracts from the frozen public selector statement.
   The cut selector retains one more path before the existing weakening. *)
val raw_prefix = beta (concl abi_decode_member_prefix_joint_observed);
val (prefix_quantifiers,prefix_imp) = strip_forall raw_prefix;
val (prefix_entry,prefix_post) = dest_imp prefix_imp;
val prefix_args = fst (strip_exists prefix_post);
val prefix_select_end = named "select_end" prefix_args;
val prefix_head_start = named "head_start" prefix_args;
val prefix_start = named "start" (free_vars raw_prefix);
val prefix_state = named "s" (free_vars raw_prefix);
val prefix_ctx = named "ctx" (free_vars raw_prefix);
val prefix_finish = named "finish" prefix_quantifiers;
val member_ambient = free_vars bounded_complex_plus_typed;
fun local_prefix_contract tm = list_mk_forall
  (List.filter (fn v => not (List.exists (aconv v) (good::bad::span::member_ambient))) (free_vars tm), tm);
fun map_prefix_outcome f g =
  modify_subgoal (fn _ => fn core =>
    let fun map_final tm =
          case total dest_conj tm of
            NONE => let val (abort,ok) = dest_disj tm
                    in mk_disj (modify_subgoal f abort,modify_subgoal g ok) end
          | SOME (l,r) => mk_conj (l,map_final r)
    in map_final core end) prefix_post;
val marked_prefix = local_prefix_contract (list_mk_forall (prefix_quantifiers,
  mk_imp (mk_conj (prefix_entry, ``^span ^prefix_start ^prefix_finish /\ ^good ^prefix_start ^prefix_state``),
    map_prefix_outcome (fn (v::_) => fn p => append_conj p ``^bad ^v``)
      (fn (v::_) => fn p => append_conj p ``^good ^prefix_head_start ^v``))));
val sliced_prefix = close_statement (list_mk_forall (prefix_quantifiers,
  mk_imp (prefix_entry,
    map_prefix_outcome (fn (v::_) => fn p => append_conj p
      ``!obs. fn_has_code ^prefix_start ^prefix_select_end obs ==>
        gas_path ^prefix_ctx obs ^prefix_state 0 (Abort Revert_abort ^v)``)
      (fn _ => I))));

Theorem abi_decode_member_marked_bind:
  ^hereditary_span /\ ^marked_prefix /\
  ((elems = []) \/
   (?ei asz msz rest. elems = (ei,asz,msz)::rest /\
     (!elem_dst elem_src.
       (^marked_guarded) elem_dst elem_src opc base_op hi ei) /\
     (^marked_member) dst src opc base_op hi rest (ao+asz) (vo+msz))) ==>
  (^marked_member) dst src opc base_op hi elems ao vo
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "hereditary")
    (CONJUNCTS_THEN2 (mk_asm "prefix")
      (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)))
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[abiDecoderSingletonSetupTheory.abi_decode_complex_nil,
          comp_return_def] >>
      `tvs = []` by
        (qpat_assum `LIST_REL _ _ _` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
         qpat_assum `LENGTH pretys = LENGTH pretvs` mp_tac >>
         Cases_on `tys` >> gvs[abi_decoder_member_infos_def] >>
         Cases_on `tvs` >> simp[]) >>
      qexistsl_tac [`OK s`, `G`, `tn`] >> conj_tac
      >- (rpt strip_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
      conj_tac >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
      disj1_tac >> qexists_tac `s` >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "member_entry")
    (CONJUNCTS_THEN2 (mk_asm "contained")
      (CONJUNCTS_THEN2 (mk_asm "input_origin") STRIP_ASSUME_TAC))) >>
  Cases_on `tys`
  >- (asm "member_entry" (mp_tac o cj 3) >> simp[abi_decoder_member_infos_def]) >>
  Cases_on `tvs`
  >- (asm "member_entry" (fn th => mp_tac (CONJUNCT1 th) >>
         mp_tac (CONJUNCT1 (CONJUNCT2 th))) >>
      POP_ASSUM_LIST (K all_tac) >>
      strip_tac >> disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  asm "member_entry" (fn entry =>
    qpat_assum `Span start finish'` (fn span_th =>
      qpat_assum `Good start s` (fn good_th =>
        let
          val static = valOf (List.find (can (match_term ``~ctx_has_dalloca ctx``) o concl)
            (CONJUNCTS entry))
          val selector_entry = PURE_REWRITE_RULE [EQT_INTRO static, AND_CLAUSES] entry
          val marked_entry = CONJ selector_entry (CONJ span_th good_th)
        in
          assume_tac static >> asm "prefix" (mp_tac o C MATCH_MP marked_entry)
        end))) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `(?rstate Gr tnr. _) \/ _`
    (DISJ_CASES_THEN2
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (qexistsl_tac [`Abort Revert_abort rstate`, `Gr`, `tnr`] >> simp[]) >>
  `(^input_origin) u` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     asm "input_origin" assume_tac >> asm "member_entry" (map_every assume_tac o CONJUNCTS) >>
     qexistsl_tac [`s`, `start`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at start x ==> _` drule >> simp[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  asm "member_entry" (mp_tac o cj 3) >>
  qpat_assum `elems = (ei,asz,msz)::rest` (fn th =>
    simp_tac bool_ss [th, abi_decoder_member_infos_def, MAP, CONS_11, pairTheory.PAIR_EQ]) >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  `cs_extends start head_start` by
    (irule cs_extends_trans >> qexists_tac `select_end` >> conj_tac
     >- (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ start = _`
           (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
              (cj 1 compile_getelemptr_abi_labels) (lhs (concl th))))) >> simp[]) >>
     drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
  `cs_extends head_start tail_start` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _`
       (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
          (cj 1 (cj 1 compile_abi_decode_labels)) (lhs (concl th))))) >> simp[]) >>
  `cs_extends tail_start finish'` by
    (qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ tail_start = _`
       (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
          (cj 1 (cj 2 compile_abi_decode_labels)) (lhs (concl th))))) >> simp[]) >>
  `cs_extends head_start finish'` by
    (irule cs_extends_trans >> qexists_tac `tail_start` >> simp[]) >>
  `Span head_start tail_start /\ Span tail_start finish'` by
    (asm "hereditary" (fn th =>
       `Span head_start finish'` by
         (mp_tac (Q.SPECL [`start`, `head_start`, `finish'`] th) >> simp[]) >>
       mp_tac (Q.SPECL [`head_start`, `tail_start`, `finish'`] th)) >> simp[]) >>
  asm "contained" assume_tac >>
  Q_TAC (fn t => SUBGOAL_THEN t
    (mk_asm "head_entry" o CONV_RULE (REDEPTH_CONV BETA_CONV)))
    `(^guarded_to_buf_entry) elem_dst elem_src opc base_op hi
       (type_to_abi_dec_info sf ce ty) env sf ty tv live protected
       head_start tail_start u Gu tnu (d+vo) /\
     (^contained) protected /\ (^input_origin) u /\ Span head_start tail_start /\ Good head_start u`
  >- (rpt (CHANGED_TAC BETA_TAC) >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `!dst src env sf ty tv live protected st fi s G tn d.
    ((abi_decoder_coherent _ _ _ _ _ /\ _) /\ _) ==> _`
    (fn th => asm_x "head_entry" (mp_tac o MATCH_MP th)) >>
  disch_then (qx_choose_then `rh` (qx_choose_then `Gh` (qx_choose_then `tnh`
    (map_every assume_tac o CONJUNCTS)))) >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (rh,Gh,tnh)` by
    (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`, `u`, `tnu`] >> simp[]) >>
  `!obs. fn_has_code start finish' obs ==>
     fn_has_code start head_start obs /\ fn_has_code head_start tail_start obs /\
     fn_has_code tail_start finish' obs` by
    (qx_gen_tac `obs` >> strip_tac >>
     `fn_has_code start head_start obs /\ fn_has_code head_start finish' obs` by
       (irule fn_has_code_split >> simp[]) >>
     simp[] >> irule fn_has_code_split >> simp[]) >>
  `!obs. fn_has_code start finish' obs ==> gas_path ctx obs s 0 rh` by
    (qx_gen_tac `obs` >> strip_tac >>
     qpat_assum `!obs. fn_has_code start finish' obs ==> _ /\ _`
       (qspec_then `obs` (drule_then strip_assume_tac)) >>
     `gas_path ctx obs s 0 (OK u) /\ gas_path ctx obs u 0 rh` by simp[] >>
     drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `(?h. rh = OK h /\ _) \/ _`
    (DISJ_CASES_THEN2
      (qx_choose_then `h` (map_every assume_tac o CONJUNCTS))
      (qx_choose_then `h` (map_every assume_tac o CONJUNCTS)))
  >- suspend "head_success" >>
  qexistsl_tac [`rh`, `Gh`, `tnh`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> qexists_tac `h` >> simp[]
QED

Resume abi_decode_member_marked_bind[head_success]:
  qpat_x_assum `rh = OK h` SUBST_ALL_TAC >>
  qpat_x_assum `!t Gt tnt.
    ((!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) [] (OK t,Gt,tnt)) /\ _) ==> _`
    (qspecl_then [`h`, `Gh`, `tnh`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_entry") (mk_asm "head_frame")) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  qabbrev_tac `saved = mem_bytes_at (d+vo) (type_memory_size tv) h.vs_memory` >>
  `LENGTH saved = type_memory_size tv` by
    (simp[NoAsms, Abbr `saved`, valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
  qpat_x_assum `!env sf pretys pretvs tys tvs live protected st fi s G tn d. _`
    (qspecl_then [`env`, `sf`, `pretys ++ [ty]`, `pretvs ++ [tv]`, `t`, `t'`,
                  `live`, `(d+vo,saved)::protected`, `tail_start`, `finish'`,
                  `h`, `Gh`, `tnh`, `d`] mp_tac) >>
  (impl_tac >- (
    asm_x "tail_entry" (map_every assume_tac o CONJUNCTS) >>
    asm "contained" assume_tac >>
    pure_rewrite_tac[GSYM abi_decoder_member_infos_def] >>
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, all_tac] >>
     rewrite_tac[EVERY_DEF, pairTheory.UNCURRY_DEF] >> BETA_TAC)
    >- (conj_tac >- (
          disj1_tac >> qpat_assum `LENGTH saved = _` SUBST1_TAC >>
          qpat_assum `type_memory_size tv = _` SUBST1_TAC >>
          rewrite_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.LESS_EQ_REFL]) >>
        first_assum ACCEPT_TAC)
    >- (conj_tac >- (
          qpat_assum `LENGTH saved = _` SUBST1_TAC >> simp[NoAsms, Abbr `saved`]) >>
        first_assum ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `LENGTH saved = _` SUBST1_TAC >>
                 conj_tac >> first_assum ACCEPT_TAC) >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r'` (qx_choose_then `G'` (qx_choose_then `tn'`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r'`, `G'`, `tn'`] >>
  conj_tac >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
               qexistsl_tac [`Gh`, `h`, `tnh`] >> simp[]) >>
  conj_tac >- (
    qx_gen_tac `obs` >> strip_tac >>
    qpat_assum `!obs. fn_has_code start finish' obs ==> _ /\ _`
      (qspec_then `obs` (drule_then strip_assume_tac)) >>
    `gas_path ctx obs s 0 (OK h) /\ gas_path ctx obs h 0 r'` by simp[] >>
    drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `(?z. r' = OK z /\ _) \/ _`
    (DISJ_CASES_THEN2 (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) assume_tac)
  >- suspend "tail_success" >>
  disj2_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_member_marked_bind[tail_success]:
  disj1_tac >> qexists_tac `z` >>
  qpat_x_assum `EVERY _ ((d+vo,saved)::protected)`
    (strip_assume_tac o REWRITE_RULE [EVERY_DEF, pairTheory.UNCURRY_DEF]) >>
  (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, all_tac])
  >- (
    `head_start.cs_next_var <= tail_start.cs_next_var` by
      (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _`
        (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
          (cj 1 exprLoweringPropsTheory.ci_mono_compile_abi_decode) (lhs (concl th))))) >>
       simp[exprLoweringPropsTheory.ci_mono_def]) >>
    `start.cs_next_var <= tail_start.cs_next_var` by simp[] >>
    qx_gen_tac `x` >> strip_tac >>
    `not_fresh_at tail_start x` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
    qpat_assum `!x. not_fresh_at tail_start x ==> _`
      (qspec_then `x` (drule_then strip_assume_tac)) >>
    asm "head_frame" (qspec_then `x` (drule_then strip_assume_tac)) >> simp[])
  >- (
    qx_gen_tac `i` >> strip_tac >>
    `i IN tnh.t_mem` by
      (qpat_assum `!i. _ /\ _ /\ i IN tn'.t_mem ==> i IN tnh.t_mem`
        (qspec_then `i` irule) >> asm_rewrite_tac[]) >>
    qpat_assum `tnu.t_mem = tn.t_mem` (fn eq =>
      qpat_assum `!i. _ /\ _ /\ i IN tnh.t_mem ==> i IN tnu.t_mem`
        (qspec_then `i` (irule o REWRITE_RULE [eq]))) >> asm_rewrite_tac[]) >>
  Cases >> rewrite_tac[LENGTH, HD, EL_restricted, rich_listTheory.TAKE, SUM,
                       arithmeticTheory.LESS_MONO_EQ, prim_recTheory.LESS_0,
                       arithmeticTheory.ADD_0]
  >- suspend "saved_member_robust" >>
  rename1 `n < LENGTH t' ==> _` >>
  qpat_assum `!k. k < LENGTH t' ==> _` (qspec_then `n` mp_tac) >>
  qpat_assum `type_memory_size tv = _` (fn eq =>
    rewrite_tac[eq, arithmeticTheory.ADD_ASSOC])
QED

Resume abi_decode_member_marked_bind[saved_member_robust]:
  rpt strip_tac >>
  `mem_bytes_at (d+vo) (type_memory_size tv) z.vs_memory =
     mem_bytes_at (d+vo) (type_memory_size tv) h.vs_memory` by
    (qpat_assum `(\a bs. mem_bytes_at a (LENGTH bs) z.vs_memory = bs) (d+vo) saved`
       (mp_tac o BETA_RULE) >>
     qpat_assum `LENGTH saved = _` (fn eq =>
       simp[NoAsms, eq, Abbr `saved`])) >>
  `val_footprint tv v <= type_memory_size tv` by
    (irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at (d+vo) (val_footprint tv v) z.vs_memory =
     mem_bytes_at (d+vo) (val_footprint tv v) h.vs_memory` by
    (qspecl_then [`d+vo`, `0`, `val_footprint tv v`, `type_memory_size tv`]
       mp_tac mem_bytes_at_window >>
     qpat_x_assum `mem_bytes_at (d+vo) (type_memory_size tv) z.vs_memory = _` mp_tac >>
     qpat_x_assum `val_footprint tv v <= _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  `val_in_memory tv v (d+vo) h.vs_memory` by
    (irule val_in_memory_relocate_footprint >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`z.vs_memory`, `d+vo`] >> once_rewrite_tac[EQ_SYM_EQ] >>
     asm_rewrite_tac[]) >>
  irule robust_val_in_memory_decreasing_taint_transport >> conj_tac
  >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`h.vs_memory`, `z.vs_memory`, `type_memory_size tv`, `d+vo`,
                `tnh.t_mem`, `tn'.t_mem`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, all_tac]
  >- simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `!i. _ /\ _ /\ i IN tn'.t_mem ==> i IN tnh.t_mem`
    (qspec_then `d+vo+i` irule) >> asm_rewrite_tac[] >>
  qpat_x_assum `output_base <= d+vo` mp_tac >>
  qpat_x_assum `d+vo+type_memory_size tv <= output_base+output_cap` mp_tac >>
  qpat_x_assum `i < type_memory_size tv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> numLib.ARITH_TAC
QED

Finalise abi_decode_member_marked_bind

(* A mark records an execution from the original shadow input, not a new
   choice of the ordinary endpoint. Slices stay within the fixed outer cut. *)
val cut_span = ``\a b. cs_extends ready a /\ cs_extends a b /\ cs_extends b outer_finish``;
val cut_cursor = ``^(bodyFullAbiDecodeCutPathLib.shadow_cursor) L outer_start``;
val cut_result = ``\u b r. (^(bodyFullAbiDecodeCutPathLib.shadow_result))
  ctx cut_obs cut L outer_start.cs_current_bb u ((^cut_cursor) b) r``;
val cut_ready = ``\a s u. ~u.vs_halted /\
  (u.vs_current_bb,u.vs_inst_idx) = (^cut_cursor) a /\
  frag_relabel_state L outer_start.cs_current_bb u s``;
val cut_good = ``\b v. (^cut_result) initial_shadow b (OK v)``;
(* A rejected run does not have a normal endpoint cursor. *)
val cut_bad = ``\(v:venom_state). ?w k. frag_relabel_state L outer_start.cs_current_bb w v /\
  run_from k ctx cut_obs initial_shadow = Abort Revert_abort w``;
fun cut_marks tm = beta (subst [good |-> cut_good, bad |-> cut_bad, span |-> cut_span] tm);

Theorem member_cut_span_split[local]:
  ^(cut_marks hereditary_span)
Proof
  rpt strip_tac >> metis_tac[cs_extends_trans]
QED

Theorem member_cut_seed[local]:
  (^cut_ready) a s initial_shadow ==> (^cut_good) a s
Proof
  simp[exec_result_distinct] >> strip_tac >> qexists_tac `initial_shadow` >> simp[]
QED

Theorem member_cut_advance[local]:
  (^cut_good) a s ==> ?u. (^cut_ready) a s u /\
    !b r. (^cut_result) u b r ==> (^cut_result) initial_shadow b r
Proof
  simp[exec_result_distinct] >> strip_tac >> qexists_tac `w` >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_tac >>
  MATCH_MP_TAC (SRULE [] (Q.INST [`cursor` |-> `(^cut_cursor) b`]
    abi_decode_cut_prefix_bind)) >>
  asm_rewrite_tac[]
QED

val member_cut_layout = ``
  cs_extends outer_start ready /\ cs_extends ready outer_finish /\
  outer_start.cs_blocks <> outer_finish.cs_blocks /\
  LENGTH ids = LENGTH outer_start.cs_current_insts /\
  fn_has_code outer_start outer_finish fn /\
  fn_has_code (start_relabel L ids outer_start) (start_swap outer_start L ids outer_finish)
    (frag_relabel_observer outer_start outer_finish L ids fn obs_id) /\
  frag_ops_free outer_start outer_finish /\ L <> outer_finish.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks outer_start outer_finish)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code outer_start outer_finish) /\
  cut_obs = frag_relabel_observer outer_start outer_finish L ids fn obs_id /\
  cut = frag_observer_cut outer_finish``;
val straight_opcodes = ``EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
                                       ~is_terminator i.inst_opcode)``;
val slice_straight = ``\a b. a.cs_blocks = outer_start.cs_blocks ==>
  b.cs_blocks = outer_start.cs_blocks /\ (^straight_opcodes) (emitted_insts a b)``;
val slice_outcome = ``\b r.
  (?v. r = OK v /\ ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
       v.vs_inst_idx = LENGTH b.cs_current_insts) \/ (?v. r = Abort Revert_abort v)``;

Theorem member_cut_slice_selected[local]:
  ^member_cut_layout /\ (^cut_span) a b /\ (^cut_ready) a s u /\
  (^slice_straight) a b /\ (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
  (^slice_outcome) b r ==> (^cut_result) u b r
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends outer_start a` by metis_tac[cs_extends_trans] >>
  mp_tac (BETA_RULE (Q.INST [`Q` |-> `\p g tn. p = r`,
    `start` |-> `outer_start`, `final` |-> `outer_finish`, `id` |-> `obs_id`]
    abi_decode_cut_noncrossing_selected)) >>
  gvs[]
QED

Theorem member_cut_select_shape[local]:
  compile_getelemptr_abi src dyn ao MLOAD base_op hi a = (ep,b) ==>
  cs_extends a b /\ b.cs_blocks = a.cs_blocks /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  (^straight_opcodes) (emitted_insts a b)
Proof
  strip_tac >> drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  drule abi_decoder_member_pointer_code >> simp[abi_decode_source_opcode_def] >>
  strip_tac >>
  gvs[inst_extends_def, cs_extends_def, EVERY_MEM, abi_decoder_reentry_opcode_def] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem member_cut_add_shape[local]:
  emit_op ADD [dst;Lit (n2w vo)] b = (dp,c) ==>
  cs_extends b c /\ c.cs_blocks = b.cs_blocks /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c /\
  (^straight_opcodes) (emitted_insts b c)
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  drule emitted_insts_emit_op >>
  simp[cs_extends_def, mk_inst_def, is_terminator_def]
QED

Theorem member_cut_marked_prefix[local]:
  ^member_cut_layout /\ ^sliced_prefix ==> ^(cut_marks marked_prefix)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "layout") (mk_asm "selector")) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "entry")
    (CONJUNCTS_THEN2 (mk_asm "span") (mk_asm "mark"))) >>
  asm "entry" (fn th => asm "selector" (mp_tac o C MATCH_MP th)) >>
  disch_then (qspecl_then [`PG`,`explicit`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  rename [`emit_op ADD [dst;Lit (n2w vo)] select_end = (elem_dst,head_start)`,
          `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ tail_start = ((),finish')`] >>
  `opc = MLOAD` by (asm "entry" (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  drule member_cut_select_shape >> strip_tac >>
  drule member_cut_add_shape >> strip_tac >>
  `cs_extends head_start tail_start` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _`
       (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
          (cj 1 (cj 1 compile_abi_decode_labels)) (lhs (concl th))))) >> simp[]) >>
  `cs_extends tail_start finish'` by
    (qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ tail_start = _`
       (fn th => mp_tac (REWRITE_RULE [th] (PART_MATCH (rand o rand)
          (cj 1 (cj 2 compile_abi_decode_labels)) (lhs (concl th))))) >> simp[]) >>
  `(^cut_span) start select_end /\ (^cut_span) start head_start` by
    (BETA_TAC >> asm "span" (strip_assume_tac o BETA_RULE) >>
     POP_ASSUM_LIST (fn ths => metis_tac (cs_extends_trans ::
       List.filter (can (match_term ``cs_extends a b``) o concl) ths))) >>
  (`(^slice_straight) start select_end /\ (^slice_straight) start head_start` by
    (simp[] >> strip_tac >>
     drule_all exprLoweringPropsTheory.emitted_insts_append >> simp[EVERY_APPEND])) >>
  asm "mark" (mp_tac o MATCH_MP (BETA_RULE member_cut_advance)) >>
  disch_then (qx_choose_then `shadow` (CONJUNCTS_THEN2 assume_tac (mk_asm "advance"))) >>
  qexistsl_tac [`elem_src`,`elem_dst`,`select_end`,`head_start`,`tail_start`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?rstate Gr tnr. _) \/ _`
    (DISJ_CASES_THEN2
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- suspend "reject" >>
  suspend "success"
QED

Resume member_cut_marked_prefix[reject]:
  disj1_tac >> qexistsl_tac [`rstate`,`Gr`,`tnr`] >> asm_rewrite_tac[] >>
  asm "advance" (qspecl_then [`select_end`,`Abort Revert_abort rstate`] mp_tac) >>
  (impl_tac >-
    ((irule (BETA_RULE member_cut_slice_selected) >> simp[] >>
     qexistsl [`start`,`fn`,`ids`,`obs_id`,`outer_finish`,`ready`,`s`] >>
     asm "layout" (map_every assume_tac o CONJUNCTS) >> simp[] >> (gvs[BETA_RULE member_cut_slice_selected])))) >>
  simp[exec_result_distinct]
QED

Resume member_cut_marked_prefix[success]:
  `(^cut_good) head_start u` by
    (BETA_TAC >>
     asm "advance" (qspecl_then [`head_start`,`OK u`] irule) >>
     MATCH_MP_TAC (BETA_RULE (Q.INST [`a` |-> `start`, `s` |-> `s`,
      `ready` |-> `ready`, `outer_finish` |-> `outer_finish`, `ids` |-> `ids`,
      `fn` |-> `fn`, `obs_id` |-> `obs_id`] member_cut_slice_selected)) >>
     asm "layout" (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `(^cut_span) start head_start` (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
     qpat_assum `(^slice_straight) start head_start` (assume_tac o BETA_RULE) >>
     qpat_assum `~shadow.vs_halted /\ _` (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, all_tac] >>
     disj1_tac >> qexists `u` >> rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  disj2_tac >> qexistsl_tac [`u`,`Gu`,`tnu`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise member_cut_marked_prefix

val crosses_cut = ``\a b. a.cs_blocks = outer_start.cs_blocks /\
  b.cs_blocks <> outer_start.cs_blocks``;

(* The primitive selector is lifted separately above. Only actual recursive
   compiler calls need this noncrossing replay interface. *)
val member_child_replay = ``
  !a b s u r dst' src' input' hi'.
    (^cut_span) a b /\ ~(^crosses_cut) a b /\ hi' <> Lit 0w /\
    ((?ei. compile_abi_decode_to_buf dst' src' MLOAD (Var input') hi' ei a = ((),b)) \/
     (?rest ao' vo'. compile_abi_decode_complex_elems dst' src' MLOAD
         (Var input') hi' rest ao' vo' a = ((),b))) /\
    (^cut_ready) a s u /\ (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
    (^slice_outcome) b r ==> (^cut_result) u b r``;

fun cut_motive crossing motive =
  let
    val (args,body) = strip_abs (beta motive)
    val (params,imp) = strip_forall body
    val (entry,post) = dest_imp imp
    val a = named "start" params and b = named "finish" params
    val s = named "s" params
    val u = variant (params @ free_vars body) ``shadow:venom_state``
    val related = ``(^cut_ready) ^a ^s ^u``
    val guard = if crossing then ``(^crosses_cut) ^a ^b /\ ^related`` else related
    val extended = bodyFullAbiDecodeCutPathLib.extend_post post ``\r. (^cut_result) ^u ^b r``
  in
    list_mk_abs (args,list_mk_forall (params @ [u],
      mk_imp (mk_conj (entry, ``(^cut_span) ^a ^b /\ ^guard``), extended)))
  end;

val crossing_head = cut_motive true guarded_plus_typed;
val crossing_tail = cut_motive true bounded_complex_plus_typed;
val cut_member = cut_motive false bounded_complex_plus_typed;

(* Introduce the marked version of a post using the existing witnesses.
   Flatten only the branch's outer conjunction, never the typed predicates. *)
val introduce_child_marks =
  qexistsl [`r`, `Gf`, `tnf`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  asm_x "outcome" (DISJ_CASES_THEN2
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS))
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> qexists `v` >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, asm "replay" mp_tac >> simp[exec_result_distinct]]) >>
  disj2_tac >> qexists `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  asm "replay" mp_tac >> simp[exec_result_distinct];

(* The old entry keeps its own conjunction shape when we separate the
   slice and the seed mark appended by marked_motive. *)
val split_marked_entry =
  disch_then (CONJUNCTS_THEN2 (mk_asm "old_entry")
    (CONJUNCTS_THEN2 (mk_asm "contained")
      (CONJUNCTS_THEN2 (mk_asm "origin")
        (CONJUNCTS_THEN2 (mk_asm "child_span") (mk_asm "seed"))))) >>
  asm_x "old_entry" (fn entry => asm_x "contained" (fn contained =>
    asm_x "origin" (mk_asm "child_entry" o CONJ entry o CONJ contained))) >>
  asm_x "seed" (mp_tac o MATCH_MP (BETA_RULE member_cut_advance)) >>
  disch_then (qx_choose_then `child_shadow`
    (CONJUNCTS_THEN2 (mk_asm "child_related") (mk_asm "advance")));

fun take_selected ttac =
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf` ttac)));
val split_child_post = CONJUNCTS_THEN2 assume_tac
  (CONJUNCTS_THEN2 (mk_asm "observer_path") (mk_asm "outcome"));

val mark_crossing_child =
  asm_x "crossing" (fn producer => asm "child_entry" (fn entry =>
    asm "child_span" (fn span => asm "crosses" (fn crossing =>
      asm "child_related" (mp_tac o MATCH_MP (SPEC_ALL producer) o
        CONJ entry o CONJ span o CONJ crossing))))) >>
  take_selected (CONJUNCTS_THEN2 split_child_post (mk_asm "child_replay")) >>
  asm "child_replay" (fn replay => asm "advance"
    (qspecl_then [`b`,`r`] (mk_asm "replay" o C MATCH_MP replay))) >>
  asm "observer_path" assume_tac >> introduce_child_marks;

fun mark_noncrossing_child operands child_call =
  asm_x "ordinary" (fn producer => asm "child_entry"
    (mp_tac o MATCH_MP (SPEC_ALL (BETA_RULE producer)))) >>
  take_selected split_child_post >>
  `(^slice_outcome) b r` by
    (BETA_TAC >> asm "outcome" (DISJ_CASES_THEN2
       (qx_choose_then `v` (map_every assume_tac o CONJUNCTS))
       (qx_choose_then `v` assume_tac))
     >- (disj1_tac >> qexists `v` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qexists `v` >> first_assum ACCEPT_TAC) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `(^cut_result) child_shadow b r` by
    (BETA_TAC >> asm "adapter"
       (qspecl_then ([`a`,`b`,`child_in`,`child_shadow`,`r`] @ operands) MATCH_MP_TAC) >>
     asm "child_entry" (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- asm "child_span" ACCEPT_TAC >>
     conj_tac >- asm "noncrossing" ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `opc = MLOAD` SUBST_ALL_TAC >>
                  qpat_assum `base_op = Var input` SUBST_ALL_TAC >> child_call) >>
     conj_tac >- asm "child_related" ACCEPT_TAC >>
     conj_tac >- asm "observer_path" ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  pop_assum (mk_asm "child_replay" o BETA_RULE) >>
  asm "child_replay" (fn replay => asm "advance"
    (qspecl_then [`b`,`r`] (mk_asm "replay" o C MATCH_MP replay))) >>
  asm "observer_path" assume_tac >> introduce_child_marks;

Theorem abi_decode_cut_member_from_prefix:
  ^sliced_prefix ==>
  ^member_cut_layout /\ ^member_child_replay /\
  ((elems = []) \/
   (?ei asz msz rest. elems = (ei,asz,msz)::rest /\
     (!elem_dst elem_src.
       (^guarded_plus_typed) elem_dst elem_src opc base_op hi ei /\
       (^crossing_head) elem_dst elem_src opc base_op hi ei) /\
     (^bounded_complex_plus_typed) dst src opc base_op hi rest (ao+asz) (vo+msz) /\
     (^crossing_tail) dst src opc base_op hi rest (ao+asz) (vo+msz))) ==>
  (^cut_member) dst src opc base_op hi elems ao vo
Proof
  BETA_TAC >> disch_then (mk_asm "selector") >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "layout")
    (CONJUNCTS_THEN2 (mk_asm "adapter") (mk_asm "children"))) >>
  map_every qx_gen_tac [`env`,`sf`,`pretys`,`pretvs`,`tys`,`tvs`,`live`,`protected`,
                       `start`,`member_end`,`s`,`G`,`tn`,`d`,`shadow`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "entry")
    (CONJUNCTS_THEN2 (mk_asm "span") (mk_asm "related"))) >>
  let
    val th = Q.INST [`initial_shadow` |-> `shadow`]
      (BETA_RULE (INST [good |-> cut_good,bad |-> cut_bad,span |-> cut_span]
        abi_decode_member_marked_bind))
  in
    mp_tac th
  end >>
  (impl_tac >- (
    conj_tac >- MATCH_ACCEPT_TAC (BETA_RULE member_cut_span_split) >>
    conj_tac >- (
      MATCH_MP_TAC (BETA_RULE (Q.INST [`initial_shadow` |-> `shadow`]
        member_cut_marked_prefix)) >>
      conj_tac >- asm "layout" ACCEPT_TAC >> asm "selector" ACCEPT_TAC) >>
    asm "children" (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th)
      (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 (mk_asm "heads")
          (CONJUNCTS_THEN2 (mk_asm "tail") (mk_asm "crossing_tail")))))) >>
    disj2_tac >> qexistsl [`ei`, `asz`, `msz`, `rest`] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- suspend "head" >> suspend "tail")) >>
  suspend "result"
QED

Resume abi_decode_cut_member_from_prefix[head]:
  map_every qx_gen_tac [`elem_dst`,`elem_src`] >>
  asm "heads" (qspecl_then [`elem_dst`,`elem_src`]
    (CONJUNCTS_THEN2 (mk_asm "ordinary") (mk_asm "crossing"))) >>
  map_every qx_gen_tac [`env1`,`sf1`,`ty1`,`tv1`,`live1`,`protected1`,`a`,`b`,
                       `child_in`,`Ga`,`tna`,`da`] >>
  split_marked_entry >>
  Q_TAC ASM_CASES_TAC `(^crosses_cut) a b`
  >- (pop_assum (mk_asm "crosses" o BETA_RULE) >> mark_crossing_child) >>
  pop_assum (mk_asm "noncrossing" o BETA_RULE) >>
  mark_noncrossing_child [`elem_dst`,`elem_src`,`input`,`hi`]
    (disj1_tac >> qexists `ei` >> asm_rewrite_tac[])
QED

Resume abi_decode_cut_member_from_prefix[tail]:
  map_every qx_gen_tac [`env1`,`sf1`,`pretys1`,`pretvs1`,`tys1`,`tvs1`,`live1`,
                       `protected1`,`a`,`b`,`child_in`,`Ga`,`tna`,`da`] >>
  asm "tail" (mk_asm "ordinary") >> asm "crossing_tail" (mk_asm "crossing") >>
  split_marked_entry >>
  Q_TAC ASM_CASES_TAC `(^crosses_cut) a b`
  >- (pop_assum (mk_asm "crosses" o BETA_RULE) >> mark_crossing_child) >>
  pop_assum (mk_asm "noncrossing" o BETA_RULE) >>
  mark_noncrossing_child [`dst`,`src`,`input`,`hi`]
    (disj2_tac >> qexistsl [`rest`,`ao+asz`,`vo+msz`] >> asm_rewrite_tac[])
QED

Resume abi_decode_cut_member_from_prefix[result]:
  `(^cut_result) shadow start (OK s)` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE member_cut_seed) >> asm "related" ACCEPT_TAC) >>
  pop_assum (mk_asm "seed" o BETA_RULE) >>
  disch_then (mk_asm "member_producer") >>
  asm "entry" (CONJUNCTS_THEN2 (mk_asm "unmarked_entry")
    (CONJUNCTS_THEN2 (mk_asm "contained") (mk_asm "input_origin"))) >>
  asm_x "member_producer" (fn producer =>
    asm "unmarked_entry" (fn entry => asm "contained" (fn contained =>
      asm "input_origin" (fn origin => asm "span" (fn span =>
        asm "seed" (mp_tac o MATCH_MP (SPEC_ALL producer) o
          CONJ entry o CONJ contained o CONJ origin o CONJ span)))))) >>
  take_selected split_child_post >> asm "observer_path" assume_tac >>
  qexistsl [`r`,`Gf`,`tnf`] >>
  asm_x "outcome" (DISJ_CASES_THEN2
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS))
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)))
  >- (conj_tac
      >- (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >> disj1_tac >>
          qexists `v` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
      qexists `v` >> first_assum ACCEPT_TAC) >>
  simp[exec_result_distinct]
QED

Finalise abi_decode_cut_member_from_prefix
