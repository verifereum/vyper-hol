Theory bodyAbiDecodeGuardedMemberBindMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeMemberPrefix
  bodyFullAbiDecodeInputOrigin robustCopyTransportPtr exprSimMemoryTransport
  abiDecoderMemberInfos abiDecoderCoherence externalEntryShape exprSimAccounts
  exprSimProps abiCanonicalHeadSize
  valueEncodingTyping valueEncodingProps fragGasOriginPtrLoop fragExec fragGasPath
  abiEncoder compileEnv words list rich_list finite_map pred_set
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyFullAbiDecodeCutPathLib bodyAbiDecodeGuardedEffectSyntaxLib

val member_effect = decorate_motive bounded_complex_plus_typed;
val head_effect = guarded_effect_motive_typed ();
val interval = ``MemberSpan : compile_state -> compile_state -> bool``;
val mark = ``M : compile_state -> exec_result -> bool``;
val split_interval = ``!a m b. ^interval a b /\ cs_extends a m /\ cs_extends m b ==>
  ^interval a m /\ ^interval m b``;
val abort_mark = ``!a b w. ^mark a (Abort Revert_abort w) ==> ^mark b (Abort Revert_abort w)``;

fun mark_motive motive =
  let
    val (args, body) = strip_abs motive
    val (ps, imp) = strip_forall body
    val (entry, post) = dest_imp imp
    val a = param ps "start" and b = param ps "finish" and s = param ps "s"
  in
    list_mk_abs (args, list_mk_forall (ps, mk_imp
      (``^entry /\ ^interval ^a ^b /\ ^mark ^a (OK ^s)``,
       extend_post post ``\r. ^mark ^b r``)))
  end;
val marked_head = mark_motive head_effect;
val marked_members = mark_motive member_effect;

(* The marked callback is the retained slice packet, with the member
   motive's ambient variables shared with the caller. *)
val prefix_slice = beta (concl abi_decode_member_prefix_joint_observed_slice);
val (prefix_ps, prefix_imp) = strip_forall prefix_slice;
val (prefix_entry, prefix_post) = dest_imp prefix_imp;
val prefix_s = param (free_vars prefix_slice) "s";
val prefix_tn = param (free_vars prefix_slice) "tn";
val prefix_start = param (free_vars prefix_slice) "start";
val prefix_finish = param prefix_ps "finish";
val (prefix_ws, prefix_body) = strip_exists prefix_post;
val prefix_fields = strip_conj prefix_body;
val (prefix_abort, prefix_normal) = dest_disj (List.last prefix_fields);
val (prefix_rs, prefix_abort_body) = strip_exists prefix_abort;
val (prefix_us, prefix_normal_body) = strip_exists prefix_normal;
val prefix_u = param prefix_us "u";
val prefix_tnu = param prefix_us "tnu";
val prefix_reject = param prefix_rs "rstate";
val select_end = param prefix_ws "select_end";
val head_start = param prefix_ws "head_start";
val prefix_effect = checked "member prefix slice" prefix_slice
  (list_mk_forall (prefix_ps, mk_imp (prefix_entry,
    list_mk_exists (prefix_ws, list_mk_conj
      (List.take (prefix_fields, length prefix_fields - 1) @
       [mk_disj (prefix_abort, list_mk_exists (prefix_us,
          mk_conj (prefix_normal_body, effect prefix_s prefix_tn prefix_u prefix_tnu)))])))));
val marked_prefix =
  let
    val (_, imp) = strip_forall prefix_effect
    val (_, post) = dest_imp imp
    val (_, body) = strip_exists post
    val fields = strip_conj body
    val (_, normal) = dest_disj (List.last fields)
    val (_, success) = strip_exists normal
    val reject = list_mk_exists (prefix_rs,
      ``^prefix_abort_body /\ ^mark ^select_end (Abort Revert_abort ^prefix_reject)``)
    val normal' = list_mk_exists (prefix_us, ``^success /\ ^mark ^head_start (OK ^prefix_u)``)
    val tm = list_mk_forall (prefix_ps, mk_imp
      (``^prefix_entry /\ ^interval ^prefix_start ^prefix_finish /\ ^mark ^prefix_start (OK ^prefix_s)``,
       list_mk_exists (prefix_ws, list_mk_conj
         (List.take (fields, length fields - 1) @ [mk_disj (reject,normal')]))))
  in list_mk_forall
       (List.filter (fn v => not (List.exists (aconv v) (interval::mark::free_vars member_effect)))
          (free_vars tm), tm)
  end;

val fields_tac = map_every assume_tac o CONJUNCTS;
val open_packet = REPEAT_TCL CHOOSE_THEN fields_tac;

(* The mark carries the selected result across cuts. Normal ghost effects
   stay in the outcome and compose only after all three phases succeed. *)
Theorem abi_decode_guarded_member_cons_bind_mods:
  ^split_interval /\ ^abort_mark /\ ^marked_prefix /\
  elems = (ei,asz,msz)::rest /\
  (!elem_dst elem_src. (^marked_head) elem_dst elem_src opc base_op hi ei) /\
  (^marked_members) dst src opc base_op hi rest (ao+asz) (vo+msz) ==>
  (^marked_members) dst src opc base_op hi elems ao vo
Proof
  CONV_TAC beta_conv >> disch_then (CONJUNCTS_THEN2 (mk_asm "split")
    (CONJUNCTS_THEN2 (mk_asm "abort")
      (CONJUNCTS_THEN2 (mk_asm "prefix")
        (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "head") (mk_asm "tail")))))) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (mk_asm "entry") (CONJUNCTS_THEN2 (mk_asm "contained") (mk_asm "input_origin")))
    fields_tac) >>
  Cases_on `tys`
  >- (asm "entry" (mp_tac o cj 3) >> simp[abi_decoder_member_infos_def]) >>
  Cases_on `tvs`
  >- (asm "entry" (fn th => mp_tac (cj 1 th) >> mp_tac (cj 2 th)) >>
      simp[LIST_REL_APPEND_EQ]) >>
  rename1 `LIST_REL (abi_decoder_coherent ce env sf) (pretys ++ ty::tys) (pretvs ++ tv::tvs)` >>
  Q_TAC (fn t => SUBGOAL_THEN t (fn th => asm_x "prefix" (open_packet o C MATCH_MP th)))
    `^(subst [prefix_finish |-> ``finish':compile_state``] prefix_entry) /\
     MemberSpan start finish' /\ M start (OK s)`
  >- (conj_tac >- asm "entry" ACCEPT_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?rstate Gr tnr. _) \/ _`
    (DISJ_CASES_THEN2 open_packet open_packet)
  >- (qexistsl [`Abort Revert_abort rstate`, `Gr`, `tnr`] >>
      reverse conj_tac >- (asm "abort" (drule_then irule) >> simp[]) >>
      simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "prefix_success"
QED

Resume abi_decode_guarded_member_cons_bind_mods[prefix_success]:
  `(^input_origin) u` by
    (CONV_TAC beta_conv >> irule abi_decode_input_origin_transport >>
     asm "input_origin" assume_tac >> asm "entry" fields_tac >>
     qexistsl [`s`, `start`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at start x ==> _` drule >> simp[]) >>
  pop_assum (assume_tac o CONV_RULE beta_conv) >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  asm "entry" (mp_tac o cj 3) >>
  qpat_assum `elems = (ei,asz,msz)::rest` (fn th =>
    simp_tac bool_ss [th,abi_decoder_member_infos_def,MAP,CONS_11,pairTheory.PAIR_EQ]) >>
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
  `MemberSpan head_start tail_start /\ MemberSpan tail_start finish'` by
    (asm "split" (fn th =>
       `MemberSpan head_start finish'` by
         (mp_tac (Q.SPECL [`start`, `head_start`, `finish'`] th) >> simp[]) >>
       mp_tac (Q.SPECL [`head_start`, `tail_start`, `finish'`] th)) >> simp[]) >>
  asm "contained" assume_tac >>
  Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "head_entry" o CONV_RULE beta_conv))
    `((^guarded_to_buf_entry) elem_dst elem_src opc base_op hi
       (type_to_abi_dec_info sf ce ty) env sf ty tv live protected
       head_start tail_start u Gu tnu (d+vo) /\
      (^contained) protected /\ (^input_origin) u) /\
     MemberSpan head_start tail_start /\ M head_start (OK u)`
  >- (CONV_TAC beta_conv >> asm_rewrite_tac[] >> simp[]) >>
  asm_x "head_entry" (fn ent => asm_x "head" (mp_tac o C MATCH_MP ent)) >>
  disch_then (qx_choose_then `rh` (qx_choose_then `Gh` (qx_choose_then `tnh` fields_tac))) >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (rh,Gh,tnh)` by
    (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`Gu`, `u`, `tnu`] >> simp[]) >>
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
  qpat_x_assum `(?h. (rh = OK h /\ _) /\ _) \/ _`
    (DISJ_CASES_THEN2 open_packet open_packet)
  >- suspend "head_success" >>
  qexistsl [`rh`, `Gh`, `tnh`] >>
  reverse conj_tac
  >- (qpat_assum `rh = Abort Revert_abort t` (fn eq =>
        rewrite_tac[eq] >> qpat_assum `M tail_start rh`
          (fn m => asm "abort" (irule o C MATCH_MP (REWRITE_RULE[eq] m))))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> qexists_tac `t` >> first_assum ACCEPT_TAC
QED

Resume abi_decode_guarded_member_cons_bind_mods[head_success]:
  rename1 `rh = OK h` >> qpat_x_assum `rh = OK h` SUBST_ALL_TAC >>
  qpat_x_assum `!t Gt tnt.
    ((!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) [] (OK t,Gt,tnt)) /\ _) ==> _`
    (qspecl_then [`h`, `Gh`, `tnh`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_entry") (mk_asm "head_frame")) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  qabbrev_tac `saved = mem_bytes_at (d+vo) (type_memory_size tv) h.vs_memory` >>
  `LENGTH saved = type_memory_size tv` by
    (simp[NoAsms, Abbr `saved`, valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
  asm_x "tail" (qspecl_then [`env`, `sf`, `pretys ++ [ty]`, `pretvs ++ [tv]`, `tys`, `tvs`,
                  `live`, `(d+vo,saved)::protected`, `tail_start`, `finish'`,
                  `h`, `Gh`, `tnh`, `d`] mp_tac) >>
  (impl_tac >- (
    asm_x "tail_entry" fields_tac >>
    pure_rewrite_tac[GSYM abi_decoder_member_infos_def] >>
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, all_tac] >>
     rewrite_tac[EVERY_DEF, pairTheory.UNCURRY_DEF] >> CONV_TAC beta_conv)
    >- (conj_tac >- (
          disj1_tac >> qpat_assum `LENGTH saved = _` SUBST1_TAC >>
          qpat_assum `type_memory_size tv = _` SUBST1_TAC >>
          rewrite_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.LESS_EQ_REFL]) >>
        first_assum ACCEPT_TAC)
    >- (conj_tac >- (
          qpat_assum `LENGTH saved = _` SUBST1_TAC >> simp[NoAsms, Abbr `saved`]) >>
        first_assum ACCEPT_TAC) >>
    qpat_assum `LENGTH saved = _` SUBST1_TAC >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r'` (qx_choose_then `G'` (qx_choose_then `tn'` fields_tac))) >>
  qexistsl [`r'`, `G'`, `tn'`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
               qexistsl [`Gh`, `h`, `tnh`] >> simp[]) >>
  conj_tac >- (
    qx_gen_tac `obs` >> strip_tac >>
    qpat_assum `!obs. fn_has_code start finish' obs ==> _ /\ _`
      (qspec_then `obs` (drule_then strip_assume_tac)) >>
    `gas_path ctx obs s 0 (OK h) /\ gas_path ctx obs h 0 r'` by simp[] >>
    drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `(?z. (r' = OK z /\ _) /\ _) \/ _`
    (DISJ_CASES_THEN2 open_packet assume_tac)
  >- suspend "tail_success" >>
  disj2_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_guarded_member_cons_bind_mods[tail_success]:
  rename1 `r' = OK z` >> disj1_tac >> qexists_tac `z` >>
  qpat_x_assum `EVERY _ ((d+vo,saved)::protected)`
    (fields_tac o REWRITE_RULE [EVERY_DEF, pairTheory.UNCURRY_DEF]) >>
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
        (qspec_then `i` (irule o REWRITE_RULE [eq]))) >> asm_rewrite_tac[])
  >- (Cases >> rewrite_tac[LENGTH, HD, EL_restricted, rich_listTheory.TAKE, SUM,
                       arithmeticTheory.LESS_MONO_EQ, prim_recTheory.LESS_0,
                       arithmeticTheory.ADD_0]
      >- suspend "saved_member_robust" >>
      rename1 `n < LENGTH tvs ==> _` >>
      qpat_assum `!k. k < LENGTH tvs ==> _` (qspec_then `n` mp_tac) >>
      qpat_assum `type_memory_size tv = _` (fn eq =>
        rewrite_tac[eq, arithmeticTheory.ADD_ASSOC])) >>
  `abi_decode_guarded_effect_core s tn h tnh` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnu`, `u`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnh`, `h`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_guarded_member_cons_bind_mods[saved_member_robust]:
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
     qpat_assum `mem_bytes_at (d+vo) (type_memory_size tv) z.vs_memory = _` mp_tac >>
     qpat_assum `val_footprint tv v <= _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  `val_in_memory tv v (d+vo) h.vs_memory` by
    (irule val_in_memory_relocate_footprint >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qexistsl [`z.vs_memory`, `d+vo`] >> once_rewrite_tac[EQ_SYM_EQ] >>
     asm_rewrite_tac[]) >>
  irule robust_val_in_memory_decreasing_taint_transport >> conj_tac
  >- first_assum ACCEPT_TAC >>
  qexistsl [`h.vs_memory`, `z.vs_memory`, `type_memory_size tv`, `d+vo`,
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

Finalise abi_decode_guarded_member_cons_bind_mods
