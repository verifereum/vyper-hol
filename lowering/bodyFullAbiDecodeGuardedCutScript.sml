Theory bodyFullAbiDecodeGuardedCut
Ancestors
  bodyFullAbiDecodeRecursive bodyFullAbiDecodeCutLoop bodyFullAbiDecodeCutArray
  bodyFullAbiDecodeCutMember bodyFullAbiDecodeCutNoncrossing
  bodyFullAbiDecodeCutStraightSlice bodyFullAbiDecodeCutPath
  abiDecoderClampedWord abiDecoderBytesPhases abiDecoderContract abiEncoder
Libs
  bodyFullAbiDecodeLoopObservedSyntaxLib bodyFullAbiDecodeRuntimeLoopLengthObservedLib
  bodyFullAbiDecodeCutArraySyntaxLib bodyFullAbiDecodeCutPathLib

val cut_fn = ``frag_relabel_observer cut_start cut_finish L ids fn id``;
val cut_pos = ``frag_observer_cut cut_finish``;
val outer_layout = ``
  cs_extends cut_start cut_ready /\
  cut_start.cs_blocks <> cut_finish.cs_blocks /\
  LENGTH ids = LENGTH cut_start.cs_current_insts /\
  fn_has_code cut_start cut_finish fn /\
  fn_has_code (start_relabel L ids cut_start) (start_swap cut_start L ids cut_finish) ^cut_fn /\
  frag_ops_free cut_start cut_finish /\ L <> cut_finish.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks cut_start cut_finish)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code cut_start cut_finish)``;
val span = ``\a b. cs_extends cut_ready a /\ cs_extends a b /\ cs_extends b cut_finish``;
val crosses = ``\a b. a.cs_blocks = cut_start.cs_blocks /\ b.cs_blocks <> cut_start.cs_blocks``;
val related = ``\a s u. ~u.vs_halted /\
  (u.vs_current_bb,u.vs_inst_idx) = (^shadow_cursor) L cut_start a /\
  frag_relabel_state L cut_start.cs_current_bb u s``;
val replay = ``\u b r. (^shadow_result) ctx ^cut_fn ^cut_pos L cut_start.cs_current_bb u
  ((^shadow_cursor) L cut_start b) r``;
val endpoints = ``\b r.
  (?v. r = OK v /\ ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
       v.vs_inst_idx = LENGTH b.cs_current_insts) \/ (?v. r = Abort Revert_abort v)``;
val straight = ``\a b. a.cs_blocks = cut_start.cs_blocks ==>
  b.cs_blocks = cut_start.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
              ~is_terminator i.inst_opcode) (emitted_insts a b)``;

fun beta t = rhs (concl (QCONV (REDEPTH_CONV BETA_CONV) t));
fun normalize th = CONV_RULE (REDEPTH_CONV BETA_CONV THENC
  REWRITE_CONV [GSYM CONJ_ASSOC]) th;
val norm_tac = CONV_TAC (REDEPTH_CONV BETA_CONV THENC REWRITE_CONV [GSYM CONJ_ASSOC]);
fun by_name name = List.find (fn v => fst (dest_var v) = name);
fun param params name = valOf (by_name name params);

(* Keep the original entries and strengthen only the selected post. *)
fun crossing_motive old =
  let
    val (args, body) = strip_abs (beta old)
    val (params, imp) = strip_forall body
    val (entry, post) = dest_imp imp
    val a = param params "start" and b = param params "finish" and s = param params "s"
    val u = variant (params @ free_vars body) ``shadow_in:venom_state``
  in
    list_mk_abs (args, list_mk_forall (params @ [u],
      mk_imp (``^entry /\ (^span) ^a ^b /\ (^crosses) ^a ^b /\ (^related) ^a ^s ^u``,
        extend_post post ``\r. (^replay) ^u ^b r``)))
  end;
val guarded_cut = crossing_motive guarded_plus_typed;
val members_cut = crossing_motive bounded_complex_plus_typed;

(* These two fixed-observer parameters are free in the array and loop APIs. *)
fun fix_observer t =
  let val vars = free_vars t
  in subst [param vars "cut_observer" |-> cut_fn, param vars "cut" |-> cut_pos] t end;
val loop_cut = fix_observer (specialize_array_cut
  (decorate_array_motive repaired_loop_length_plus_typed));
val cut_ind = ISPECL [guarded_cut, members_cut, loop_cut]
  abiEncoderTheory.compile_abi_decode_to_buf_ind;
val cut_mutual = snd (dest_imp (concl cut_ind));

Theorem guarded_cut_straight_replay[local]:
  ^outer_layout /\ (^span) a b /\ (^straight) a b /\ (^related) a s u /\
  (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\ (^endpoints) b r ==>
  (^replay) u b r
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_start a` by metis_tac[cs_extends_trans] >>
  mp_tac (BETA_RULE (Q.INST [`Q` |-> `\p g tn. p = r`,
    `start` |-> `cut_start`, `final` |-> `cut_finish`]
    abi_decode_cut_noncrossing_selected)) >>
  gvs[]
QED

Theorem guarded_cut_noncrossing_replay[local]:
  ^outer_layout ==>
  !a b s u r dst' src' input' hi.
    (^span) a b /\ ~(^crosses) a b /\ hi <> Lit 0w /\
    ((?ei. compile_abi_decode_to_buf dst' src' MLOAD (Var input') hi ei a = ((),b)) \/
     (?rest ao' vo'. compile_abi_decode_complex_elems dst' src' MLOAD
         (Var input') hi rest ao' vo' a = ((),b))) /\
    (^related) a s u /\ (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
    (^endpoints) b r ==> (^replay) u b r
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_start a` by metis_tac[cs_extends_trans] >>
  `(^straight) a b` by
    (BETA_TAC >> strip_tac >> gvs[] >>
     irule abi_decode_cut_before_slice_straight >> simp[] >> metis_tac[]) >>
  MATCH_MP_TAC (BETA_RULE (Q.INST [`a` |-> `a`, `s` |-> `s`,
    `cut_ready` |-> `cut_ready`] guarded_cut_straight_replay)) >>
  gns[]
QED

val fixed_array = BETA_RULE (Q.INST [`cut_observer` |-> `^cut_fn`, `cut` |-> `^cut_pos`]
  abi_decode_cut_array_clause);
val fixed_loop = normalize (Q.INST [`cut_observer` |-> `^cut_fn`, `cut` |-> `^cut_pos`]
  abi_decode_cut_loop_selected);
val fixed_complex = normalize (Q.INST [`outer_start` |-> `cut_start`, `ready` |-> `cut_ready`,
  `final` |-> `cut_finish`, `shadow_fn` |-> `^cut_fn`, `Kcut` |-> `^cut_pos`,
  `src` |-> `src_op`, `opc` |-> `load_opc`, `hi` |-> `hi_op`,
  `infos` |-> `elems`, `dyn` |-> `is_dyn_complex`] abi_decode_cut_complex_clause);
val fixed_member = BETA_RULE (Q.INST [`outer_start` |-> `cut_start`, `ready` |-> `cut_ready`,
  `outer_finish` |-> `cut_finish`, `cut_obs` |-> `^cut_fn`,
  `obs_id` |-> `id`, `cut` |-> `^cut_pos`,
  `src` |-> `src_op`, `opc` |-> `load_opc`, `hi` |-> `hi_op`,
  `ao` |-> `abi_offset`, `vo` |-> `vyper_offset`,
  `elems` |-> `(ei,abi_sz,mem_sz)::rest`] abi_decode_cut_member_clause);
val ordinary = normalize abi_decode_joint_mutual;

Theorem cut_cert_at_input[local]:
  ((?r g tn. qa r g tn /\ qb r /\ qc r g tn /\
              !w. (^related) ca vs w ==> (^replay) w cb r) /\
   (^related) ca vs shadow_in) ==>
  ?r g tn. qa r g tn /\ qb r /\ qc r g tn /\ (^replay) shadow_in cb r
Proof
  norm_tac >> strip_tac >> qexistsl [`r`,`g`,`tn`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!w. ~w.vs_halted /\ _ ==> _` (qspec_then `shadow_in` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Theorem guarded_cut_mutual[local]:
  ^outer_layout ==> ^cut_mutual
Proof
  disch_then (mk_asm "layout") >> MATCH_MP_TAC cut_ind >> rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume guarded_cut_mutual[loop]:
  norm_tac >> rpt gen_tac >> disch_tac >>
  mp_tac fixed_loop >>
  (impl_tac >- (asm "layout" (map_every assume_tac o CONJUNCTS) >>
    simp[frag_observer_cut_def] >> qexistsl [`ids`,`fn`,`id`] >> simp[])) >>
  disch_then (fn th => MATCH_MP_TAC (SPEC_ALL th)) >>
  rpt gen_tac >> disch_tac >>
  MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT1 ordinary))
QED

Resume guarded_cut_mutual[array]:
  norm_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (normalize fixed_array) >>
  (impl_tac >- (asm "layout" (map_every assume_tac o CONJUNCTS) >>
    simp[frag_observer_cut_def] >> qexistsl [`ids`,`fn`,`id`] >> simp[])) >>
  disch_then (drule_then (mk_asm "array")) >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecDynArray _ _ _ _ nmax) ca = ((),cb)` >>
  rename1 `frag_relabel_state L cut_start.cs_current_bb shadow_in vs` >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  ho_match_mp_tac (normalize cut_cert_at_input) >>
  conj_tac >- (asm "array" irule >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    asm_simp_tac bool_ss [] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    qexistsl [`env`,`nmax`,`sf`,`ty`] >> rpt conj_tac >-
      (pure_rewrite_tac [TypeBase.distinct_of ``:abi_dec_info``] >>
       first_assum ACCEPT_TAC) >>
    asm_simp_tac bool_ss [] >>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ ca = ((),cb)` mp_tac >>
    asm_simp_tac bool_ss []) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume guarded_cut_mutual[word]:
  norm_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `load_opc = MLOAD` SUBST_ALL_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  metis_tac[]
QED

Resume guarded_cut_mutual[bytes]:
  norm_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `load_opc = MLOAD` SUBST_ALL_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  metis_tac[]
QED

Resume guarded_cut_mutual[nil]:
  norm_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ [] _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]
QED

Resume guarded_cut_mutual[complex]:
  norm_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "bounded") assume_tac) >>
  mp_tac fixed_complex >>
  (impl_tac >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
    rename1 `frag_relabel_state L cut_start.cs_current_bb w v` >>
    MATCH_MP_TAC (normalize (Q.INST [`s` |-> `v`] guarded_cut_straight_replay)) >>
    asm "layout" (map_every assume_tac o CONJUNCTS) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  asm "layout" (assume_tac o CONJUNCT1) >>
  (impl_tac >- (
    rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
    asm "bounded" (qspec_then
      `FOLDR (\(_,asz,_) acc. asz + acc) 0 (elems:(abi_dec_info # num # num) list)` mp_tac) >>
    (impl_tac >- (simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
    disch_then (fn th => MATCH_MP_TAC (SPEC_ALL th)) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "complex") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "complex" (fn th => MATCH_MP_TAC (SPEC_ALL th)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume guarded_cut_mutual[cons]:
  norm_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "head") (mk_asm "tail")) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `cs_extends member_end cut_finish` >>
  `cs_extends cut_ready cut_finish` by
    (irule cs_extends_trans >> qexists `start` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists `member_end` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac fixed_member >>
  (impl_tac >- (
    conj_tac >- (asm "layout" (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC]) >>
    conj_tac >- (norm_tac >> asm "layout"
      (ACCEPT_TAC o normalize o MATCH_MP (BETA_RULE guarded_cut_noncrossing_replay))) >>
    disj2_tac >> qexistsl [`ei`, `abi_sz`, `mem_sz`, `rest`] >>
    conj_tac >- REFL_TAC >>
    conj_tac >- (rpt gen_tac >> conj_tac
      >- (norm_tac >> MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT1 ordinary))) >>
      norm_tac >> asm "head" (qspecl_then
        [`dec_info_needs_offset ei`,`elem_dst`,`elem_src`] mp_tac) >>
      (impl_tac >- simp_tac bool_ss []) >> disch_then ACCEPT_TAC) >>
    conj_tac >- (norm_tac >> MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT1 (CONJUNCT2 ordinary)))) >>
    norm_tac >> asm "tail" (qspec_then `dec_info_needs_offset ei` mp_tac) >>
    (impl_tac >- simp_tac bool_ss []) >> disch_then MATCH_ACCEPT_TAC)) >>
  disch_then (fn th => MATCH_MP_TAC (SPEC_ALL (normalize th))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise guarded_cut_mutual[local]

val guarded_entry = bodyFullAbiDecodeRuntimeLoopSyntaxLib.guarded_to_buf_entry;
val ready_post = ``(^observed_decoder_post) ((^robust_at_typed) tv d) live protected
  cut_ready cut_finish t Gs ts``;
val ready_trace = extend_post ready_post ``\r. (^replay) u cut_finish r``;
val terminal_replay = ``\r.
  (?v w. r = OK v /\ ~w.vs_halted /\
         (w.vs_current_bb,w.vs_inst_idx) = ^cut_pos /\
         frag_relabel_state L cut_start.cs_current_bb w v /\
         local_prefix ctx ^cut_fn ^cut_pos u w) \/
  (?v w k. r = Abort Revert_abort v /\ frag_relabel_state L cut_start.cs_current_bb w v /\
           run_from k ctx ^cut_fn u = Abort Revert_abort w)``;
val selected_statement = ``^outer_layout /\ cut_ready.cs_blocks = cut_start.cs_blocks /\
  (^guarded_entry) dst src opc base_op hi info env sf ty tv live protected
    cut_ready cut_finish t Gs ts d /\
  (^contained) protected /\ (^input_origin) t /\
  ~u.vs_halted /\ u.vs_current_bb = L /\ u.vs_inst_idx = LENGTH cut_ready.cs_current_insts /\
  frag_relabel_state L cut_start.cs_current_bb u t ==>
  ^(extend_post ready_post terminal_replay)``;

Theorem abi_decode_guarded_to_buf_cut_selected:
  ^(close_statement selected_statement)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "layout") (map_every assume_tac o CONJUNCTS)) >>
  asm "layout" (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cut_ready cut_finish` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ cut_ready = ((),cut_finish)`
       (mp_tac o AP_TERM ``SND : (unit # compile_state) -> compile_state``) >>
     simp_tac bool_ss [pairTheory.SND] >>
     disch_then (SUBST1_TAC o SYM) >> simp[externalEntryShapeTheory.compile_abi_decode_labels]) >>
  SUBGOAL_THEN (beta ready_trace) (qx_choose_then `result` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (CONJUNCTS_THEN2 (mk_asm "post") (mk_asm "replay")))))
  >- (asm "layout" (fn th =>
       MATCH_MP_TAC (SPEC_ALL (Q.SPECL [`dst`,`src`,`opc`,`base_op`,`hi`,`info`]
         (CONJUNCT1 (MATCH_MP (BETA_RULE guarded_cut_mutual) th))))) >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
             asm_simp_tac bool_ss [cs_extends_refl, pairTheory.PAIR_EQ]]) >>
  qexistsl [`result`,`Gf`,`tnf`] >> conj_tac >- asm "post" ACCEPT_TAC >>
  `(^shadow_cursor) L cut_start cut_finish = ^cut_pos` by
    (BETA_TAC >> simp[frag_observer_cut_def]) >>
  asm "replay" mp_tac >>
  asm_simp_tac bool_ss [frag_observer_cut_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`v`,`w`] >> simp[] >>
      conj_tac >- fs[pairTheory.PAIR_EQ] >>
      irule abi_decode_cut_prefix_at_end >> asm_rewrite_tac[]) >>
  disj2_tac >> metis_tac[]
QED
