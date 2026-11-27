(* Conditional assembly of the dynamic-array phase packets. *)
Theory bodyAbiDecodeGuardedArrayBindMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeArrayPrepare bodyFullAbiDecodeArrayBulkRobust
  bodyFullAbiDecodeArrayScratch bodyFullAbiDecodeRuntimeLoopSyntax
  bodyFullAbiDecodeScratchCode abiDecoderCoherence exprLowering vyperTypeSystem
  abiDecodeRanges valueEncodingProps vyperValue words arithmetic
  abiDecoderBulk abiDecoderDynarrayPrefix abiDecoderArrayLoopInit
  abiDecoderIndexInit abiDecoderRecursiveArray abiEncoderChildContext
  emitHelperProps exprLoweringProps abiDecoderReentry fragExec
  fragGasOriginPtrLoop fragGasPath compileEnv emitHelper venomExecSemantics venomInst
  abiDecoderContract abiDecoderComposition abiEncoder loweringStateRelDefs
  normalizationPrefixPtr typedSArrayDynSafety valueEncodingTyping
  exprSimAggregateEncoding pred_set bodyFullAbiDecodeCutPath
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeCutArraySyntaxLib

structure Effect = bodyAbiDecodeGuardedEffectSyntaxLib;
val term_beta = Effect.beta;
val triple = Effect.triple;

fun close tm = list_mk_forall (free_vars tm, tm);

val prepare_all =
  let
    val old = concl abi_decode_array_prepare_width_joint
    val (entry, post) = dest_imp (term_beta old)
    val (ws, body) = strip_exists post
    val (_, _, tf) = triple "prepare witnesses" ws
    val (path, obs_result) = dest_conj body
    val (obs, result) = dest_conj obs_result
    val (abort, success) = dest_disj result
    val (ns, fields) = strip_exists success
    val (t, _, _) = triple "prepare success" ns
    val s = param (free_vars old) "s"
    val tn = param (free_vars old) "tn"
    val success' = list_mk_exists (ns, mk_conj (fields, effect s tn t tf))
    val new = mk_imp (entry, list_mk_exists
      (ws, mk_conj (path, mk_conj (obs, mk_disj (abort, success')))))
  in close (checked "array prepare" old new) end;

val scratch_all =
  let
    val old = concl abi_decode_array_scratch_loop_entry_horizon_joint
    val (entry, post) = dest_imp (term_beta old)
    val (ws, body) = strip_exists post
    val s = param (free_vars old) "s"
    val tn = param (free_vars old) "tn"
    val (t,tf) = case ws of [t,_,tf,_,_,_] => (t,tf)
      | _ => raise Fail "array scratch witnesses"
    val new = mk_imp (entry, list_mk_exists (ws, mk_conj (body,effect s tn t tf)))
  in close (checked "array scratch" old new) end;

val bulk_all = close (term_beta (guarded_effect_bulk_clause ()));
val array_effect_clause = guarded_effect_array_clause ();

(* Compile-state adapters. These do not select physical runs. *)
Triviality array_compile_phases:
  !dst src input hi ei asz msz dyn maxn start finish.
  compile_abi_decode_to_buf dst src MLOAD (Var input) hi
    (DecDynArray ei asz msz dyn maxn) start = ((),finish) ==>
  ?addr sg cnt sh.
    abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn asz start = (addr,sg) /\
    abi_decode_array_header dst addr MLOAD sg = (cnt,sh) /\
    (if ~dyn /\ ~dec_info_needs_clamp ei then
       abi_decode_bulk_payload dst src cnt msz MLOAD (Var input) sh = ((),finish)
     else ?ip sl. abi_decode_index_init sh = (ip,sl) /\
       compile_abi_decode_dyn_loop dst src MLOAD (Var input) hi ei asz msz ip cnt sl =
         ((),finish))
Proof
  rpt gen_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  Cases_on `dyn \/ dec_info_needs_clamp ei`
  >- (strip_tac >> drule_all abi_decode_loop_array_trace >> strip_tac >>
      drule abi_decode_array_loop_init_trace >> strip_tac >>
      qexistsl [`addr`, `guard_st`, `cnt`, `header_st`] >> gvs[] >> metis_tac[]) >>
  `~dyn /\ ~dec_info_needs_clamp ei` by metis_tac[] >>
  `dyn = F` by simp[] >>
  asm_simp_tac (srw_ss()) [abi_decode_bulk_phases, abi_decode_bulk_body_def, comp_bind_def] >>
  Cases_on `abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn asz start` >>
  rename1 `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = (addr,sg)` >>
  Cases_on `abi_decode_array_header dst addr MLOAD sg` >> simp[LET_THM]
QED

Triviality array_prepare_straight:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn asz start = (addr,sg) /\
  abi_decode_array_header dst addr MLOAD sg = (cnt,sh) ==>
  sh.cs_blocks = start.cs_blocks /\ sh.cs_current_bb = start.cs_current_bb /\
  inst_extends start sh /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start sh)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `emitted_insts start sh = emitted_insts start sg ++ emitted_insts sg sh` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[listTheory.EVERY_APPEND] >> conj_tac
  >- metis_tac[inst_extends_trans] >> fs[listTheory.EVERY_MEM]
QED

Triviality array_bulk_payload_layout:
  abi_decode_bulk_payload dst src cnt msz MLOAD (Var input) sa = ((),sf) ==>
  cs_extends sa sf /\ sf.cs_blocks = sa.cs_blocks
Proof
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
       abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  strip_tac >> gvs[cs_extends_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Triviality array_robust_from_count:
  n < dimword (:256) /\ cap < dimword (:256) /\
  mem_word_at d m = n2w n /\ (!i. d <= i /\ i < d+32 ==> i NOTIN tm) /\
  (!k v. k < n /\ value_has_type tv v /\ val_wf tv v /\
    val_in_memory tv v (d+32+k*type_memory_size tv) m ==>
    !mem. mem_agree_outside tm m mem ==>
      val_in_memory tv v (d+32+k*type_memory_size tv) mem) ==>
  !v. value_has_type (ArrayTV tv (Dynamic cap)) v /\
      val_wf (ArrayTV tv (Dynamic cap)) v /\
      val_in_memory (ArrayTV tv (Dynamic cap)) v d m ==>
      !mem. mem_agree_outside tm m mem ==>
        val_in_memory (ArrayTV tv (Dynamic cap)) v d mem
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule value_has_type_dynarray_cases >>
  disch_then (qx_choose_then `vs` SUBST_ALL_TAC) >>
  qpat_assum `value_has_type (ArrayTV _ _) _` mp_tac >>
  simp_tac bool_ss [vyperTypingTheory.value_has_type_def] >> strip_tac >>
  qpat_assum `val_in_memory (ArrayTV _ _) _ _ _`
    (strip_assume_tac o SRULE [valueEncodingDefsTheory.val_in_memory_def]) >>
  `LENGTH vs = n` by
    (`LENGTH vs < dimword (:256)` by decide_tac >>
     qpat_assum `mem_word_at d m = n2w (LENGTH vs)` mp_tac >>
     qpat_assum `mem_word_at d m = n2w n` (rewrite_tac o single) >>
     simp[wordsTheory.n2w_11]) >>
  match_mp_tac robust_dynarray_clean_count_assemble >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  qx_gen_tac `k` >> rpt strip_tac >>
  qpat_assum `!k v. k < n /\ _ ==> _` irule >> simp[] >>
  `value_has_type tv (EL k vs)` by
    fs[vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  gvs[typedMemoryCopyTheory.typed_copy_dynarray_representation]
QED

Theorem abi_decode_array_guarded_bind_effect_mods:
  ^prepare_all ==> ^scratch_all ==>
  (^array_mode ==> ^array_straight_rule) ==>
  (^array_mode ==> ^array_bind_rule) ==>
  (^array_mode ==> ^array_revert_rule) ==>
  ^bulk_all ==> ^array_effect_clause
Proof
  BETA_TAC >> disch_then (mk_asm "prepare") >> disch_then (mk_asm "scratch") >>
  disch_then (mk_asm "observe_straight") >>
  disch_then (mk_asm "observe_bind") >> disch_then (mk_asm "observe_revert") >>
  disch_then (mk_asm "bulk") >>
  rpt gen_tac >> disch_then (mk_asm "loop_ih") >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2
    (map_every assume_tac o CONJUNCTS) (mk_asm "crossing")) >>
  `?et ev. ty = ArrayT et (Dynamic max_count) /\ tv = ArrayTV ev (Dynamic max_count)` by
    (qpat_assum `DecDynArray _ _ _ _ _ = type_to_abi_dec_info _ _ ty` mp_tac >>
     qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     namedCases_on `ty` ["bt", "tys", "elt bd", "nsid", "nsid", ""]
     >- (namedCases_on `bt` ["k", "k", "", "", "k", "bnd", ""] >>
         simp[Once type_to_abi_dec_info_def] >>
         Cases_on `bnd` >> simp[Once type_to_abi_dec_info_def])
     >- simp[Once type_to_abi_dec_info_def]
     >- (Cases_on `bd` >> simp[Once type_to_abi_dec_info_def,
                                abi_decoder_coherent_array_iff] >>
         rpt strip_tac >> gvs[])
     >- (Cases_on `FLOOKUP sf (nsid_to_string nsid)` >>
         simp[Once type_to_abi_dec_info_def])
     >> simp[Once type_to_abi_dec_info_def]) >>
  `abi_decoder_coherent ce env sf et ev /\
   abi_decoder_header ce env (ArrayT et (Dynamic max_count))
     (ArrayTV ev (Dynamic max_count))` by
    (qpat_x_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     simp[abi_decoder_coherent_array_iff]) >>
  `elem_info = type_to_abi_dec_info sf ce et /\
   elem_abi_sz = abi_embedded_static_size ce.ce_struct_fields et /\
   elem_mem_sz = type_memory_bytes ce et /\
   elem_is_dyn = is_abi_dynamic ce.ce_struct_fields et` by
    (qpat_x_assum `DecDynArray _ _ _ _ _ = type_to_abi_dec_info _ _ ty` mp_tac >>
     asm_simp_tac bool_ss [] >> simp[Once type_to_abi_dec_info_def]) >>
  `0 < type_slot_size ev` by
    (qpat_assum `abi_decoder_header ce env (ArrayT _ _) _` mp_tac >>
     simp_tac bool_ss [abi_decoder_header_def] >>
     disch_then (mp_tac o CONJUNCT1) >> simp[Once evaluate_type_def, AllCaseEqs()]) >>
  `elem_mem_sz = type_memory_size ev /\
   elem_abi_sz <= elem_mem_sz /\ (~elem_is_dyn ==> elem_abi_sz = elem_mem_sz)` by
    (qpat_assum `abi_decoder_coherent ce env sf et ev`
       (mp_then Any mp_tac abi_decoder_coherent_header) >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     Cases_on `is_dynamic (vyper_to_abi_type env et)` >>
     fs[abi_member_head_size_def, type_memory_size_slots]) >>
  `!c. c <= max_count ==> c * elem_abi_sz < dimword (:256)` by
    (rpt strip_tac >>
     `c * elem_abi_sz <= max_count * elem_mem_sz` by
       (irule LESS_MONO_MULT2 >> simp[]) >>
     irule LESS_EQ_LESS_TRANS >> qexists_tac `max_count * elem_mem_sz` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `d + type_memory_size tv <= _` mp_tac >>
     qpat_assum `tv = ArrayTV ev _` (rewrite_tac o single) >>
     rewrite_tac[valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
     qpat_assum `output_base + output_cap < dimword (:256)` mp_tac >> decide_tac) >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `dp` strip_assume_tac) >>
  qpat_x_assum `dst = Var dp` SUBST_ALL_TAC >>
  qpat_x_assum `base_op = Var input` SUBST_ALL_TAC >>
  qpat_x_assum `load_opc = MLOAD` SUBST_ALL_TAC >>
  qpat_x_assum `?off h. eval_operand _ s = SOME (n2w off) /\
      _ /\ off < dimword (:256) /\ h <= LENGTH input_bytes`
    (qx_choose_then `off` (qx_choose_then `h` strip_assume_tac)) >>
  qpat_assum `tv = ArrayTV ev _` SUBST_ALL_TAC >>
  drule array_compile_phases >>
  disch_then (qx_choose_then `addr` (qx_choose_then `sg`
    (qx_choose_then `cnt` (qx_choose_then `sh`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac)))))) >>
  suspend "prepare"
QED

Resume abi_decode_array_guarded_bind_effect_mods[prepare]:
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all array_prepare_straight >> strip_tac >>
  `cs_extends start sh` by (irule abi_encoder_straight_extends >> simp[]) >>
  `cs_extends sh finish'` by
    (qpat_x_assum `(if _ then _ else _)` mp_tac >>
     Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp elem_info` >>
     asm_simp_tac bool_ss [] >> strip_tac
     >- (drule array_bulk_payload_layout >> simp[]) >>
     rename1 `abi_decode_index_init sh = (ip,sl)` >>
     drule abi_decode_index_init_shape >> strip_tac >>
     drule_all abi_decoder_recursive_loop_end >> strip_tac >>
     irule cs_extends_trans >> qexists `sl` >> simp[] >>
     irule abi_encoder_straight_extends >> simp[]) >>
  `fn_has_code start sh fn /\ fn_has_code sh finish' fn` by
    (irule fn_has_code_split >> simp[]) >>
  `lookup_var dp s = SOME (n2w d) /\ not_fresh_at start dp /\ not_fresh_at start input` by
    (qpat_assum `eval_operand (Var dp) s = _` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var dp)` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var input)` mp_tac >>
     simp[NoAsms, venomStateTheory.eval_operand_def, abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `ptr_covers G tn dp s (type_memory_size (ArrayTV ev (Dynamic max_count)))` by
    (qpat_assum `ptr_covers G tn dp s _` mp_tac >> simp[NoAsms]) >>
  `EVERY (\(aid,q,b,k,bytes). b+k <= d \/
       d + type_memory_size (ArrayTV ev (Dynamic max_count)) <= b) live` by
    (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < _ /\ (_ \/ _)) live` mp_tac >>
     simp[NoAsms, listTheory.EVERY_MEM] >> disch_tac >>
     qx_gen_tac `entry` >> disch_tac >>
     first_x_assum drule >> PairCases_on `entry` >> simp[]) >>
  asm_x "prepare" (mp_tac o Q.INST
    [`dst` |-> `dp`, `src` |-> `src_op`, `hi` |-> `hi_op`,
     `tv` |-> `ev`, `maxn` |-> `max_count`, `stride` |-> `elem_abi_sz`,
     `guard_st` |-> `sg`, `header_st` |-> `sh`] o SPECL (fst (strip_forall prepare_all))) >>
  (impl_tac >- (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >>
  disch_then (qx_choose_then `r0` (qx_choose_then `G1` (qx_choose_then `tn1`
    (CONJUNCTS_THEN2 (mk_asm "prep_path")
      (CONJUNCTS_THEN2 (mk_asm "prep_obs") assume_tac))))) >>
  `(^array_cert) start sh s r0` by
    (BETA_TAC >> disch_tac >>
     asm "crossing" (strip_assume_tac o UNDISCH) >>
     `cs_extends sh cut_finish` by
       (irule cs_extends_trans >> qexists `finish'` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     asm "observe_straight" (irule o UNDISCH) >>
     rpt (FIRST [conj_tac, first_assum ACCEPT_TAC, asm "prep_obs" ACCEPT_TAC]) >>
     qpat_x_assum `(?t. r0 = Abort Revert_abort t) \/ _` strip_assume_tac
     >- (disj2_tac >> qexists `t` >> first_assum ACCEPT_TAC) >>
     disj1_tac >> qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?t. r0 = Abort Revert_abort t) \/ _` DISJ_CASES_TAC
  >- (qpat_x_assum `?t. r0 = Abort Revert_abort t` (qx_choose_then `u` SUBST_ALL_TAC) >>
      qexistsl [`Abort Revert_abort u`, `G1`, `tn1`] >>
      reverse conj_tac >-
        (disch_tac >> asm "observe_revert" (irule o UNDISCH) >>
         qexists `sh` >> fs[]) >>
      conj_tac >- (rpt strip_tac >> asm "prep_path" irule) >>
      conj_tac
      >- (gen_tac >> disch_tac >> asm "prep_obs" irule >>
          drule_all fn_has_code_split >> simp[]) >>
      disj2_tac >> qexists `u` >> simp[]) >>
  qpat_x_assum `?t n cvar. (r0 = OK t /\ _) /\ _`
    (qx_choose_then `u` (qx_choose_then `n` (qx_choose_then `cvar`
      (map_every assume_tac o CONJUNCTS)))) >>
  suspend "dispatch"
QED

Resume abi_decode_array_guarded_bind_effect_mods[dispatch]:
  `start.cs_next_var <= sh.cs_next_var` by
    (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >> simp[]) >>
  `!x. not_fresh_at start x ==> not_fresh_at sh x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `start` >> simp[]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
        abi_decoder_operand_live sh.cs_next_var op` by
    (rpt strip_tac >> irule abi_decoder_operand_live_mono >>
     qexists `start.cs_next_var` >> simp[]) >>
  `max_count < dimword (:256)` by
    (`1 <= elem_mem_sz` by fs[type_memory_size_slots] >>
     `max_count * 1 <= max_count * elem_mem_sz` by
       (irule LESS_MONO_MULT2 >> simp[]) >>
     qpat_assum `d + type_memory_size _ <= output_base+output_cap` mp_tac >>
     rewrite_tac[valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
     qpat_assum `output_base+output_cap < dimword (:256)` mp_tac >>
     qpat_assum `max_count * 1 <= _` mp_tac >>
     rewrite_tac[MULT_RIGHT_1] >>
     qabbrev_tac `span = max_count * elem_mem_sz` >>
     qabbrev_tac `limit = dimword (:256)` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `32+n*elem_mem_sz <= type_memory_size (ArrayTV ev (Dynamic max_count))` by
    (rewrite_tac[valueEncodingTheory.type_memory_size_def] >>
     qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >> simp[]) >>
  `d+32+n*elem_mem_sz <= output_base+output_cap` by
    (qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qpat_assum `d + type_memory_size _ <= output_base+output_cap` mp_tac >>
     qabbrev_tac `span = n * elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `w2n input_word+LENGTH input_bytes <= d \/ d+32+n*elem_mem_sz <= w2n input_word`
  >- (qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qpat_assum `w2n input_word+LENGTH input_bytes <= d \/ _` mp_tac >>
     qabbrev_tac `span = n * elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     qabbrev_tac `ibase = w2n input_word` >> qabbrev_tac `len = LENGTH input_bytes` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp elem_info` >>
  asm_simp_tac bool_ss [] >> disch_tac
  >- suspend "bulk" >>
  suspend "loop"
QED

Resume abi_decode_array_guarded_bind_effect_mods[bulk]:
  asm_x "loop_ih" kall_tac >> asm_x "scratch" kall_tac >>
  `~observe_array` by
    (disch_tac >> asm "crossing" (strip_assume_tac o UNDISCH) >>
     drule array_bulk_payload_layout >> strip_tac >>
     qpat_assum `finish'.cs_blocks <> cut_start.cs_blocks` mp_tac >>
     qpat_assum `finish'.cs_blocks = sh.cs_blocks` mp_tac >>
     qpat_assum `sh.cs_blocks = start.cs_blocks` mp_tac >>
     qpat_assum `start.cs_blocks = cut_start.cs_blocks` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `elem_abi_sz = elem_mem_sz` by
    (qpat_assum `~elem_is_dyn ==> _` mp_tac >> simp[]) >>
  `ptr_covers G1 tn1 dp u (32+n*elem_mem_sz)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists `type_memory_size (ArrayTV ev (Dynamic max_count))` >> simp[]) >>
  `off+32+n*elem_mem_sz <= LENGTH input_bytes` by
    (qpat_assum `off+32+n*elem_abi_sz <= LENGTH input_bytes` mp_tac >>
     qpat_assum `elem_abi_sz = elem_mem_sz` (rewrite_tac o single) >> simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `w2n input_word+LENGTH input_bytes <= d+32 \/ d+32+n*elem_mem_sz <= w2n input_word`
  >- (qpat_assum `w2n input_word+LENGTH input_bytes <= d \/ d+32+n*elem_mem_sz <= _` mp_tac >>
      simp[NoAsms]) >>
  `EVERY (\(aid,p,b,k,bytes). b+k <= d+32 \/ d+32+n*elem_mem_sz <= b) live` by
    (qpat_assum `EVERY (\(aid,q,b,k,bytes). b+k <= d \/ _) live` mp_tac >>
     simp_tac bool_ss [listTheory.EVERY_MEM] >> disch_tac >>
     qx_gen_tac `entry` >> disch_tac >> first_x_assum drule >>
     PairCases_on `entry` >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qabbrev_tac `span = n*elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `EVERY (\(a,bytes). a+LENGTH bytes <= d+32 \/ d+32+n*elem_mem_sz <= a) protected` by
    (qpat_assum `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ _) protected` mp_tac >>
     simp_tac bool_ss [listTheory.EVERY_MEM] >> disch_tac >>
     qx_gen_tac `entry` >> disch_tac >> first_x_assum drule >>
     PairCases_on `entry` >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qabbrev_tac `span = n*elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     qabbrev_tac `len = LENGTH entry1` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `abi_decode_bulk_payload (Var dp) src_op cnt elem_mem_sz MLOAD (Var input) sh = ((),finish')` by
    (qpat_assum `cnt = Var cvar` (rewrite_tac o single) >>
     qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `abi_decoder_operand_live sh.cs_next_var (Var dp) /\
   abi_decoder_operand_live sh.cs_next_var (Var input)` by
    (conj_tac >> qpat_assum `!op. abi_decoder_operand_live start.cs_next_var op ==> _`
        irule >> first_assum ACCEPT_TAC) >>
  asm_x "bulk" (mp_tac o Q.INST
    [`sa` |-> `sh`, `sf` |-> `finish'`, `s` |-> `u`,
     `G` |-> `G1`, `tn` |-> `tn1`, `src` |-> `src_op`,
     `tv` |-> `ev`, `msz` |-> `elem_mem_sz`] o SPECL (fst (strip_forall bulk_all))) >>
  (impl_tac >- (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "bulk_exit"
QED

Resume abi_decode_array_guarded_bind_effect_mods[bulk_exit]:
  qexistsl [`OK t`, `Gf`, `tnf`] >>
  reverse conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`G1`, `u`, `tn1`] >> conj_tac
     >- (asm "prep_path" (qspec_then `DF H` mp_tac) >> simp[]) >>
     first_x_assum irule) >>
  conj_tac >-
    (qx_gen_tac `obs` >> disch_tac >> drule_all fn_has_code_split >> strip_tac >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists `u` >> conj_tac
     >- (asm "prep_obs" (qspec_then `obs` mp_tac) >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  disj1_tac >> qexists `t` >>
  `abi_decode_guarded_effect_core s tn t tnf` by
    (drule_all abi_decode_guarded_effect_compose_core >> simp[]) >>
  `!x. not_fresh_at start x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sh x` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at sh x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
     i IN tn.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!i. output_base <= i /\ _ /\ i IN tn1.t_mem ==> _` irule >>
     simp[] >> first_x_assum irule >> simp[]) >>
  simp_tac bool_ss [] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    match_mp_tac array_robust_from_count >>
    conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
    rpt strip_tac >> first_x_assum irule >> simp[]]
QED

Resume abi_decode_array_guarded_bind_effect_mods[loop]:
  asm_x "bulk" kall_tac >>
  qpat_x_assum `?ip sl. abi_decode_index_init sh = (ip,sl) /\ _`
    (qx_choose_then `ip` (qx_choose_then `sl` strip_assume_tac)) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `cs_extends sh sl /\ sh.cs_next_var <= sl.cs_next_var` by
    (simp[] >> irule abi_encoder_straight_extends >> simp[]) >>
  `cs_extends sl finish'` by (drule_all abi_decoder_recursive_loop_end >> simp[]) >>
  `fn_has_code sh sl fn /\ fn_has_code sl finish' fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule abi_decode_scratch_code >> strip_tac >>
  rename [`compile_alloc_buffer 32 sh = (ibuf,isb)`, `ip = Var code_counter`] >>
  asm_x "scratch" (mp_tac o Q.INST
    [`sa` |-> `sh`, `loop_st` |-> `sl`, `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`]
    o SPECL (fst (strip_forall scratch_all))) >>
  (impl_tac >- (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >>
  disch_then (qx_choose_then `v` (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `counter` (qx_choose_then `cell` (qx_choose_then `srcbase`
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 (mk_asm "scratch_path")
          (CONJUNCTS_THEN2 (mk_asm "scratch_obs") (map_every assume_tac o CONJUNCTS)))
        assume_tac))))))) >>
  `(^array_cert) sh sl u (OK v)` by
    (BETA_TAC >> disch_tac >>
     asm "crossing" (strip_assume_tac o UNDISCH) >>
     `cs_extends cut_ready sh /\ cs_extends sl cut_finish` by
       (conj_tac
        >- (irule cs_extends_trans >> qexists `start` >>
            conj_tac >> first_assum ACCEPT_TAC) >>
        irule cs_extends_trans >> qexists `finish'` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     asm "observe_straight" (irule o UNDISCH) >>
     rpt (FIRST [conj_tac, first_assum ACCEPT_TAC, asm "scratch_obs" ACCEPT_TAC]) >>
     simp[]) >>
  `(^array_cert) start sl s (OK v)` by
    (BETA_TAC >> disch_tac >> asm "observe_bind" (irule o UNDISCH) >>
     qexistsl [`sh`, `u`] >> conj_tac
     >- (qpat_assum `r0 = OK u` (rewrite_tac o single o SYM) >>
         qpat_assum `(^array_cert) start sh s r0`
           (ACCEPT_TAC o UNDISCH o BETA_RULE)) >>
     qpat_assum `(^array_cert) sh sl u (OK v)`
       (ACCEPT_TAC o UNDISCH o BETA_RULE)) >>
  `observe_array ==> (^array_crossing) sl finish'` by
    (BETA_TAC >> disch_tac >> asm "crossing" (strip_assume_tac o UNDISCH) >>
     `cs_extends cut_ready sl` by
       (irule cs_extends_trans >> qexists `sh` >> conj_tac
        >- (irule cs_extends_trans >> qexists `start` >>
            conj_tac >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     simp[]) >>
  suspend "loop_entry"
QED

Resume abi_decode_array_guarded_bind_effect_mods[loop_entry]:
  `v.vs_labels = u.vs_labels` by
    (qpat_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
     asm "scratch_path" (qspec_then `H0` mp_tac) >>
     simp[] >> MATCH_ACCEPT_TAC gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels) >>
  `!opnd. abi_decoder_operand_live sh.cs_next_var opnd ==>
       eval_operand opnd v = eval_operand opnd u /\
       op_prov G2 opnd = op_prov G1 opnd /\ op_taint tn2 opnd = op_taint tn1 opnd` by
    (rpt gen_tac >> disch_tac >>
     MATCH_MP_TAC (Q.INST [`R` |-> `{x | not_fresh_at sh x}`]
       abiDecodePtrScalarFrameTheory.abi_decode_scalar_protected_operand) >>
     simp[] >> qx_gen_tac `x` >> disch_then SUBST_ALL_TAC >>
     qpat_assum `abi_decoder_operand_live sh.cs_next_var (Var x)` mp_tac >>
     simp[NoAsms, abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `abi_decoder_operand_live sh.cs_next_var (Var dp) /\
   abi_decoder_operand_live sh.cs_next_var (Var input) /\
   abi_decoder_operand_live sh.cs_next_var cnt` by
    (qpat_assum `cnt = Var cvar` (rewrite_tac o single) >>
     qpat_assum `not_fresh_at sh dp` mp_tac >>
     qpat_assum `not_fresh_at sh input` mp_tac >>
     qpat_assum `not_fresh_at sh cvar` mp_tac >>
     simp[NoAsms, abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!opnd. abi_decoder_operand_live sh.cs_next_var opnd ==>
        abi_decoder_operand_live sl.cs_next_var opnd` by
    (rpt strip_tac >> irule abi_decoder_operand_live_mono >>
     qexists `sh.cs_next_var` >> simp[]) >>
  `local_ptrs_reserved ce sl` by
    (irule local_ptrs_reserved_next_var >> qexists `sh` >> simp[]) >>
  `ptr_covers G2 tn2 dp v (32+n*elem_mem_sz)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists `type_memory_size (ArrayTV ev (Dynamic max_count))` >> simp[] >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G1`,`u`,`tn1`] >> simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `cell+32 <= d \/ d+(32+n*elem_mem_sz) <= cell`
  >- (qpat_assum `output_base+output_cap <= cell \/ cell+32 <= output_base` mp_tac >>
      qpat_assum `d+32+n*elem_mem_sz <= output_base+output_cap` mp_tac >>
      qpat_assum `output_base <= d` mp_tac >>
      qabbrev_tac `span = n*elem_mem_sz` >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `mem_word_at d v.vs_memory = n2w n /\
   mem_word_at (w2n input_word + off) v.vs_memory = n2w n` by
    (`d+32 <= cell \/ cell+32 <= d` by
       (qpat_assum `cell+32 <= d \/ _` mp_tac >> simp[NoAsms]) >>
     `w2n input_word+off+32 <= cell \/ cell+32 <= w2n input_word+off` by
       (qpat_assum `w2n input_word+LENGTH input_bytes <= cell \/ cell+32 <= w2n input_word` mp_tac >>
        qpat_assum `off+32+n*elem_abi_sz <= LENGTH input_bytes` mp_tac >>
        qabbrev_tac `span = n*elem_abi_sz` >> qabbrev_tac `ibase = w2n input_word` >>
        qabbrev_tac `len = LENGTH input_bytes` >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     conj_tac >>
     (fn g => (qmatch_goalsub_abbrev_tac `mem_word_at a v.vs_memory` >>
       `mem_word_at a v.vs_memory = mem_word_at a u.vs_memory` by
         (simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
          qpat_assum `!a k. a+k <= cell \/ cell+32 <= a ==> _`
            (qspecl_then [`a`,`32`] mp_tac) >> simp[Abbr `a`]) >>
       simp[Abbr `a`]) g)) >>
  suspend "loop_apply"
QED

Resume abi_decode_array_guarded_bind_effect_mods[loop_apply]:
  `start.cs_next_id <= sl.cs_next_id` by
    (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >>
     qpat_assum `start.cs_next_id <= sg.cs_next_id` mp_tac >>
     qpat_assum `sh.cs_next_id = sg.cs_next_id + 2` mp_tac >>
     qpat_assum `sh.cs_next_id < sl.cs_next_id` mp_tac >> simp[NoAsms]) >>
  `EVERY (\(aid,p,b,k,bytes). aid < sl.cs_next_id /\
       (b+k <= d \/ d+(32+n*elem_mem_sz) <= b)) live` by
    (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (_ \/ _)) live` mp_tac >>
     simp_tac bool_ss [listTheory.EVERY_MEM] >> disch_tac >>
     qx_gen_tac `entry` >> disch_tac >> first_x_assum drule >> PairCases_on `entry` >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qpat_assum `start.cs_next_id <= sl.cs_next_id` mp_tac >>
     qabbrev_tac `span = n*elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+(32+n*elem_mem_sz) <= a) protected` by
    (qpat_assum `EVERY (\(a,bytes). a+LENGTH bytes <= d \/ _) protected` mp_tac >>
     simp_tac bool_ss [listTheory.EVERY_MEM] >> disch_tac >>
     qx_gen_tac `entry` >> disch_tac >> first_x_assum drule >>
     PairCases_on `entry` >>
     CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
     qpat_assum `32+n*elem_mem_sz <= type_memory_size _` mp_tac >>
     qabbrev_tac `span = n*elem_mem_sz` >>
     qabbrev_tac `cap = type_memory_size (ArrayTV ev (Dynamic max_count))` >>
     qabbrev_tac `len = LENGTH entry1` >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `cell = buffer_allocation_base _ _` kall_tac >>
  map_every (fn opnd =>
    qpat_assum `!opnd. abi_decoder_operand_live sh.cs_next_var opnd ==>
       eval_operand opnd v = _ /\ _` (qspec_then opnd mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac)
    [`src_op`,`hi_op`,`cnt`,`Var dp`,`Var input`] >>
  `FLOOKUP G2 dp = SOME (output_base,output_cap)` by
    (qpat_assum `!x. not_fresh_at sh x ==> lookup_var x v = _ /\ _`
       (qspec_then `dp` mp_tac) >> simp[]) >>
  `n < dimword (:256)` by
    (match_mp_tac LESS_EQ_LESS_TRANS >> qexists `max_count` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `off <= h` by
    (qpat_assum `off+32+n*elem_abi_sz <= h` mp_tac >>
     qabbrev_tac `span = n*elem_abi_sz` >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `eval_operand (Var dp) u = SOME (n2w d)` by
    (simp_tac bool_ss [venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `?ci cp. MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
     ci.inst_outputs = [cp] /\ ci.inst_id = sh.cs_next_id /\
     not_local_ptr ce es.scopes cp` by
    (qexistsl [`mk_inst sh.cs_next_id ALLOCA [Lit 32w] [counter]`, `counter`] >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[mk_inst_def]) >>
  `!name b k. local_region ce es.scopes v name b k ==> cell+32 <= b \/ b+k <= cell` by
    (qpat_assum `!name b sz. local_region ce es.scopes v name b sz ==> b+sz <= cell \/ _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  asm_x "loop_ih" (qspecl_then [`F`,`ip`,`ibuf`,`cnt`] mp_tac) >>
  (impl_tac >- (qpat_assum `ibuf.buf_operand = ip` (rewrite_tac o single o SYM) >>
    qpat_assum `~(~elem_is_dyn /\ ~dec_info_needs_clamp elem_info)` mp_tac >>
    simp_tac bool_ss [])) >>
  disch_then (qspecl_then [`env`,`sf`,`et`,`ev`,`live`,`protected`,`sl`,`finish'`,
      `v`,`G2`,`tn2`,`d`,`sh.cs_next_id`,`counter`,`cell`,`n`,`0`,`srcbase`,`off`,`h`] mp_tac) >>
  (impl_tac >- (conj_tac >-
    (simp_tac bool_ss [SUB_EQUAL_0, ADD_CLAUSES, ZERO_LESS_EQ] >>
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
    asm_simp_tac bool_ss [GSYM ADD_ASSOC] >>
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
    >- (qexistsl [`mk_inst sh.cs_next_id ALLOCA [Lit 32w] [counter]`, `counter`] >>
        (conj_tac >- first_assum ACCEPT_TAC) >> simp[mk_inst_def])
    >- (qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC)
    >- (qpat_assum `w2n input_word+LENGTH input_bytes <= cell \/ cell+32 <= w2n input_word` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
    >- (qpat_assum `ip = Var counter` (rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC)
    >- (qexists `dp` >>
        qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
        simp_tac bool_ss [] >> conj_tac >> first_assum ACCEPT_TAC)
    >- (qexistsl [`off`,`h`] >> simp_tac bool_ss [] >> conj_tac >> first_assum ACCEPT_TAC)
    >> qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM)
    >> rewrite_tac [ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
    qpat_assum `observe_array ==> (^array_crossing) sl finish'`
      (ACCEPT_TAC o BETA_RULE))) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (mk_asm "loop_path")
        (CONJUNCTS_THEN2 (mk_asm "loop_obs") assume_tac)) assume_tac)))) >>
  suspend "loop_exit"
QED

Resume abi_decode_array_guarded_bind_effect_mods[loop_exit]:
  qexistsl [`r`,`Gf`,`tnf`] >>
  reverse conj_tac >-
    (disch_tac >> asm "observe_bind" (irule o UNDISCH) >>
     qexistsl [`sl`, `v`] >> conj_tac
     >- (qpat_assum `(^array_cert) start sl s (OK v)`
           (ACCEPT_TAC o UNDISCH o BETA_RULE)) >>
     qpat_assum `observe_array ==> observe_phase sl finish' v r`
       (ACCEPT_TAC o UNDISCH)) >>
  conj_tac >-
    (qx_gen_tac `H` >> disch_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`G1`,`u`,`tn1`] >> conj_tac
     >- (asm "prep_path" (qspec_then `DF H` mp_tac) >> simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`G2`,`v`,`tn2`] >> conj_tac
     >- (asm "scratch_path" (qspec_then `H` mp_tac) >> simp[]) >>
     asm "loop_path" (qspec_then `H` mp_tac) >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `obs` >> disch_tac >>
     `fn_has_code start sh obs /\ fn_has_code sh finish' obs` by
       (irule fn_has_code_split >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `fn_has_code sh sl obs /\ fn_has_code sl finish' obs` by
       (irule fn_has_code_split >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists `u` >> conj_tac
     >- (qpat_assum `r0 = OK u` (rewrite_tac o single o SYM) >>
         asm "prep_obs" irule >> first_assum ACCEPT_TAC) >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
     qexists `v` >> conj_tac
     >- (asm "scratch_obs" irule >> first_assum ACCEPT_TAC) >>
     asm "loop_obs" irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?t. (r = OK t /\ _) /\ _) \/ (?t. r = Abort Revert_abort t)`
    (DISJ_CASES_THEN2 (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))
                     (fn th => disj2_tac >> ACCEPT_TAC th)) >>
  disj1_tac >> qexists `t` >>
  `abi_decode_guarded_effect_core s tn v tn2` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tn1`, `u`] >> simp[]) >>
  `abi_decode_guarded_effect_core s tn t tnf` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tn2`, `v`] >> simp[]) >>
  suspend "loop_robust"
QED

Resume abi_decode_array_guarded_bind_effect_mods[loop_robust]:
  `!x. not_fresh_at start x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sh x` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     `not_fresh_at sl x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `sh` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sl x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sh x ==> lookup_var x v = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
     i IN tn1.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!i. output_base <= i /\ _ /\ i IN tn2.t_mem ==> i IN tn1.t_mem` irule >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!i. output_base <= i /\ _ /\ i IN tnf.t_mem ==> i IN tn2.t_mem` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
     i IN tn.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!i. output_base <= i /\ _ /\ i IN tn1.t_mem ==> i IN tn.t_mem` irule >>
     simp[] >> first_x_assum irule >> simp[]) >>
  `!i. d <= i /\ i < d+32 ==> i NOTIN tnf.t_mem` by
    (qx_gen_tac `i` >> strip_tac >> spose_not_then assume_tac >>
     `i < output_base+output_cap` by
       (qpat_assum `d+32+n*elem_mem_sz <= output_base+output_cap` mp_tac >>
        qpat_assum `i < d+32` mp_tac >>
        qabbrev_tac `span = n*elem_mem_sz` >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `output_base <= i` by simp[] >>
     `i IN tn1.t_mem` by
       (qpat_assum `!i. output_base <= i /\ _ /\ i IN tnf.t_mem ==> i IN tn1.t_mem` irule >>
        rpt conj_tac >> asm_rewrite_tac[]) >>
     qpat_assum `!i. d <= i /\ i < d+32 ==> i NOTIN tn1.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `mem_word_at d t.vs_memory = n2w n` by
    (qpat_assum `mem_word_at d t.vs_memory = mem_word_at d v.vs_memory` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  match_mp_tac array_robust_from_count >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `elem_mem_sz = type_memory_size ev` (rewrite_tac o single o SYM) >>
  rpt strip_tac >>
  qpat_assum `!i. 0 <= i /\ i < n ==> !v. value_has_type ev v /\ _ ==> _` irule >>
  simp[]
QED

Finalise abi_decode_array_guarded_bind_effect_mods
