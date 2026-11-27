Theory bodyAbiDecodeGuardedWordMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeOwnedWordStoreObserved
  bodyFullAbiDecodeOwnedStateProps bodyFullAbiDecodeClampObserved
  bodyFullAbiDecodeInputOrigin abiDecoderClampedWord abiDecoderContract
  abiDecoderReentry abiDecoderCoherence abiDecoderWordTyped
  exprSimAbiDecodeChildBounds externalEntryShape calldataClampPtr
  bodyPtrBopScalarOutcome stateRelProj stateFrame
  fragExec fragGasPath fragGasOriginPtrLoop
  abiEncoder exprLoweringProps emitHelperProps loweringShapeRules
  venomInst venomExecSemantics venomState venomMemDefs freshWrites ptrDiscipline
  bodyPtrDefs compileEnv loweringStateRelDefs valueEncodingProps
  finite_map list rich_list pred_set words combin pair
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeRuntimeLoopSyntaxLib
  bodyFullAbiDecodeLoopObservedSyntaxLib

(* Use the singleton packets only as syntax templates. The two stronger
   packets are closed assumptions here, to be discharged at the join. *)
fun extend_phase theorem additions =
  let
    val old = bodyAbiDecodeGuardedEffectSyntaxLib.beta (concl theorem)
    val (pre,post) = dest_imp old
    val (ws,body) = strip_exists post
    val tm = mk_imp (pre,list_mk_exists (ws,mk_conj (body,additions (free_vars pre) ws)))
    val (pre',post') = dest_imp tm
    val (ws',body') = strip_exists post'
    val erased = mk_imp (pre',list_mk_exists (ws',fst (dest_conj body')))
  in
    if aconv erased old then list_mk_forall (free_vars tm,tm)
    else raise Fail "guarded word phase does not preserve its singleton contract"
  end;

val load_all = extend_phase abi_decode_owned_relative_load_exact
  (fn vs => fn ws =>
    let
      val s = param vs "s" and tn = param vs "tn" and ctx = param vs "ctx"
      val sa = param vs "sa" and sc = param vs "sc"
      val t = param ws "t" and tnf = param ws "tnf"
    in ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
           ^tnf.t_imm = ^tn.t_imm /\
           (!obs. fn_has_code ^sa ^sc obs ==> gas_path ^ctx obs ^s 0 (OK ^t))`` end);

val store_all = extend_phase abi_decode_owned_word_store_observed_exact
  (fn vs => fn ws =>
    let
      val s = param vs "s" and tn = param vs "tn"
      val t = param ws "t" and tnf = param ws "tnf"
    in ``^t.vs_alloca_next = ^s.vs_alloca_next /\
           ^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
           ^tnf.t_imm = ^tn.t_imm`` end);

val word = #word (guarded_effect_compiler_cases (guarded_effect_length_ind_typed ()));
val crossing_word = let
  val tm = #word (guarded_effect_compiler_cases (guarded_effect_cut_ind ()))
  in list_mk_forall (free_vars tm,tm) end;
val norm_tac = CONV_TAC normalize_guarded_effect;

Theorem abi_decode_guarded_word_crossing_clause_mods:
  ^crossing_word
Proof
  norm_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `load_opc = MLOAD` SUBST_ALL_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  metis_tac[]
QED

val owned = bodyFullAbiDecodeRuntimeLoopSyntaxLib.owned_decoder_state;
val origin_of_input = bodyFullAbiDecodeLoopObservedSyntaxLib.input_origin;

(* Fold the same owned-state formula in phase applications. *)
fun rewrite_abbr direction q =
  qpat_assum q (fn th =>
    let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
    in direction eq end);
fun expand_owned q ttac = rewrite_abbr
  (fn eq => qpat_assum q (ttac o BETA_RULE o PURE_REWRITE_RULE [eq]))
  `Abbrev (OS = _)`;
fun fold_owned ttac th = rewrite_abbr
  (fn eq =>
    let
      val args = [`phase_ci`, `phase_s`, `phase_G`, `phase_tn`]
      val applied = List.foldl (fn (q,e) => Q.AP_THM e q) eq args
      val fold = Q.GENL args (GSYM (BETA_RULE applied))
    in ttac (PURE_REWRITE_RULE [fold] th) end) `Abbrev (OS = _)`;

fun owned_fmp state =
  strip_tac >> irule owned_decoder_allocas_below_fmp >>
  qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ ^state /\ _`
    (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)));

Theorem abi_decode_guarded_word_clause_conditional_mods:
  ^load_all ==> ^store_all ==> ^word
Proof
  disch_then (mk_asm "load") >> disch_then (mk_asm "store") >>
  norm_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(^owned) live protected start s G tn` by
    (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `OS = (^owned) live protected` >>
  qabbrev_tac `IO = ^origin_of_input` >>
  `IO s` by simp[Abbr `IO`] >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _`
    (qx_choose_then `off` (qx_choose_then `h` (map_every assume_tac o CONJUNCTS))) >>
  `off + abi_member_head_size (vyper_to_abi_type env ty) <= h` by
    (qpat_assum `(?clamp'. _) ==> _` mp_tac >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def,compile_abi_decode_static_def,
       comp_bind_def,comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `type_to_abi_dec_info sf ce ty = DecPrimWord clamp_info` by simp[Once EQ_SYM_EQ] >>
  drule_all exprSimAbiDecodeChildBoundsTheory.abi_decode_scalar_member_head >>
  strip_tac >>
  drule abiDecoderWordTypedTheory.abi_decoder_primitive_cases >>
  disch_then drule >> disch_then (assume_tac o cj 2) >>
  `type_memory_size tv = 32 /\ abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     simp[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  rename1 `compile_abi_clamp_basetype val_op clamp_info loaded = (ignored,clamped)` >>
  rename1 `emit_op MLOAD [src_addr] addressed = (val_op,loaded)` >>
  `ignored = ()` by (Cases_on `ignored` >> simp[]) >>
  qpat_x_assum `ignored = ()` SUBST_ALL_TAC >>
  `cs_extends start addressed` by
    (qspecl_then [`Var input`,`src_op`,`start`,`K T`] mp_tac
       compile_abi_dec_addr_labels >> simp[]) >>
  `cs_extends addressed loaded` by
    (qspecl_then [`MLOAD`,`[src_addr]`,`addressed`,`K T`] mp_tac emit_op_labels >> simp[]) >>
  `cs_extends loaded clamped` by
    (qspecl_then [`val_op`,`clamp_info`,`loaded`,`K T`] mp_tac
       compile_abi_clamp_basetype_labels >> simp[]) >>
  `cs_extends clamped finish'` by
    (qspecl_then [`MSTORE`,`[dst;val_op]`,`clamped`,`K T`] mp_tac emit_void_labels >> simp[]) >>
  `cs_extends start loaded` by (irule cs_extends_trans >> qexists `addressed` >> simp[]) >>
  `cs_extends loaded finish'` by (irule cs_extends_trans >> qexists `clamped` >> simp[]) >>
  `fn_has_code start loaded fn /\ fn_has_code loaded finish' fn` by
    (qspecl_then [`start`,`loaded`,`finish'`,`fn`] mp_tac fn_has_code_split >> simp[]) >>
  `off + 32 <= LENGTH input_bytes` by decide_tac >>
  `allocas_from lo s` by
    (qpat_assum `?H. V H` (qx_choose_then `H` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `ghost_inv_at _ lo _ ce cx es G tn s`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp_tac bool_ss []) >>
  qpat_x_assum `base_op = Var input` SUBST_ALL_TAC >>
  `not_fresh_at start input` by
    (qpat_assum `abi_decoder_operand_live start.cs_next_var (Var input)` mp_tac >>
     simp[NoAsms,abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `origin` >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (owned_fmp ``s:venom_state``) >>
  asm_x "load" (fold_owned drule_all o SPEC_ALL) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `out` (qx_choose_then `t` (qx_choose_then `Gf`
      (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS)))))) >>
  `fn_has_code loaded clamped fn /\ fn_has_code clamped finish' fn` by
    (qspecl_then [`loaded`,`clamped`,`finish'`,`fn`] mp_tac fn_has_code_split >> simp[]) >>
  `abi_decoder_operand_live loaded.cs_next_var val_op` by
    (irule abi_decoder_operand_live_emit >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`MLOAD`,`[src_addr]`,`addressed`] >> first_assum ACCEPT_TAC) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `t.vs_allocas = s.vs_allocas` (fn th =>
           rewrite_tac[allocas_from_def, th]) >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     qpat_assum `t.vs_alloca_next = s.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (expand_owned `OS loaded t Gf tnf` (map_every assume_tac o CONJUNCTS) >>
     owned_fmp ``t:venom_state``) >>
  drule_all abi_decode_clamp_joint_observed >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `cr` (qx_choose_then `CG` (qx_choose_then `CT`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (DISJ_CASES_THEN (qx_choose_then `u` strip_assume_tac))))))))
  >- suspend "clamp_revert"
  >> suspend "clamp_success"
QED

Resume abi_decode_guarded_word_clause_conditional_mods[clamp_revert]:
  asm_x "store" kall_tac >>
  qpat_x_assum `cr = Abort Revert_abort u` SUBST_ALL_TAC >>
  qexistsl [`Abort Revert_abort u`,`CG`,`CT`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`Gf`,`t`,`tnf`] >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `obs` >> disch_tac >>
      qspecl_then [`start`,`loaded`,`finish'`,`obs`] mp_tac fn_has_code_split >>
      simp[] >> strip_tac >>
      qspecl_then [`loaded`,`clamped`,`finish'`,`obs`] mp_tac fn_has_code_split >>
      simp[] >> strip_tac >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists `t` >> simp[]) >>
  disj2_tac >> qexists `u` >> REFL_TAC
QED

Resume abi_decode_guarded_word_clause_conditional_mods[clamp_success]:
  qpat_x_assum `cr = OK u` SUBST_ALL_TAC >>
  `start.cs_next_var <= loaded.cs_next_var` by
    (`emit_op ADD [Var input;src_op] start = (src_addr,addressed)` by
       fs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     decide_tac) >>
  `loaded.cs_next_var <= clamped.cs_next_var /\ loaded.cs_next_id <= clamped.cs_next_id` by
    (qspecl_then [`val_op`,`clamp_info`,`loaded`] mp_tac ci_mono_compile_abi_clamp_basetype >>
     simp[ci_mono_def]) >>
  `start.cs_next_var <= clamped.cs_next_var` by decide_tac >>
  `?B. bop_scalar_seq {} UNIV (emitted_insts loaded clamped) B /\
       clamped.cs_current_insts = loaded.cs_current_insts ++ emitted_insts loaded clamped /\
       same_blocks loaded clamped` by
    (drule calldataClampPtrTheory.abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`{}`,`UNIV`] mp_tac) >> simp[] >>
     strip_tac >> qexists `UNIV` >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts loaded clamped)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >> simp[]) >>
  `alloca_history fn t` by
    (expand_owned `OS loaded t Gf tnf` (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl [`t`,`loaded`,`clamped`] >> simp[same_blocks_def,IS_PREFIX_APPEND] >>
     fs[same_blocks_def]) >>
  `not_fresh_at loaded input /\ local_ptrs_reserved ce loaded /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loaded x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loaded x)` by
    (rpt strip_tac >> FIRST
      [irule freshWritesTheory.not_fresh_at_mono >> qexists `start` >>
       rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       FIRST [first_assum ACCEPT_TAC, first_assum (drule_then ACCEPT_TAC)],
       irule local_ptrs_reserved_next_var >> qexists `start` >> simp[]]) >>
  `OS clamped u CG CT` by
    (fold_owned irule (BETA_RULE abi_decode_owned_scalar_frame_with_history_lower) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`Gf`,`t`,`loaded`,`tnf`] >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP CG x = FLOOKUP G x /\ op_taint CT (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at loaded x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `start` >> simp[]) >>
     qpat_assum `!x. not_fresh_at loaded x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `IO u` by
    (rewrite_abbr (fn th => pure_rewrite_tac [th]) `Abbrev (IO = _)` >>
     BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl [`s`,`start`] >>
     rewrite_abbr (fn th => qpat_assum `IO s`
       (assume_tac o BETA_RULE o PURE_REWRITE_RULE [th])) `Abbrev (IO = _)` >>
     simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  suspend "store"
QED

Resume abi_decode_guarded_word_clause_conditional_mods[store]:
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `p` strip_assume_tac) >>
  qpat_x_assum `dst = Var p` SUBST_ALL_TAC >>
  `not_fresh_at start p` by
    (qpat_assum `abi_decoder_operand_live start.cs_next_var (Var p)` mp_tac >>
     simp[NoAsms,abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `lookup_var p u = SOME (n2w d) /\ ptr_covers CG CT p u 32` by
    (qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _`
       (qspec_then `p` (drule_then strip_assume_tac)) >>
     conj_tac >- simp[GSYM eval_operand_def] >>
     qpat_assum `ptr_covers G tn p s _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  `local_ptrs_reserved ce clamped /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x)` by
    (rpt strip_tac >> FIRST
      [irule freshWritesTheory.not_fresh_at_mono >> qexists `start` >>
       rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       FIRST [first_assum ACCEPT_TAC, first_assum (drule_then ACCEPT_TAC)],
       irule local_ptrs_reserved_next_var >> qexists `start` >> simp[]]) >>
  `d+32 <= u.vs_alloca_next /\ w2n (n2w d : 256 word) = d` by
    (expand_owned `OS clamped u CG CT` (map_every assume_tac o CONJUNCTS) >>
     `alloca_inv u` by
       (qpat_assum `?H. V H` (qx_choose_then `H` assume_tac) >>
        qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
          (qspec_then `H` (drule_then (strip_assume_tac o CONJUNCT1))) >>
        drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `output_base+output_cap <= u.vs_alloca_next` by
       (qpat_assum `alloca_inv u`
          (mp_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
        strip_tac >>
        qpat_assum `!aid b sz. FLOOKUP u.vs_allocas aid = _ ==> _`
          (qspecl_then [`output_id`,`output_base`,`output_cap`] MATCH_MP_TAC) >>
        first_assum ACCEPT_TAC) >>
     `d < dimword (:256)` by
       (qpat_assum `d + type_memory_size tv <= _` mp_tac >>
        qpat_assum `output_base + output_cap < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     conj_tac >- (qpat_assum `d + type_memory_size tv <= _` mp_tac >>
        qpat_assum `type_memory_size tv = 32` (fn th => rewrite_tac[th]) >>
        qpat_assum `output_base + output_cap <= u.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     simp[]) >>
  `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+32 <= b) live` by
    (pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < _ /\ (b+k <= d \/ _)) live`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >> simp[]) >>
  qpat_assum `type_memory_size tv = 32` (fn sz =>
    map_every (fn q => qpat_assum q (assume_tac o PURE_REWRITE_RULE [sz]))
      [`d + type_memory_size tv <= _`,
       `w2n input_word + LENGTH input_bytes <= d \/ d + type_memory_size tv <= _`,
       `EVERY (\(a,bytes). a + LENGTH bytes <= d \/ d + type_memory_size tv <= a) protected`]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (expand_owned `OS clamped u CG CT` (map_every assume_tac o CONJUNCTS) >>
     owned_fmp ``u:venom_state``) >>
  rewrite_abbr (fn th => qpat_assum `IO u`
    (assume_tac o BETA_RULE o PURE_REWRITE_RULE [th])) `Abbrev (IO = _)` >>
  asm_x "store" (fn th => fold_owned
    (fn reduced => qpat_assum `w2n (n2w d : 256 word) = d` (fn addr =>
      drule_all (PURE_REWRITE_RULE [addr]
        (Q.INST [`dw` |-> `(n2w d : 256 word)`] reduced))))
    (SPEC_ALL th)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z` (qx_choose_then `ZG` (qx_choose_then `ZT`
      (map_every assume_tac o CONJUNCTS))))) >>
  suspend "finish"
QED

Resume abi_decode_guarded_word_clause_conditional_mods[finish]:
  `abi_decode_guarded_effect_core s tn t tnf` by
    simp[abi_decode_guarded_effect_core_def] >>
  `abi_decode_guarded_effect_core t tnf u CT` by
    (`u.vs_alloca_next = t.vs_alloca_next` by
       (qpat_assum `state_frame u = _` mp_tac >> simp[NoAsms,state_frame_def]) >>
     simp[abi_decode_guarded_effect_core_def]) >>
  `abi_decode_guarded_effect_core u CT z ZT` by
    (qpat_assum `ZT.t_mem SUBSET CT.t_mem` (assume_tac o REWRITE_RULE [SUBSET_DEF]) >>
     simp[abi_decode_guarded_effect_core_def]) >>
  `abi_decode_guarded_effect_core s tn u CT` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnf`,`t`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_guarded_effect_core s tn z ZT` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`CT`,`u`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at start x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP ZG x = FLOOKUP G x /\ op_taint ZT (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at clamped x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `start` >> simp[]) >>
     qpat_assum `!x. not_fresh_at clamped x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!i. i IN ZT.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `ZT.t_mem SUBSET CT.t_mem` mp_tac >> simp[SUBSET_DEF]) >>
  expand_owned `OS finish' z ZG ZT` (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`OK z`,`ZG`,`ZT`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`Gf`,`t`,`tnf`] >> conj_tac >- simp[] >>
      irule gas_origin_ptr_path_trans >> qexistsl [`CG`,`u`,`CT`] >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `obs` >> disch_tac >>
      qspecl_then [`start`,`loaded`,`finish'`,`obs`] mp_tac fn_has_code_split >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      qspecl_then [`loaded`,`clamped`,`finish'`,`obs`] mp_tac fn_has_code_split >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists `t` >> conj_tac >- first_assum (drule_then ACCEPT_TAC) >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists `u` >> conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  disj1_tac >> qexists `z` >>
  rpt (conj_tac >- FIRST
    [REFL_TAC, first_assum ACCEPT_TAC,
     qmatch_goalsub_rename_tac `LENGTH input_bytes + w2n input_word` >>
       once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC,
     qmatch_goalsub_rename_tac `IO z` >>
       simp_tac bool_ss [Abbr `IO`] >> first_assum ACCEPT_TAC]) >>
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >>
      qpat_assum `!i. i IN ZT.t_mem ==> i IN tn.t_mem`
        (qspec_then `i` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qx_gen_tac `v` >> strip_tac >>
      qpat_assum `!tv v. type_memory_size tv = 32 /\ _ ==> _`
        (qspecl_then [`tv`,`v`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise abi_decode_guarded_word_clause_conditional_mods
