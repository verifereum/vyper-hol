(* Scratch-aware observation boundaries for recursive calldata decoders. *)
Theory sourceRecursiveComplexPtr
Ancestors sourcePrimitiveComplexPtr robustCopyTransportPtr abiDecoderFrame bodyPtrDefs
  list rich_list arithmetic valueTypingMemoryProps abiEncoderInput valueEncodingProps exprSimProps exprLowering vyperABI contractABI abiEncoder
  canonicalMemberTraversalPtr abiDecoderMemberCons abiDecoderMemberSetup
  abiDecoderDynamic abiDecoderOffset abiDecoderOffsetHead abiDecoderCoherence abiDecoderHeadAdequacy
  abiDecoderDynamicLoopSetup sourceEncodingWindows sourceEncodingLayout abiDecoderMemberSlice
  abiDecoderContract abiDecodeRanges compileEnv emitHelperProps fragExec
  venomState venomExecSemantics ptrDiscipline decoderGhostFramePtr freshWrites
  abiDecoderCode abiDecoderReentry abiEncoderArrayFrame vyperValue
  exprLoweringProps finite_map pred_set

Theorem robust_value_footprint_frame:
  val_wf tv v /\ abi_decode_footprint_frame fp s t /\
  abi_footprint_disjoint p (val_footprint tv v) fp /\
  u.t_mem SUBSET tn.t_mem /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) ==>
  val_in_memory tv v p t.vs_memory /\
  (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v p mem)
Proof
  strip_tac >> drule_all abi_decode_footprint_frame_slice >> strip_tac >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v p mem` by
    metis_tac[calldata_member_robust_window_frame] >>
  simp[] >> first_x_assum irule >> simp[mem_agree_outside_def]
QED

Theorem decoded_tuple_prefix_footprint_frame:
  LIST_REL value_has_type tvs vs /\ k <= LENGTH tvs /\
  abi_decode_footprint_frame fp s t /\
  abi_footprint_disjoint d (SUM (MAP type_memory_size (TAKE k tvs))) fp /\
  u.t_mem SUBSET tn.t_mem /\
  (!i. i < k ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
  !i. i < k ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
  `i < LENGTH tvs /\ value_has_type (EL i tvs) (EL i vs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `val_wf (EL i tvs) (EL i vs)` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint (EL i tvs) (EL i vs) <= type_memory_size (EL i tvs)` by
    metis_tac[val_footprint_le] >>
  `SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
    SUM (MAP type_memory_size (TAKE k tvs))` by
    (qspec_then `type_memory_size` mp_tac abi_encoder_prefix_sum_bound >>
     disch_then (qspecl_then [`TAKE k tvs`, `i`] mp_tac) >>
     simp[TAKE_TAKE, EL_TAKE, MIN_DEF]) >>
  irule robust_value_footprint_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`fp`, `s`, `tn`] >> simp[] >>
  gvs[abi_footprint_disjoint_def] >> rpt strip_tac >>
  qpat_x_assum `!d' sz. MEM (d',sz) fp ==> _` drule >> decide_tac
QED


Theorem canonical_recursive_complex_suffix_ptr:
  (!i mid en q childsrc r H u.
    i < LENGTH tys /\
    compile_abi_decode_to_buf (Var q) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce (EL i tys)) mid = ((),en) /\
    eval_operand (Var q) r = SOME (n2w (d + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    eval_operand childsrc r = SOME (n2w (cdsbase + abi_tuple_child_offset ats avs i)) /\
    mem_bytes_at (cdsbase + abi_tuple_child_offset ats avs i)
      (LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs)))
      r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (EL i tys)) (EL i avs) /\
    ptr_covers H u q r (type_memory_size (EL i tvs)) /\
    ptr_covers H u root r cap /\ op_taint u childsrc = {} /\ op_prov H childsrc = NONE /\
    fresh_vars_wrt mid r /\ fn_has_code mid en fn /\ fn_inst_ids_distinct fn /\
    allocas_from lo r /\ ~ctx_has_dalloca ctx /\ ~r.vs_halted /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
    ?t J v fp.
      ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt en t /\
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
      (!mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
        val_in_memory (EL i tvs) (EL i vs)
          (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) /\
      abi_decode_footprint_frame
        ((d + SUM (MAP type_memory_size (TAKE i tvs)), type_memory_size (EL i tvs))::fp) r t /\
      abi_footprint_disjoint d cap fp /\ allocas_from lo t /\ ptr_covers J v root t cap /\
      (!op w. abi_decoder_operand_live mid.cs_next_var op /\ eval_operand op r = SOME w ==>
        eval_operand op t = SOME w) /\
      (!x. not_fresh_at mid x ==> FLOOKUP J x = FLOOKUP H x /\
        op_taint v (Var x) = op_taint u (Var x)) /\
      v.t_mem SUBSET u.t_mem /\ v.t_stor = u.t_stor /\
      v.t_trans = u.t_trans /\ v.t_imm = u.t_imm /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG J v t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG H u r)) ==>
  !n k sa s G tn.
    LENGTH tys - k = n /\ k <= LENGTH tys /\
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
    ats = MAP (vyper_to_abi_type env) tys /\ LENGTH elems = LENGTH tys /\
    (!i. i < LENGTH tys ==>
      EL i elems = (type_to_abi_dec_info sf ce (EL i tys),
        abi_member_head_size (EL i ats), type_memory_size (EL i tvs))) /\
    compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP k elems) (SUM (MAP abi_member_head_size (TAKE k ats)))
      (SUM (MAP type_memory_size (TAKE k tvs))) sa = ((),sb) /\
    mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) s.vs_call_ctx.cc_calldata =
      enc (Tuple ats) (ListV avs) /\
    cdsbase + LENGTH (enc (Tuple ats) (ListV avs)) < dimword (:256) /\
    (!i. i < LENGTH tys ==> cdsbase + abi_tuple_child_offset ats avs i < dimword (:256)) /\
    lookup_var root s = SOME (n2w d) /\ not_fresh_at sa root /\
    abi_decoder_operand_live sa.cs_next_var src /\
    abi_decoder_operand_live sa.cs_next_var (Var root) /\
    (!q. src = Var q ==> not_fresh_at sa q) /\
    eval_operand src s = SOME (n2w cdsbase) /\ ptr_covers G tn root s cap /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    SUM (MAP type_memory_size tvs) <= cap /\ d + cap < dimword (:256) /\
    fresh_vars_wrt sa s /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!i. i < k ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
    ?t H u fp.
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
      (!i. i < LENGTH tys ==>
        val_in_memory (EL i tvs) (EL i vs)
          (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
        (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs)
            (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)) /\
      abi_decode_footprint_frame ((d,cap)::fp) s t /\
      abi_footprint_disjoint d cap fp /\ allocas_from lo t /\ ptr_covers H u root t cap /\
      (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
        eval_operand op t = SOME w) /\
      (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (mk_asm "child") >> Induct
  >- (rpt gen_tac >> strip_tac >>
      `k = LENGTH tys /\ DROP k elems = []` by simp[DROP_EQ_NIL] >>
      gvs[Once compile_abi_decode_to_buf_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`, `[]`] >>
      simp[abi_decode_footprint_frame_refl, abi_footprint_disjoint_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[mem_agree_outside_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!k sa s G tn. _` (mk_asm "ih") >>
  `k < LENGTH tys /\ SUC k <= LENGTH tys /\ LENGTH tys - SUC k = n` by decide_tac >>
  `LENGTH tvs = LENGTH tys /\ LENGTH ats = LENGTH tys` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `DROP k elems = EL k elems :: DROP (SUC k) elems` by metis_tac[DROP_CONS_EL] >>
  `EL k elems = (type_to_abi_dec_info sf ce (EL k tys),
    abi_member_head_size (EL k ats), type_memory_size (EL k tvs))` by simp[] >>
  `abi_decoder_coherent ce env sf (EL k tys) (EL k tvs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce (EL k tys)) = is_dynamic (EL k ats)` by
    (drule abi_decoder_nonempty_type_offset >>
     (impl_tac >-
       (`evaluate_type env (EL k tys) = SOME (EL k tvs)` by
          metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
        spose_not_then assume_tac >>
        `?elem. EL k tys = ArrayT elem (Fixed 0)` by
          metis_tac[abi_decoder_zero_array_type] >>
        gvs[evaluate_type_def, AllCaseEqs()])) >>
     simp[EL_MAP]) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `DROP k elems = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `EL k elems = _` (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) _ _ _ sa = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ CALLDATALOAD (Lit 0w) (Lit 0w) _ mid = ((),en)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code sa mid fn /\ fn_has_code mid en fn` by metis_tac[fn_has_code_split] >>
  `fresh_vars_wrt mid s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[] >>
     drule abi_decode_member_setup_counters >> simp[]) >>
  suspend "navigate"
QED

Resume canonical_recursive_complex_suffix_ptr[navigate]:
  qabbrev_tac `ats = MAP (vyper_to_abi_type env) tys` >>
  `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) <= cap` by
    (qspec_then `type_memory_size` mp_tac abi_encoder_prefix_sum_bound >>
     disch_then (qspecl_then [`tvs`, `k`] mp_tac) >> simp[]) >>
  `d < dimword (:256) /\ d + SUM (MAP type_memory_size (TAKE k tvs)) < dimword (:256)` by
    decide_tac >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `k < LENGTH ats` by simp[Abbr `ats`] >>
  `is_dynamic (EL k ats) ==>
    abi_decode_load CALLDATALOAD
      (n2w (cdsbase + SUM (MAP abi_member_head_size (TAKE k ats))) : bytes32) s =
      n2w (abi_tuple_child_offset ats avs k) /\
    cdsbase + abi_tuple_child_offset ats avs k < dimword (:256)` by
    (strip_tac >> conj_tac >- (irule structural_tuple_indexed_offset_load >>
      simp[abi_decode_source_def, Excl "enc_def"] >> gvs[]) >> simp[]) >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `dec_info_needs_offset _ = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  drule_all calldata_member_setup_source_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_operand (FST ops) r = SOME (n2w (cdsbase + abi_tuple_child_offset ats avs k))` by
    (Cases_on `is_dynamic (EL k ats)` >> gvs[abi_tuple_child_offset_def]) >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) r.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by gvs[abi_decoder_address_frame_def] >>
  `LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = abi_member_head_size ty) ats avs` by
    metis_tac[] >>
  drule_all structural_tuple_indexed_source >> strip_tac >>
  `ptr_covers H u root r cap` by metis_tac[ptr_covers_frame] >>
  `allocas_from lo r /\ ~r.vs_halted` by
    (gvs[abi_decoder_address_frame_def, allocas_from_def] >> gvs[]) >>
  `compile_abi_decode_to_buf (Var q) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (EL k tys)) mid = ((),en)` by
    gvs[] >>
  `eval_operand (Var q) r = SOME (n2w (d + SUM (MAP type_memory_size (TAKE k tvs))))` by
    gvs[] >>
  `mem_bytes_at (cdsbase + abi_tuple_child_offset ats avs k)
    (LENGTH (enc (vyper_to_abi_type env (EL k tys)) (EL k avs))) r.vs_call_ctx.cc_calldata =
    enc (vyper_to_abi_type env (EL k tys)) (EL k avs)` by
    gvs[Abbr `ats`, EL_MAP, Excl "enc_def"] >>
  asm "child" (qspec_then `k` (drule_at (Pos (el 2)))) >>
  disch_then (qspecl_then [`r`, `H`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> suspend "prefix"
QED

Resume canonical_recursive_complex_suffix_ptr[prefix]:
  `abi_decode_footprint_frame
    ((d + SUM (MAP type_memory_size (TAKE k tvs)), type_memory_size (EL k tvs))::fp) s t` by
    gvs[abi_decoder_address_frame_def, abi_decode_footprint_frame_def] >>
  `abi_footprint_disjoint d (SUM (MAP type_memory_size (TAKE k tvs)))
    ((d + SUM (MAP type_memory_size (TAKE k tvs)), type_memory_size (EL k tvs))::fp)` by
    (simp[abi_footprint_disjoint_def] >> rpt strip_tac >>
     qpat_x_assum `abi_footprint_disjoint d cap fp` mp_tac >>
     simp[abi_footprint_disjoint_def] >> disch_then drule >> decide_tac) >>
  `v.t_mem SUBSET tn.t_mem` by gvs[] >>
  `!i. i < k ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
    (!mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)` by
    (gen_tac >> disch_tac >> irule decoded_tuple_prefix_footprint_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`((d + SUM (MAP type_memory_size (TAKE k tvs)),
       type_memory_size (EL k tvs))::fp)`, `k`, `s`, `tn`] >> simp[]) >>
  `!i. i < SUC k ==> !mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (rpt strip_tac >> Cases_on `i < k` >- metis_tac[] >>
     `i = k` by decide_tac >> gvs[]) >>
  suspend "tail"
QED

Resume canonical_recursive_complex_suffix_ptr[tail]:
  `!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!op w. abi_decoder_operand_live mid.cs_next_var op /\ _ ==> _` irule >>
     conj_tac >- gvs[abi_decoder_address_frame_def] >>
     irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP J x = FLOOKUP G x /\
    op_taint v (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at mid x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `lookup_var root t = SOME (n2w d) /\ eval_operand src t = SOME (n2w cdsbase)` by
    (conj_tac
     >- (qpat_assum `!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = _ ==> eval_operand op t = _`
           (qspecl_then [`Var root`, `n2w d`] mp_tac) >>
         (impl_tac >- simp[eval_operand_def]) >>
         rewrite_tac[eval_operand_def] >> disch_then ACCEPT_TAC) >>
     first_assum irule >> simp[]) >>
  `op_taint v src = {} /\ op_prov J src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `sa.cs_next_var <= en.cs_next_var` by decide_tac >>
  `not_fresh_at en root /\ (!q. src = Var q ==> not_fresh_at en q)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `abi_decoder_operand_live en.cs_next_var src /\
   abi_decoder_operand_live en.cs_next_var (Var root)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) t.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by gvs[abi_decode_footprint_frame_def] >>
  `SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + abi_member_head_size (EL k ats) /\
   SUM (MAP type_memory_size (TAKE (SUC k) tvs)) =
     SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs)` by
    simp[TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC] >>
  asm "ih" (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`en`, `t`, `J`, `v`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> gvs[])) >> strip_tac >>
  suspend "compose"
QED

Resume canonical_recursive_complex_suffix_ptr[compose]:
  asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
  `abi_decode_footprint_frame ((d,cap)::(fp ++ fp')) s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `((d + SUM (MAP type_memory_size (TAKE k tvs)),
       type_memory_size (EL k tvs))::fp)` >> simp[] >>
     rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`, `cap`] >> simp[]) >>
     qexistsl_tac [`d'`, `sz`] >> simp[]) >>
  `abi_decode_footprint_frame ((d,cap)::(fp ++ fp')) t t'` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `((d,cap)::fp')` >> simp[] >>
     rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`, `cap`] >> simp[]) >>
     qexistsl_tac [`d'`, `sz`] >> simp[]) >>
  qexistsl_tac [`t'`, `H'`, `u'`, `fp ++ fp'`] >>
  simp[abi_footprint_disjoint_append] >>
  conj_tac >- metis_tac[abi_decode_footprint_frame_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op w. abi_decoder_operand_live en.cs_next_var op /\ _ ==> _` irule >>
      conj_tac >- metis_tac[] >>
      irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at en x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> metis_tac[]) >>
  metis_tac[SUBSET_TRANS]
QED

Finalise canonical_recursive_complex_suffix_ptr
