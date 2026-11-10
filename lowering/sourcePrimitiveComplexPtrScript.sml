(* Finite canonical complex decoders: compiler and prefix frame boundaries. *)
Theory sourcePrimitiveComplexPtr
Ancestors canonicalMemberTraversalPtr robustCopyTransportPtr abiDecoderFrameCompose
  abiEncoderInput valueTypingMemoryProps exprSimProps abiDecoderMemberSetup
  emitHelperProps compileEnv abiDecoderContract bodyPtrDefs
  list rich_list arithmetic pred_set abiDecoderMemberCons abiEncoder
  abiDecoderCode fragExec abiDecoderDynamic decoderGhostFramePtr freshWrites
  venomState venomExecSemantics ptrDiscipline abiDecoderReentry

Theorem member_setup_entry_freshness[local]:
  abi_decode_member_setup dst src opc (Lit 0w) hi dyn ao vo sa = (ops,mid) /\
  fresh_vars_wrt sa s ==> fresh_vars_wrt mid s
Proof
  strip_tac >> drule abi_decode_member_setup_counters >> strip_tac >>
  irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[] >>
  Cases_on `dyn` >> simp[] >> Cases_on `hi = Lit 0w` >> simp[]
QED

Theorem decoded_tuple_prefix_robust_frame:
  LIST_REL value_has_type tvs vs /\ k <= LENGTH tvs /\
  abi_decode_frame (d + SUM (MAP type_memory_size (TAKE k tvs))) C s t /\
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
  rpt strip_tac >>
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
  `mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
    (val_footprint (EL i tvs) (EL i vs)) t.vs_memory =
    mem_bytes_at (d + SUM (MAP type_memory_size (TAKE i tvs)))
      (val_footprint (EL i tvs) (EL i vs)) s.vs_memory` by
    (gvs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (metis_tac[calldata_member_robust_window_frame]) >>
  simp[] >> first_x_assum irule >> simp[mem_agree_outside_def]
QED

Theorem complex_member_phase_code[local]:
  compile_abi_decode_complex_elems dst src opc (Lit 0w) hi ((ei,az,mz)::rest)
    ao vo sa = ((),sb) /\ abi_decode_source_opcode opc /\
  fn_has_code sa sb fn /\ fresh_vars_wrt sa s ==>
  ?ops mid en.
    abi_decode_member_setup dst src opc (Lit 0w) hi (dec_info_needs_offset ei)
      ao vo sa = (ops,mid) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc (Lit 0w) hi ei mid = ((),en) /\
    compile_abi_decode_complex_elems dst src opc (Lit 0w) hi rest (ao+az) (vo+mz) en = ((),sb) /\
    fn_has_code sa mid fn /\ fn_has_code mid en fn /\ fn_has_code en sb fn /\
    cs_extends sa mid /\ cs_extends mid en /\ cs_extends en sb /\
    fresh_vars_wrt mid s
Proof
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup dst src opc (Lit 0w) hi _ ao vo sa = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ opc (Lit 0w) hi ei mid = ((),en)` >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code sa mid fn /\ fn_has_code mid en fn` by
    (metis_tac[fn_has_code_split]) >>
  `fresh_vars_wrt mid s` by metis_tac[member_setup_entry_freshness] >>
  simp[]
QED

(* The complete parent stays fixed while k advances through the suffix.
   All runtime and ghost witnesses precede the safety observer D. *)
Theorem canonical_primitive_complex_suffix_ptr:
  !n k sa s G tn.
  LENGTH tys - k = n /\ k <= LENGTH tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
  ats = MAP (vyper_to_abi_type env) tys /\ LENGTH elems = LENGTH tys /\
  (!i. i < LENGTH tys ==>
    EL i elems = (type_to_abi_dec_info sf ce (EL i tys),
      abi_member_head_size (EL i ats), type_memory_size (EL i tvs)) /\
    ((?clamp. type_to_abi_dec_info sf ce (EL i tys) = DecPrimWord clamp /\
       is_word_type (EL i tys) /\ type_memory_size (EL i tvs) = 32) \/
     (?m. type_to_abi_dec_info sf ce (EL i tys) = DecBytestring m /\
       type_memory_size (EL i tvs) = abi_decode_bytes_copy_size m /\
       m < dimword (:256)))) /\
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
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    (!i. i < LENGTH tys ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (EL i tvs) (EL i vs)
          (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)) /\
    abi_decode_frame d cap s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Induct >- suspend "empty" >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!k sa s G tn. _` (mk_asm "ih") >>
  `k < LENGTH tys /\ SUC k <= LENGTH tys /\ LENGTH tys - SUC k = n` by decide_tac >>
  `LENGTH tvs = LENGTH tys /\ LENGTH ats = LENGTH tys` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `DROP k elems = EL k elems :: DROP (SUC k) elems` by
    metis_tac[DROP_CONS_EL] >>
  qpat_assum `!i. i < LENGTH tys ==> EL i elems = _ /\ _`
    (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `abi_decoder_coherent ce env sf (EL k tys) (EL k tvs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce (EL k tys)) = is_dynamic (EL k ats)` by
    (drule abi_decoder_coherent_dynamic >> strip_tac >>
     qpat_x_assum `(?clamp. _ /\ _ /\ _) \/ (?m. _ /\ _ /\ _)` mp_tac >>
     strip_tac >> gvs[EL_MAP, abi_decoder_dynamic_def, dec_info_needs_offset_def]) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `DROP k elems = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `EL k elems = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all complex_member_phase_code >> strip_tac >>
  suspend "member"
QED

Resume canonical_primitive_complex_suffix_ptr[empty]:
  rpt gen_tac >> strip_tac >>
  `k = LENGTH tys /\ DROP k elems = []` by simp[DROP_EQ_NIL] >>
  gvs[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[abi_decode_frame_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[mem_agree_outside_def]
QED

Resume canonical_primitive_complex_suffix_ptr[member]:
  `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) <= cap` by
    (qspec_then `type_memory_size` mp_tac abi_encoder_prefix_sum_bound >>
     disch_then (qspecl_then [`tvs`, `k`] mp_tac) >> simp[]) >>
  `d < dimword (:256) /\
   d + SUM (MAP type_memory_size (TAKE k tvs)) < dimword (:256) /\
   type_memory_size (EL k tvs) < dimword (:256)` by decide_tac >>
  `type_to_abi_dec_info sf ce (EL k tys) = type_to_abi_dec_info sf ce (EL k tys)` by simp[] >>
  `cdsbase + abi_tuple_child_offset ats avs k < dimword (:256)` by simp[] >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `dec_info_needs_offset _ = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  drule_all canonical_tuple_primitive_traversal_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `fresh_vars_wrt en r` >> suspend "tail"
QED

Resume canonical_primitive_complex_suffix_ptr[tail]:
  `k <= LENGTH tvs` by decide_tac >>
  `!i. i < k ==>
     val_in_memory (EL i tvs) (EL i vs)
       (d + SUM (MAP type_memory_size (TAKE i tvs))) r.vs_memory /\
     (!mem. mem_agree_outside u.t_mem r.vs_memory mem ==>
       val_in_memory (EL i tvs) (EL i vs)
         (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)` by
    (gen_tac >> disch_tac >> irule decoded_tuple_prefix_robust_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!i. i < SUC k ==> !mem. mem_agree_outside u.t_mem r.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (rpt strip_tac >> Cases_on `i < k` >- metis_tac[] >>
     `i = k` by decide_tac >> gvs[]) >>
  `abi_decode_frame d cap s r` by
    (irule abi_decode_frame_widen >>
     qexistsl_tac [`d + SUM (MAP type_memory_size (TAKE k tvs))`,
       `type_memory_size (EL k tvs)`] >> simp[]) >>
  `lookup_var root r = SOME (n2w d) /\ eval_operand src r = SOME (n2w cdsbase)` by
    (conj_tac
     >- (qpat_assum `!op w. abi_decoder_operand_live sa.cs_next_var op /\ _ ==> _`
           (qspecl_then [`Var root`, `n2w d`] mp_tac) >>
         (impl_tac >- simp[eval_operand_def]) >>
         rewrite_tac[eval_operand_def] >> disch_then ACCEPT_TAC) >>
     first_assum irule >> simp[]) >>
  `ptr_covers H u root r cap` by metis_tac[ptr_covers_frame] >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `sa.cs_next_var <= en.cs_next_var` by decide_tac >>
  `not_fresh_at en root /\ (!q. src = Var q ==> not_fresh_at en q)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `abi_decoder_operand_live en.cs_next_var src /\
   abi_decoder_operand_live en.cs_next_var (Var root)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `allocas_from lo r` by
    metis_tac[allocas_from_def] >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) r.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by gvs[abi_decode_frame_def] >>
  `SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + abi_member_head_size (EL k ats) /\
   SUM (MAP type_memory_size (TAKE (SUC k) tvs)) =
     SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs)` by
    simp[TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC] >>
  asm "ih" (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`en`, `r`, `H`, `u`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> gvs[])) >> strip_tac >>
  qexistsl_tac [`t`, `H'`, `u'`] >> simp[] >> suspend "compose"
QED

Resume canonical_primitive_complex_suffix_ptr[compose]:
  conj_tac >- metis_tac[abi_decode_frame_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op w. abi_decoder_operand_live en.cs_next_var op /\ _ ==> _` irule >>
      metis_tac[abi_decoder_operand_live_mono]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at en x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  metis_tac[SUBSET_TRANS]
QED

Finalise canonical_primitive_complex_suffix_ptr

Theorem canonical_primitive_complex_ptr:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
  ats = MAP (vyper_to_abi_type env) tys /\ LENGTH elems = LENGTH tys /\
  (!i. i < LENGTH tys ==>
    EL i elems = (type_to_abi_dec_info sf ce (EL i tys),
      abi_member_head_size (EL i ats), type_memory_size (EL i tvs)) /\
    ((?clamp. type_to_abi_dec_info sf ce (EL i tys) = DecPrimWord clamp /\
       is_word_type (EL i tys) /\ type_memory_size (EL i tvs) = 32) \/
     (?m. type_to_abi_dec_info sf ce (EL i tys) = DecBytestring m /\
       type_memory_size (EL i tvs) = abi_decode_bytes_copy_size m /\
       m < dimword (:256)))) /\
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    elems 0 0 sa = ((),sb) /\
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
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    (!i. i < LENGTH tys ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (EL i tvs) (EL i vs)
          (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)) /\
    abi_decode_frame d cap s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all (SRULE [Excl "enc_def"]
    (Q.SPECL [`LENGTH (tys : vyperAST$type list)`, `0`] canonical_primitive_complex_suffix_ptr)) >>
  disch_then (qspec_then `PG` ACCEPT_TAC)
QED
