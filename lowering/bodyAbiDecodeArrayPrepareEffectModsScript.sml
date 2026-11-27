Theory bodyAbiDecodeArrayPrepareEffectMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeArrayPrepare
  bodyFullAbiDecodeArrayPrepareSuffix bodyFullAbiDecodeGuardReadObserved
  bodyFullAbiDecodeScalarObserved bodyFullAbiDecodeBytesArithmetic
  bodyFullAbiDecodeScalarNoAlloca bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeOwnedStateProps abiDecodePtrRead abiDecodePtrBytesMember
  abiDecodePtrMemberFrame abiDecoderReentry abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderGuard abiDecoderGuards
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome bodyPtrDefs
  exprLoweringProps emitHelperProps compileEnv fragExec emitHelper abiEncoder
  venomState venomInst venomExecSemantics words finite_map ptrDiscipline freshWrites
  fragGasOriginPtr fragGasOriginPtrLoop fragGasPath forPtrAllocationFrame
  valueEncodingProps venomMemProps loweringShapeRules arithmetic list rich_list
  loweringStateRelDefs stateFrame pred_set
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

(* The success decoration preserves the actual result, observer paths and
   ghost binders of the two selectors.  Their free phase parameters are closed
   independently, so the suffix can be used at the reached count state. *)
fun array_selector_effect sname tnname th =
  let
    val old = beta (concl th)
    val (qs,body) = strip_forall old
    val (pre,post) = dest_imp body
    val (ws,paths) = strip_exists post
    val (_,_,tf) = triple "array selector result" ws
    val (physical,rest) = dest_conj paths
    val (observer,branches) = dest_conj rest
    val (aborted,normal) = dest_disj branches
    val (vs,fields) = strip_exists normal
    val all = free_vars old @ qs
    val e = effect (param all sname) (param all tnname) (hd vs) tf
    val post' = list_mk_exists (ws, mk_conj (physical, mk_conj (observer,
      mk_disj (aborted, list_mk_exists (vs, mk_conj (fields,e))))))
    val tm = checked "array selector" old (list_mk_forall (qs,mk_imp (pre,post')))
  in list_mk_forall (free_vars tm,tm) end;

val suffix_all = array_selector_effect "u" "tnu" abi_decode_array_prepare_suffix_width_joint;
val prepare_all = array_selector_effect "s" "tn" abi_decode_array_prepare_width_joint;

(* Split observer code by the very compiler cursors used by the finite runs. *)
Theorem prepare_trace[local]:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn stride
    start = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) ==>
  ?head head_st addr_st read_st count_st first reload_st.
    abi_decode_bytes_head src hi start = (head,head_st) /\
    compile_abi_dec_addr (Var input) src head_st = (addr,addr_st) /\
    emit_op MLOAD [addr] addr_st = (first,read_st) /\
    abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),count_st) /\
    abi_decode_dynarray_payload_guard head first stride hi count_st = ((),guard_st) /\
    emit_op MLOAD [addr] guard_st = (cnt,reload_st) /\
    emit_void MSTORE [dst;cnt] reload_st = ((),header_st) /\
    cs_extends start head_st /\ cs_extends head_st addr_st /\
    cs_extends addr_st read_st /\ cs_extends read_st count_st /\
    cs_extends head_st read_st /\ cs_extends start count_st /\
    cs_extends count_st guard_st /\ cs_extends guard_st reload_st /\
    cs_extends reload_st header_st /\ cs_extends count_st header_st /\
    (!obs. fn_has_code start header_st obs ==>
      fn_has_code start head_st obs /\ fn_has_code head_st read_st obs /\
      fn_has_code read_st count_st obs /\ fn_has_code count_st header_st obs) /\
    (!obs. fn_has_code count_st header_st obs ==>
      fn_has_code count_st guard_st obs /\ fn_has_code guard_st reload_st obs /\
      fn_has_code reload_st header_st obs)
Proof
  simp[abi_decode_dynarray_position_prefix_trace] >> strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_bytes_head src hi start = (head,head_st)` >>
  rename1 `compile_abi_dec_addr (Var input) src head_st = (addr,addr_st)` >>
  rename1 `emit_op MLOAD [addr] addr_st = (first,read_st)` >>
  rename1 `emit_op MLOAD [addr] guard_st = (cnt,reload_st)` >>
  rename1 `emit_void MSTORE [dst;cnt] reload_st = ((),header_st)` >>
  `abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),count_st)` by
    simp[abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `cs_extends start head_st` by
    (drule abi_decode_bytes_head_fragment_shape >>
     simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
     simp[IS_PREFIX_APPEND]) >>
  `emit_op ADD [Var input;src] head_st = (addr,addr_st)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends head_st addr_st /\ cs_extends addr_st read_st /\
   cs_extends guard_st reload_st` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `cs_extends read_st count_st` by
    (drule abi_decode_le_guard_shape >>
     qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, inst_extends_def] >> rpt strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends count_st guard_st` by
    (`guard_st.cs_blocks = count_st.cs_blocks /\
      guard_st.cs_current_bb = count_st.cs_current_bb` by
       (qpat_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
             emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
             comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        Cases_on `hi = Lit 0w` >> simp[comp_return_def] >> strip_tac >>
        gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
            fresh_var_def, fresh_id_def]) >>
     drule abi_decode_dynarray_payload_guard_shape >>
     simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
     simp[IS_PREFIX_APPEND]) >>
  `cs_extends reload_st header_st` by
    (qspecl_then [`MSTORE`, `[dst;cnt]`, `reload_st`, `K T`]
       mp_tac externalEntryShapeTheory.emit_void_labels >> simp[]) >>
  `cs_extends head_st read_st /\ cs_extends guard_st header_st` by
    metis_tac[cs_extends_trans] >>
  `cs_extends head_st count_st /\ cs_extends count_st header_st` by
    metis_tac[cs_extends_trans] >>
  qexists_tac `count_st` >> simp[] >>
  `cs_extends start count_st /\ cs_extends read_st header_st /\
   cs_extends head_st header_st` by metis_tac[cs_extends_trans] >>
  simp[] >> rpt strip_tac >> metis_tac[fn_has_code_split]
QED

(* Lift the finite scalar certificate to the owned resources, without
   changing either its selected state or its provenance/taint witnesses. *)
val scalar_old = beta (concl abi_decode_bytes_scalar_frame_joint);
val scalar_plus =
  let val (pre,post) = dest_imp scalar_old
      val (ws,fields) = strip_exists post
      val (u,_,tf) = triple "scalar witnesses" ws
      val ps = free_vars scalar_old
      val s = param ps "s"
      val sa = param ps "sa"
      val sb = param ps "sb"
      val ctx = param ps "ctx"
      val obs = ``!obs. fn_has_code ^sa ^sb obs ==> gas_path ^ctx obs ^s 0 (OK ^u)``
  in mk_imp (pre,list_mk_exists (ws,mk_conj (fields,
       mk_conj (effect s (param ps "tn") u tf,obs)))) end;

Theorem prepare_scalar_frame[local]:
  ^scalar_plus
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  drule_all bodyFullBopWordSuccessTheory.bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `u`] >>
     qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tnf (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`, lookup_var_def, op_taint_def] >> gvs[]) >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[IS_PREFIX_APPEND] >>
     fs[inst_extends_def]) >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    (qpat_assum `sb.cs_current_insts = _` (fn th => simp[th])) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gf,tnf)` by
    (simp_tac bool_ss [Abbr `u`] >>
     qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
    (simp_tac bool_ss [Abbr `u`] >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
     drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >>
     simp[EVERY_CONJ, LENGTH_NIL, FILTER_EQ_NIL]) >>
  `abi_decode_guarded_effect_core s tn u tnf` by simp[abi_decode_guarded_effect_core_def] >>
  mp_tac (abi_decode_owned_scalar_frame_with_history_lower |> SPEC_ALL |> BETA_RULE |>
    Q.INST [`t` |-> `u`, `G'` |-> `Gf`, `tn'` |-> `tnf`]) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[] >> simp[Abbr `u`]
QED

fun guard_selector_effect th =
  let
    val old = beta (concl th)
    val (pre,post) = dest_imp old
    val (normal,aborted) = dest_disj post
    val (ws,fields) = strip_exists normal
    val (t,_,tf) = triple "finite guard witnesses" ws
    val ps = free_vars old
    val e = effect (param ps "s") (param ps "tn") t tf
  in checked "finite guard" old
    (mk_imp (pre,mk_disj (list_mk_exists (ws,mk_conj (fields,e)),aborted))) end;

val head_plus = guard_selector_effect abi_decode_bytes_head_joint_observed;
val count_plus = guard_selector_effect abi_decode_bytes_count_joint_observed;

Theorem prepare_head[local]:
  ^head_plus
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;hi;Lit 32w}
      (emitted_insts sa sb) B /\ {src;hi;Lit 32w} SUBSET B /\ head IN B` by
    (irule abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {src;hi;Lit 32w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `lo <= s.vs_alloca_next` by first_assum ACCEPT_TAC >>
  drule_all abi_decode_bytes_head_run >> strip_tac
  >- suspend "normal" >>
  disj2_tac >> drule_all member_scalar_revert_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

Resume prepare_head[normal]:
  disj1_tac >>
  `off+32 <= h` by
    (irule abi_decode_checked_add_bound >>
     asm_simp_tac (srw_ss()) [LESS_MOD] >>
     conj_tac >- simp[dimword_def] >>
     gvs[w2n_n2w, MOD_LESS_EQ, LESS_EQ_TRANS]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    metis_tac[abi_decode_scalar_seq_no_alloca] >>
  drule_all prepare_scalar_frame >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS))))) >>
  `eval_operand head u = SOME (n2w (off+32))` by
    (qpat_x_assum `u = _` SUBST1_TAC >> Cases_on `head` >>
     fs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `u = _` kall_tac >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  first_x_assum drule >> simp[]
QED

Finalise prepare_head

Theorem prepare_count[local]:
  ^count_plus
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb /\ inst_extends sa sb` by
    (qpat_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit (n2w n)}
      (emitted_insts sa sb) B /\ {cnt;Lit (n2w n)} SUBSET B` by
    (irule abi_decode_le_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt;Lit (n2w n)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `(?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ c <= n) \/
   (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)` by
    (Cases_on `emit_op GT [cnt;Lit (n2w n)] sa` >>
     rename1 `emit_op GT [cnt;Lit (n2w n)] sa = (many,c1)` >>
     Cases_on `emit_op ISZERO [many] c1` >>
     rename1 `emit_op ISZERO [many] c1 = (ok,c2)` >>
     `emit_void ASSERT [ok] c2 = ((),sb)` by
       (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
        asm_simp_tac bool_ss [abi_decode_le_guard_def, comp_bind_def, LET_THM, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND]) >>
     drule_all abi_decode_bytes_count_run >> simp[]) >>
  pop_assum strip_assume_tac
  >- (disj1_tac >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
        metis_tac[abi_decode_scalar_seq_no_alloca] >>
      drule_all prepare_scalar_frame >>
      disch_then (qspecl_then [`explicit`,`PG`]
        (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf`
          (map_every assume_tac o CONJUNCTS))))) >>
      qpat_x_assum `u = _` kall_tac >>
      qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all member_scalar_revert_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

(* Load uses its explicit ADD;MLOAD certificate, including the fresh address
   window.  The lower path theorem selects the same ghosts by finite-sequence
   uniqueness, not by equality of machine endpoints. *)
val relative_plus =
  let val old = beta (concl abi_decode_bytes_owned_load_frame_joint_observed)
      val (pre,post) = dest_imp old
      val (ws,fields) = strip_exists post
      val [_,_,t,_,tf] = ws
      val ps = free_vars old
  in checked "relative load" old
    (mk_imp (pre,list_mk_exists (ws,mk_conj (fields,
         effect (param ps "s") (param ps "tn") t tf)))) end;

Theorem prepare_load[local]:
  ^relative_plus
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST [`D` |-> `ARB`]) >>
  disch_then (qspec_then `PG` (qx_choose_then `out` (qx_choose_then `t`
    (qx_choose_then `Gp` (qx_choose_then `tp` (map_every assume_tac o CONJUNCTS)))))) >>
  drule_all abi_decode_relative_load_joint_lower >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `out2`
    (qx_choose_then `t2` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS)))))) >>
  `out2 = out /\ t2 = t` by
    (conj_tac >- metis_tac[operand_11] >>
     `t2 with vs_inst_idx := s.vs_inst_idx = t with vs_inst_idx := s.vs_inst_idx` by
       (qpat_x_assum `run_inst_seq _ s = OK (t2 with vs_inst_idx := _)` mp_tac >> simp[]) >>
     qpat_x_assum `_ with vs_inst_idx := _ = _ with vs_inst_idx := _`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sc.cs_current_insts`) >>
     simp[venom_state_component_equality]) >>
  `inst_seq_ptr ARB lo ctx fn PG G tn (emitted_insts sa sc) s Gp tp` by
    (irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `ARB` >> simp[]) >>
  qpat_assum `!D. inst_seq_ptr D lo ctx fn PG G tn _ s Gf tnf` (qspec_then `ARB` assume_tac) >>
  `Gf = Gp /\ tnf = tp` by
    (irule fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique >>
     metis_tac[]) >>
  qpat_x_assum `t2 = t` SUBST_ALL_TAC >>
  qpat_x_assum `out2 = out` SUBST_ALL_TAC >>
  qpat_x_assum `Gf = Gp` SUBST_ALL_TAC >>
  qpat_x_assum `tnf = tp` SUBST_ALL_TAC >>
  suspend "exact_frame"
QED

Resume prepare_load[exact_frame]:
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by fs[compile_abi_dec_addr_def] >>
  `inst_extends sa sb /\ inst_extends sb sc` by metis_tac[inst_extends_emit_op] >>
  `inst_extends sa sc` by metis_tac[inst_extends_trans] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    simp[emitted_insts_append] >>
  `sc.cs_current_bb = sa.cs_current_bb /\ isPREFIX sa.cs_current_insts sc.cs_current_insts /\
   sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sc`] >> simp[mk_inst_def]) >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `((t with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx := LENGTH sc.cs_current_insts) = t` by
    (qpat_assum `t.vs_inst_idx = LENGTH sc.cs_current_insts`
       (fn th => simp_tac (srw_ss()) [GSYM th, venom_state_component_equality])) >>
  `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t)` by
    (qsuff_tac `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0
      (OK ((t with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx := LENGTH sc.cs_current_insts))`
     >- (qpat_assum `_ with vs_inst_idx := _ = t` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     rpt strip_tac >> irule abi_decode_finite_success_observed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sc`,`sa`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  `abi_decode_guarded_effect_core s tn t tp` by simp[abi_decode_guarded_effect_core_def] >>
  mp_tac (abi_decode_owned_scalar_frame_with_history_lower |> SPEC_ALL |> BETA_RULE |>
    Q.INST [`sb` |-> `sc`, `G'` |-> `Gp`, `tn'` |-> `tp`]) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `v = Var (STRING _ _)` kall_tac >>
  qpat_x_assum `addr = Var (STRING _ _)` kall_tac >>
  qpat_x_assum `?ap. addr = Var ap /\ _` (qx_choose_then `ap` strip_assume_tac) >>
  qpat_x_assum `v = Var out` SUBST_ALL_TAC >>
  qexistsl_tac [`out`,`ap`,`t`,`Gp`,`tp`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC, simp[eval_operand_def]]
QED

Finalise prepare_load

Theorem prepare_gas_bind[local]:
  gas_path ctx obs s 0 (OK u) /\ gas_path ctx obs u 0 r ==>
  gas_path ctx obs s 0 r
Proof
  metis_tac[SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)]
QED

Theorem prepare_age[local]:
  sa.cs_next_var <= sb.cs_next_var /\ local_ptrs_reserved ce sa ==>
  local_ptrs_reserved ce sb /\ (!x. not_fresh_at sa x ==> not_fresh_at sb x)
Proof
  metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]
QED

Theorem prepare_head_age[local]:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w ==>
  sa.cs_next_var <= sb.cs_next_var /\ abi_decoder_operand_live sb.cs_next_var head
Proof
  strip_tac >> qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  rpt strip_tac >> irule fresh_var_distinct >> decide_tac
QED

Theorem prepare_old_operand[local]:
  abi_decoder_operand_live sa.cs_next_var opnd /\ t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) ==>
  eval_operand opnd t = eval_operand opnd s /\
  op_prov Gf opnd = op_prov G opnd /\ op_taint tf opnd = op_taint tn opnd
Proof
  Cases_on `opnd` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def,
       eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]
QED

val prepare_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
      w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
      ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

Theorem abi_decode_array_prepare_width_joint_if_suffix_effect_mods:
  ^suffix_all ==> ^prepare_all
Proof
  disch_then (mk_asm "suffix") >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all prepare_trace >>
  disch_then (qx_choose_then `head` (qx_choose_then `head_st`
    (qx_choose_then `addr_st` (qx_choose_then `read_st`
    (qx_choose_then `count_st` (qx_choose_then `first`
    (qx_choose_then `reload_st` strip_assume_tac))))))) >>
  `fn_has_code start head_st fn /\ h < dimword(:256)` by simp[] >>
  `allocas_from lo s` by
    (qpat_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
     (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >> irule owned_decoder_allocas_below_fmp >>
     qexistsl_tac [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!H. V H ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (Q.INST [`sa` |-> `start`, `sb` |-> `head_st`] prepare_head) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `sh` (qx_choose_then `Gh` (qx_choose_then `tnh`
      (map_every assume_tac o CONJUNCTS)))))
  >- suspend "load" >>
  qexistsl_tac [`Abort Revert_abort sh`,`Gh`,`tnh`] >> simp[]
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[load]:
  drule_all prepare_head_age >> strip_tac >>
  drule_all (Q.INST [`sb` |-> `head_st`] prepare_age) >> strip_tac >>
  `sh.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (s,G,tn) [] (OK sh,_,_)`
       (qspec_then `ARB` (mp_then Any ACCEPT_TAC
          gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `eval_operand src sh = SOME (n2w off) /\ op_taint tnh src = {}` by
    (qpat_assum `!x. _ ==> lookup_var x sh = _ /\ _` mp_tac >>
     qpat_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_assum `eval_operand src s = _` mp_tac >>
     qpat_assum `op_taint tn src = _` mp_tac >>
     qpat_assum `sh.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          not_fresh_at_def, eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `not_fresh_at head_st input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at head_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at head_st x)` by simp[] >>
  `off + 32 <= LENGTH input_bytes /\ fn_has_code head_st read_st fn` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sh` by
    (strip_tac >> irule owned_decoder_allocas_below_fmp >>
     qexistsl_tac [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ sh /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (Q.INST [`sa` |-> `head_st`, `sb` |-> `addr_st`, `sc` |-> `read_st`,
                  `pos` |-> `src`, `v` |-> `first`, `p` |-> `off`,
                  `s` |-> `sh`, `G` |-> `Gh`, `tn` |-> `tnh`] prepare_load) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `first_var` (qx_choose_then `ar`
    (qx_choose_then `sl` (qx_choose_then `Gl` (qx_choose_then `tnl`
      (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "count"
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[count]:
  `head_st.cs_next_var <= read_st.cs_next_var` by
    (qpat_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_assum `emit_op MLOAD [_] addr_st = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_abi_dec_addr_def, emit_op_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def] >> rpt strip_tac >> gvs[]) >>
  drule_all (Q.INST [`sa` |-> `head_st`, `sb` |-> `read_st`] prepare_age) >> strip_tac >>
  `not_fresh_at read_st input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at read_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at read_st x)` by simp[] >>
  `abi_decoder_operand_live read_st.cs_next_var first` by
    (qpat_assum `first = Var first_var` SUBST1_TAC >>
     qpat_assum `not_fresh_at read_st first_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  qabbrev_tac `c = w2n (mload (w2n input_word + off) sh)` >>
  `eval_operand first sl = SOME (n2w c) /\ c < dimword (:256)` by
    simp[Abbr `c`, w2n_lt] >>
  `fn_has_code read_st count_st fn /\ maxn MOD dimword (:256) < dimword (:256)` by
    simp[arithmeticTheory.MOD_LESS] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sl` by
    (strip_tac >> irule owned_decoder_allocas_below_fmp >>
     qexistsl_tac [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ sl /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK sl,Gl,tnl)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`sh`,`tnh`] >> simp[]) >>
  `!obs. fn_has_code start header_st obs ==> gas_path ctx obs s 0 (OK sl)` by
    (rpt strip_tac >> irule prepare_gas_bind >> qexists_tac `sh` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `read_st`, `sb` |-> `count_st`, `cnt` |-> `first`,
                  `s` |-> `sl`, `G` |-> `Gl`, `tn` |-> `tnl`,
                  `n` |-> `maxn MOD dimword (:256)`] prepare_count) >>
  (impl_tac >- (rewrite_tac[n2w_mod] >> asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
      (map_every assume_tac o CONJUNCTS)))))
  >- suspend "prepared" >>
  qexistsl_tac [`Abort Revert_abort u`,`Gu`,`tnu`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gl`,`sl`,`tnl`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule prepare_gas_bind >> qexists_tac `sl` >> simp[]) >>
  simp[]
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[prepared]:
  `read_st.cs_next_var <= count_st.cs_next_var` by
    (qpat_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  drule_all (Q.INST [`sa` |-> `read_st`, `sb` |-> `count_st`] prepare_age) >> strip_tac >>
  `!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `!x. not_fresh_at head_st x ==> lookup_var x u = lookup_var x sh /\
    FLOOKUP Gu x = FLOOKUP Gh x /\ op_taint tnu (Var x) = op_taint tnh (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gl`,`sl`,`tnl`] >> simp[]) >>
  `!obs. fn_has_code start header_st obs ==> gas_path ctx obs s 0 (OK u)` by
    (rpt strip_tac >> irule prepare_gas_bind >> qexists_tac `sl` >> simp[]) >>
  `abi_decode_guarded_effect_core s tn sl tnl` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl_tac [`tnh`,`sh`] >> simp[]) >>
  `abi_decode_guarded_effect_core s tn u tnu` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl_tac [`tnl`,`sl`] >> simp[]) >>
  `tnu.t_mem = tn.t_mem` by simp[] >>
  Q_TAC (fn tm => SUBGOAL_THEN (beta tm) ASSUME_TAC) `(^prepare_origin) u` >-
    (irule abi_decode_input_origin_transport >> qexistsl_tac [`s`,`start`] >>
     asm_rewrite_tac[] >> conj_tac >- simp[] >>
     qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (s,G,tn) [] (OK u,_,_)`
       (qspec_then `ARB` (mp_then Any mp_tac gas_origin_ptr_path_projections)) >>
     strip_tac >> drule gas_path_ptr_old_allocations >> simp[]) >>
  `u.vs_labels = sl.vs_labels /\ u.vs_labels = s.vs_labels` by
    (conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (sl,Gl,tnl) [] (OK u,_,_)`
           (qspec_then `ARB` (mp_then Any ACCEPT_TAC gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
     qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (s,G,tn) [] (OK u,_,_)`
       (qspec_then `ARB` (mp_then Any ACCEPT_TAC gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `u.vs_labels = sh.vs_labels` by simp[] >>
  mp_tac (Q.INST [`sa` |-> `head_st`, `opnd` |-> `head`, `t` |-> `u`, `s` |-> `sh`,
    `Gf` |-> `Gu`, `G` |-> `Gh`, `tf` |-> `tnu`, `tn` |-> `tnh`] prepare_old_operand) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `read_st`, `opnd` |-> `first`, `t` |-> `u`, `s` |-> `sl`,
    `Gf` |-> `Gu`, `G` |-> `Gl`, `tf` |-> `tnu`, `tn` |-> `tnl`] prepare_old_operand) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `start`, `opnd` |-> `hi`, `t` |-> `u`,
    `Gf` |-> `Gu`, `tf` |-> `tnu`] prepare_old_operand) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `c <= maxn` by
    (irule LESS_EQ_TRANS >> qexists_tac `maxn MOD dimword(:256)` >> simp[MOD_LESS_EQ]) >>
  `start.cs_next_var <= count_st.cs_next_var /\ head_st.cs_next_var <= count_st.cs_next_var /\
   off+32 < dimword(:256) /\ fn_has_code count_st header_st fn` by simp[] >>
  `abi_decoder_operand_live count_st.cs_next_var head /\
   abi_decoder_operand_live count_st.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono
     >- (qexists_tac `head_st.cs_next_var` >> simp[]) >>
     qexists_tac `start.cs_next_var` >> simp[]) >>
  `not_fresh_at count_st input /\ not_fresh_at count_st dst /\ not_fresh_at count_st ar /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x)` by simp[] >>
  suspend "suffix_input"
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[suffix_input]:
  `w2n (input_word + n2w off) = w2n input_word + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
  `abi_decode_ptr_window Gu tnu u ar (input_word + n2w off) (LENGTH input_bytes-off)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gl`,`sl`,`tnl`] >> simp[]) >>
  `abi_decode_ptr_window Gu tnu u ar (input_word + n2w off) 32` by
    (qpat_assum `abi_decode_ptr_window Gu tnu u ar _ (LENGTH input_bytes-off)` mp_tac >>
     rewrite_tac[abi_decode_ptr_window_def] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
                  qexists_tac `LENGTH input_bytes-off` >> simp[]) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!j. w2n (input_word + n2w off) <= j /\ j < _ ==> j NOTIN tnu.t_mem`
       (qspec_then `i` irule) >> simp[]) >>
  `w2n (input_word + n2w off) + 32 <= u.vs_alloca_next` by simp[] >>
  `mem_word_at (w2n (input_word + n2w off)) u.vs_memory = n2w c` by
    simp[Abbr `c`, mem_word_at_eq_mload, mload_def] >>
  `32 <= type_memory_size (ArrayTV tv (Dynamic maxn))` by simp[valueEncodingTheory.type_memory_size_def] >>
  `d < dimword (:256) /\ d+32 <= output_base+output_cap` by simp[] >>
  `alloca_inv u` by
    (qpat_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_then Any ACCEPT_TAC
       (cj 2 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) o CONJUNCT1)) >>
  `d+32 <= u.vs_alloca_next` by
    (qpat_assum `FLOOKUP u.vs_allocas output_id = SOME (output_base,output_cap)`
       (mp_then Any irule abiCallerAllocationTheory.abi_caller_allocation_end) >> simp[]) >>
  `ptr_covers Gu tnu dst u (type_memory_size (ArrayTV tv (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `ptr_covers Gu tnu dst u 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size (ArrayTV tv (Dynamic maxn))` >> simp[]) >>
  `EVERY (\(aid,q,b,k,bytes). b+k <= d \/ d+32 <= b) live` by
    (irule EVERY_MONOTONIC >>
     qexists_tac `\(aid,q,b,k,bytes). b+k <= d \/
       d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b` >>
     simp[] >> qx_gen_tac `row` >> PairCases_on `row` >> simp[] >> decide_tac) >>
  `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+32 <= b) protected` by
    (irule EVERY_MONOTONIC >>
     qexists_tac `\(b,bytes). b+LENGTH bytes <= d \/
       d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b` >>
     simp[pairTheory.FORALL_PROD] >> decide_tac) >>
  qpat_assum `emit_op MLOAD [addr] guard_st = (cnt,reload_st)`
    (mp_then Any (qx_choose_then `reload_var` (strip_assume_tac o CONJUNCT1))
       loweringShapeRulesTheory.emit_op_facts) >>
  qpat_x_assum `cnt = Var reload_var` SUBST_ALL_TAC >>
  qpat_x_assum `addr = Var ar` SUBST_ALL_TAC >>
  suspend "suffix_call"
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[suffix_call]:
  `c * stride < dimword (:256)` by simp[] >>
  asm_x "suffix" (mp_tac o Q.INST [`addr` |-> `ar`, `cnt` |-> `reload_var`,
     `p` |-> `off+32`, `a` |-> `input_word + n2w off`, `dw` |-> `n2w d`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[w2n_n2w])) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gp` (qx_choose_then `tnp`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`,`Gp`,`tnp`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule prepare_gas_bind >> qexists_tac `u` >> simp[]) >>
  qpat_x_assum `(?t. r = Abort Revert_abort t) \/ (?t. _)`
    (DISJ_CASES_THEN (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> qexists_tac `t` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`t`,`c`,`reload_var`] >>
  suspend "finish"
QED

Resume abi_decode_array_prepare_width_joint_if_suffix_effect_mods[finish]:
  `abi_decode_guarded_effect_core s tn t tnp` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl_tac [`tnu`,`u`] >> simp[]) >>
  `!mem. mem_bytes_at (w2n input_word) (LENGTH input_bytes) mem = input_bytes ==>
     mem_bytes_at (w2n input_word + off) 32 mem = TAKE 32 (DROP off input_bytes)` by
    (gen_tac >> disch_tac >>
     qspecl_then [`w2n input_word`,`off`,`32`,`LENGTH input_bytes`,`mem`] mp_tac
       abiCanonicalHeadSizeTheory.mem_bytes_at_window >> simp[]) >>
  `mem_bytes_at (w2n input_word + off) 32 t.vs_memory =
   mem_bytes_at (w2n input_word + off) 32 u.vs_memory` by simp[] >>
  `mem_word_at (w2n input_word + off) t.vs_memory = n2w c` by
    (irule EQ_TRANS >> qexists_tac `mem_word_at (w2n input_word + off) u.vs_memory` >>
     conj_tac
     >- (qpat_assum `mem_bytes_at _ 32 t.vs_memory = mem_bytes_at _ 32 u.vs_memory`
           (fn th => rewrite_tac [abiStaticAggregatePropsTheory.mem_word_at_bytes, th])) >>
     qpat_assum `w2n (input_word + n2w off) = _` (fn addr_eq =>
       qpat_assum `mem_word_at (w2n (input_word + n2w off)) u.vs_memory = _`
         (ACCEPT_TAC o REWRITE_RULE [addr_eq]))) >>
  `count_st.cs_next_var <= guard_st.cs_next_var` by
    (qpat_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
          comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `start.cs_next_var <= header_st.cs_next_var` by
    (qpat_assum `emit_op MLOAD [Var ar] guard_st = _`
       (mp_then Any (assume_tac o cj 4) emitted_insts_emit_op) >>
     qpat_assum `emit_void MSTORE _ reload_st = _`
       (mp_then Any (assume_tac o cj 3) emitted_insts_emit_void) >> simp[]) >>
  drule_all (Q.INST [`sa` |-> `start`, `sb` |-> `header_st`] prepare_age) >> strip_tac >>
  `abi_decoder_operand_live header_st.cs_next_var src /\
   abi_decoder_operand_live header_st.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  `!x. not_fresh_at start x ==> not_fresh_at count_st x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (u,Gu,tnu) [] (r,_,_)`
       (qspec_then `ARB` mp_tac) >>
     qpat_assum `r = OK t` (rewrite_tac o single) >>
     disch_then (mp_then Any assume_tac gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels) >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `start`, `opnd` |-> `src`, `Gf` |-> `Gp`, `tf` |-> `tnp`] prepare_old_operand) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `start`, `opnd` |-> `hi`, `Gf` |-> `Gp`, `tf` |-> `tnp`] prepare_old_operand) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `ptr_covers Gp tnp dst t (type_memory_size (ArrayTV tv (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `w2n (n2w d : 256 word) = d` by simp[w2n_n2w] >>
  qpat_assum `mem_word_at (w2n (n2w d : 256 word)) t.vs_memory = _`
    (fn th => qpat_assum `w2n (n2w d : 256 word) = d`
      (fn addr_eq => assume_tac (REWRITE_RULE [addr_eq] th))) >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnp.t_mem ==>
       i IN tn.t_mem` by
    (qpat_assum `!i. _ /\ _ /\ i IN tnp.t_mem ==> i IN tnu.t_mem`
      (fn th => qpat_assum `tnu.t_mem = tn.t_mem`
        (fn mem_eq => ACCEPT_TAC (REWRITE_RULE [mem_eq] th)))) >>
  asm_rewrite_tac[] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_decode_array_prepare_width_joint_if_suffix_effect_mods
