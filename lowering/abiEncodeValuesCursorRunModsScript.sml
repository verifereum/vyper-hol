Theory abiEncodeValuesCursorRunMods
Ancestors
  abiEncodeValuesRun abiEncodeValuesCode abiEncodeValuesMetadata
  abiEncodeValuesCursorInit abiEncodeValuesFinish abiEncoderTuple
  abiEncoderOpenInput abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderRegisteredEffect allocaSiteResource fragGasOriginPtr
  fragGasOriginPtrLoop fragExec abiCanonicalWindows exprLoweringProps
  emitHelperProps ptrDiscipline
  compileEnv exprLowering valueEncodingDefs loweringPosts contractABI
  venomState venomMemDefs venomInst finite_map pred_set list rich_list arithmetic pair

Theorem abi_encode_values_execute_with_cursor:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
  emit_op ALLOCA [Lit 32w] st = (cursor0,allocated) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  FLOOKUP s.vs_allocas owner = SOME (b,cap) /\ owner < st.cs_next_id /\
  P st s G tn /\
  (!a u Gu tu. P a u Gu tu ==>
    alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)) /\
  (!p n. FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,n) ==> n = 32) /\
  (!a c ids u Gu tu v Gv tv.
    P a u Gu tu /\ ci_mono a c /\ window_phase ctx func a c ids [] u v /\
    abi_encode_exec_frame func u v /\ ids SUBSET {st.cs_next_id} /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
    tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
    tv.t_mem SUBSET tu.t_mem ==>
    P c v Gv tv) /\
  (!i a c u Gu tu slot.
    i < LENGTH rows /\ P a u Gu tu /\
    abi_encode_values_prefix_at ats avs hl d cursor0 st.cs_next_id slot i a u Gu tu /\
    compile_abi_encode_value_rows ce dst cursor0
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?v Gv tv. P c v Gv tv /\
      abi_encode_values_prefix_at ats avs hl d cursor0 st.cs_next_id slot (SUC i) c v Gv tv /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv))) ==>
  ?t G' tn'.
    P en t G' tn' /\ eval_operand out t = SOME (n2w (LENGTH bytes)) /\ op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at d (LENGTH bytes) t.vs_memory = bytes /\
    (!j. d <= j /\ j < d + LENGTH bytes ==> j NOTIN tn'.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `abi_static_size ce.ce_struct_fields (TupleT (MAP SND rows)) = hl` by
    metis_tac[abi_encode_value_rows_head_total] >>
  mp_tac (Q.INST
        [`x` |-> `(s,G,tn)`,
         `row_inv` |-> `\cursor i a (u,Gu,tu).
           cursor = cursor0 /\ ci_mono st a /\ P a u Gu tu /\ ?slot.
             abi_encode_values_prefix_at ats avs hl d cursor st.cs_next_id slot i a u Gu tu`,
         `row_step` |-> `\a c (u,Gu,tu) (v,Gv,tv).
           ci_mono a c /\ ((u = v /\ Gu = Gv /\ tu = tv) \/
             !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv))`,
         `Q` |-> `\out (u,Gu,tu). P en u Gu tu /\
           eval_operand out u = SOME (n2w (LENGTH bytes)) /\ op_taint tu out = {} /\
           (!x. out = Var x ==> not_fresh_at en x) /\ mem_bytes_at d (LENGTH bytes) u.vs_memory = bytes /\
           (!j. d <= j /\ j < d + LENGTH bytes ==> j NOTIN tu.t_mem)`]
        (INST_TYPE [alpha |-> ``:venom_state # (string |-> num # num) # taint``]
          abi_encode_values_to_buf_indexed)) >>
  qpat_assum `compile_abi_encode_values_to_buf ce dst rows st = (out,en)`
    (fn th => simp_tac bool_ss [th, FORALL_PROD, EXISTS_PROD]) >>
  CONV_TAC (DEPTH_CONV (BETA_CONV ORELSEC pairLib.PAIRED_BETA_CONV)) >>
  impl_tac
  >- (rpt conj_tac
      >- suspend "init"
      >- suspend "row"
      >- suspend "finish"
      >- simp[ci_mono_refl] >>
      rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[ci_mono_trans]) >>
      rpt BasicProvers.VAR_EQ_TAC >> asm_rewrite_tac[] >>
      disj2_tac >> gen_tac >>
      irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `~s.vs_halted` by (qpat_assum `!a u Gu tu. P a u Gu tu ==> _`
    (drule_then (ACCEPT_TAC o cj 5))) >>
  metis_tac[cj 1 gas_origin_ptr_path_rules]
QED

Resume abi_encode_values_execute_with_cursor[init]:
  rpt gen_tac >> strip_tac >>
  `cursor = cursor0 /\ a = allocated` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `a = allocated` SUBST_ALL_TAC >>
  qpat_x_assum `cursor = cursor0` SUBST_ALL_TAC >>
  `ci_mono st allocated /\ ci_mono allocated b'` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono b' last /\ ci_mono last en` by
    metis_tac[ci_mono_compile_abi_encode_value_rows, ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono st b'` by metis_tac[ci_mono_trans] >>
  `fn_has_code st b' func` by metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  qpat_assum `!a u Gu tu. P a u Gu tu ==> _` (drule_then strip_assume_tac) >>
  `emit_void MSTORE [cursor0; Lit (n2w hl)] allocated = ((),b')` by
    (qpat_assum `abi_static_size _ _ = hl` (fn th =>
       qpat_assum `emit_void MSTORE _ allocated = _` (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  mp_tac (Q.INST [`cursor` |-> `cursor0`, `mid` |-> `allocated`,
    `en` |-> `b'`, `dst_site` |-> `owner`,
    `dst_base` |-> `b`, `capacity` |-> `cap`] abi_encode_values_cursor_init) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`v`,`slot`,`p`,`Gv`,`tv`] strip_assume_tac) >>
  `P b' v Gv tv` by
    (qpat_assum `!a c ids u Gu tu v Gv tv. P a u Gu tu /\ _ ==> P c v Gv tv`
       (qspecl_then [`st`,`b'`,`{st.cs_next_id}`,`s`,`G`,`tn`,`v`,`Gv`,`tv`] MATCH_MP_TAC) >>
     asm_rewrite_tac[SUBSET_REFL, DIFF_SUBSET]) >>
  qexistsl_tac [`v`,`Gv`,`tv`] >>
  asm_rewrite_tac[] >> qexists_tac `slot` >>
  simp[abi_encode_values_prefix_at_def, abi_tuple_heads_def, abi_tuple_tails_def] >>
  qpat_assum `cursor0 = Var p` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
  first_assum ACCEPT_TAC
QED

Resume abi_encode_values_execute_with_cursor[row]:
  rpt gen_tac >> strip_tac >>
  rename1 `P a u Gu tu` >>
  qpat_x_assum `cursor = cursor0` SUBST_ALL_TAC >>
  `ci_mono a b'` by metis_tac[ci_mono_compile_abi_encode_value_rows, pairTheory.SND] >>
  `ci_mono b' last /\ ci_mono last en` by
    metis_tac[ci_mono_compile_abi_encode_value_rows, ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code a b' func` by metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  qpat_assum `!i a c u Gu tu slot. _`
    (qspecl_then [`i`,`a`,`b'`,`u`,`Gu`,`tu`,`slot`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac) >>
  `ci_mono st b'` by metis_tac[ci_mono_trans] >>
  qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[] >>
  qexists_tac `slot` >>
  qpat_assum `hl = head_lengths ats 0` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Resume abi_encode_values_execute_with_cursor[finish]:
  rpt gen_tac >> strip_tac >>
  rename1 `P a u Gu tu` >>
  `ci_mono a en` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code a en func` by metis_tac[ci_mono_def, fn_has_code_split] >>
  qpat_assum `!a u Gu tu. P a u Gu tu ==> _` (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_x_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_values_prefix_at_def]) >>
  `TAKE (LENGTH rows) ats = ats /\ TAKE (LENGTH rows) avs = avs` by
    simp[TAKE_LENGTH_ID_rwt] >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  qpat_x_assum `TAKE (LENGTH rows) ats = ats`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `TAKE (LENGTH rows) avs = avs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LENGTH (FLAT (abi_tuple_heads hl 0 ats avs)) = hl` by
    simp[abi_encoder_open_heads_length, abiDecodeRangesTheory.head_lengths_acc] >>
  qpat_x_assum `LENGTH (FLAT (abi_tuple_heads hl 0 ats avs)) = hl`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`s` |-> `u`, `st` |-> `a`, `G` |-> `Gu`, `tn` |-> `tu`,
    `cursor` |-> `p`,
    `tys` |-> `ats`, `vs` |-> `avs`, `tl` |-> `LENGTH (FLAT (abi_tuple_tails ats avs))`]
    abi_encode_values_finish) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac) >>
  `P en v Gv tv` by
    (qpat_assum `!a c ids u Gu tu v Gv tv. P a u Gu tu /\ _ ==> P c v Gv tv`
       (qspecl_then [`a`,`en`,`{}`,`u`,`Gu`,`tu`,`v`,`Gv`,`tv`] MATCH_MP_TAC) >>
     asm_rewrite_tac[EMPTY_SUBSET, SUBSET_REFL]) >>
  qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[]
QED

Finalise abi_encode_values_execute_with_cursor
