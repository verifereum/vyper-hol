Theory abiEncodeValuesRun
Ancestors
  abiEncodeValuesCode abiEncodeValuesMetadata abiEncodeValuesCursorInit abiEncodeValuesFinish
  abiEncodeValuesAdvance abiEncodeValuesDynamic abiEncodeValuesLayout abiEncodeValuesPhases
  allocaSiteResource freshWrites
  abiEncoderTuple abiEncoderOpenInput abiCanonicalWindows abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderRegisteredEffect exprSimAbiEncodeExecFrame bodyFullAbiEncodeOriginFloor
  fragGasOriginPtr fragGasOriginPtrLoop fragExec exprLoweringProps
  compileEnv exprLowering emitHelperProps ptrDiscipline valueEncodingDefs
  bodyPtrDefs loweringPosts loweringStateRelDefs assignTuplePtrCopyLen
  contractABI venomState venomMemDefs venomInst finite_map pred_set list rich_list arithmetic pair

Definition abi_encode_values_prefix_at_def:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn <=>
    (?p. cursor = Var p /\ not_fresh_at st p /\
      eval_operand cursor s = SOME (n2w slot) /\ ptr_covers G tn p s 32) /\
    FLOOKUP s.vs_allocas loc = SOME (slot,32) /\ loc < st.cs_next_id /\
    slot + 32 <= s.vs_alloca_next /\
    abi_encoder_tuple_prefix hl (TAKE i ats) (TAKE i avs) d s.vs_memory /\
    mem_word_at slot s.vs_memory =
      n2w (hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))) /\
    (!j. slot <= j /\ j < slot+32 ==> j NOTIN tn.t_mem) /\
    (!j. d <= j /\ j < d + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) ==>
      j NOTIN tn.t_mem) /\
    (!j. d+hl <= j /\ j < d+hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) ==>
      j NOTIN tn.t_mem)
End

Definition abi_encode_values_path_def[local]:
  abi_encode_values_path lo explicit ctx func PG (u,Gu,tu) (v,Gv,tv) <=>
    (u = v /\ Gu = Gv /\ tu = tv) \/
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)
End

(* The extra endpoint relation is folded over the very same steps as the
   ghost path. The cursor laws consume the actual straight-line sequence,
   not just the resulting PC or the absence of GAS marks. *)
Definition abi_encode_values_path_laws_def:
  abi_encode_values_path_laws R func st en s hl out <=>
    (!a u. R a a u u) /\
    (!a b c u v z. ci_mono a b /\ ci_mono b c /\ R a b u v /\ R b c v z ==> R a c u z) /\
    (!p a b v. emit_op ALLOCA [Lit 32w] st = (p,a) /\
      emit_void MSTORE [p; Lit (n2w hl)] a = ((),b) /\ fn_has_code st b func /\
      ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts /\
      run_inst_seq (emitted_insts st b) s = OK (v with vs_inst_idx := s.vs_inst_idx) /\
      v.vs_inst_idx = LENGTH b.cs_current_insts ==> R st b s v) /\
    (!p a u v. emit_op MLOAD [p] a = (out,en) /\ fn_has_code a en func /\
      ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
      u.vs_inst_idx = LENGTH a.cs_current_insts /\
      run_inst_seq (emitted_insts a en) u = OK (v with vs_inst_idx := u.vs_inst_idx) /\
      v.vs_inst_idx = LENGTH en.cs_current_insts ==> R a en u v)
End

(* The caller proves its frame through pure phases and supplies the
   materialization rule for a singleton at the original argument index. *)
Theorem abi_encode_values_execute_with_path:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
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
  (!i a c u Gu tu cursor slot.
    i < LENGTH rows /\ P a u Gu tu /\
    abi_encode_values_prefix_at ats avs hl d cursor st.cs_next_id slot i a u Gu tu /\
    compile_abi_encode_value_rows ce dst cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?v Gv tv. P c v Gv tv /\
      abi_encode_values_prefix_at ats avs hl d cursor st.cs_next_id slot (SUC i) c v Gv tv /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
      R a c u v) /\
  abi_encode_values_path_laws R func st en s hl out ==>
  ?t G' tn'.
    P en t G' tn' /\ eval_operand out t = SOME (n2w (LENGTH bytes)) /\ op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at d (LENGTH bytes) t.vs_memory = bytes /\
    (!j. d <= j /\ j < d + LENGTH bytes ==> j NOTIN tn'.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    R st en s t
Proof
  simp_tac bool_ss [abi_encode_values_path_laws_def, GSYM CONJ_ASSOC] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `abi_static_size ce.ce_struct_fields (TupleT (MAP SND rows)) = hl` by
    metis_tac[abi_encode_value_rows_head_total] >>
  mp_tac (Q.INST
        [`x` |-> `(s,G,tn)`,
         `row_inv` |-> `\cursor i a (u,Gu,tu).
           ci_mono st a /\ P a u Gu tu /\ ?slot.
             abi_encode_values_prefix_at ats avs hl d cursor st.cs_next_id slot i a u Gu tu`,
         `row_step` |-> `\a c (u,Gu,tu) (v,Gv,tv).
           ci_mono a c /\ abi_encode_values_path lo explicit ctx func PG (u,Gu,tu) (v,Gv,tv) /\ R a c u v`,
         `Q` |-> `\out (u,Gu,tu). P en u Gu tu /\
           eval_operand out u = SOME (n2w (LENGTH bytes)) /\ op_taint tu out = {} /\
           (!x. out = Var x ==> not_fresh_at en x) /\ mem_bytes_at d (LENGTH bytes) u.vs_memory = bytes /\
           (!j. d <= j /\ j < d + LENGTH bytes ==> j NOTIN tu.t_mem)`]
        (INST_TYPE [alpha |-> ``:venom_state # (string |-> num # num) # taint``]
          abi_encode_values_to_buf_indexed)) >>
  qpat_assum `compile_abi_encode_values_to_buf ce dst rows st = (out,en)`
    (fn th => simp_tac (srw_ss()) [th, FORALL_PROD, EXISTS_PROD]) >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `ci_mono st a /\ ci_mono a b'` by
            metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
          `ci_mono b' last /\ ci_mono last en` by
            metis_tac[ci_mono_compile_abi_encode_value_rows, ci_mono_emit_op, pairTheory.SND] >>
          `fn_has_code st b' func` by metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
          qpat_assum `!a u Gu tu. P a u Gu tu ==> _` (drule_then strip_assume_tac) >>
          mp_tac (Q.INST [`mid` |-> `a`, `en` |-> `b'`, `dst_site` |-> `owner`,
            `dst_base` |-> `b`, `capacity` |-> `cap`] abi_encode_values_cursor_init_run) >>
          impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- (qpat_assum `abi_static_size _ _ = hl` (fn th =>
                  qpat_assum `emit_void MSTORE _ a = _` (ACCEPT_TAC o REWRITE_RULE [th])))
            >> asm_rewrite_tac[]) >>
          disch_then (qx_choosel_then [`v`,`slot`,`p`,`Gv`,`tv`] strip_assume_tac) >>
          `P b' v Gv tv` by
            (qpat_assum `!a c ids u Gu tu v Gv tv. P a u Gu tu /\ _ ==> P c v Gv tv`
               (qspecl_then [`st`,`b'`,`{st.cs_next_id}`,`s`,`G`,`tn`,`v`,`Gv`,`tv`]
                 MATCH_MP_TAC) >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
             >- metis_tac[ci_mono_trans] >>
             simp[SUBSET_DEF, IN_DIFF]) >>
          `ci_mono st b'` by metis_tac[ci_mono_trans] >>
          `R st b' s v` by
            (qpat_assum `!p a b v. emit_op ALLOCA _ _ = _ /\ _ ==> _`
               (qspecl_then [`cursor`,`a`,`b'`,`v`] mp_tac) >>
             impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                           metis_tac[window_phase_control]) >> simp[]) >>
          qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[abi_encode_values_path_def] >>
          qexists_tac `slot` >> simp[abi_encode_values_prefix_at_def,
            abi_tuple_heads_def, abi_tuple_tails_def] >> metis_tac[])
      >- (rpt gen_tac >> strip_tac >>
          rename1 `P a u Gu tu` >>
          `ci_mono a b'` by metis_tac[ci_mono_compile_abi_encode_value_rows, pairTheory.SND] >>
          `ci_mono b' last /\ ci_mono last en` by
            metis_tac[ci_mono_compile_abi_encode_value_rows, ci_mono_emit_op, pairTheory.SND] >>
          `fn_has_code a b' func` by metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
          qpat_assum `!i a c u Gu tu cursor slot. _`
            (qspecl_then [`i`,`a`,`b'`,`u`,`Gu`,`tu`,`cursor`,`slot`] mp_tac) >>
          impl_tac >- asm_rewrite_tac[] >>
          disch_then (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac) >>
          `ci_mono st b'` by metis_tac[ci_mono_trans] >>
          qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[abi_encode_values_path_def] >>
          qexists_tac `slot` >>
          qpat_assum `hl = head_lengths ats 0` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
          first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> strip_tac >>
          rename1 `P a u Gu tu` >>
          `ci_mono a en` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
          `fn_has_code a en func` by metis_tac[ci_mono_def, fn_has_code_split] >>
          qpat_assum `!a u Gu tu. P a u Gu tu ==> _` (drule_then strip_assume_tac) >>
          `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
            (strip_tac >> res_tac) >>
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
            abi_encode_values_finish_run) >>
          impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            TRY REFL_TAC >> TRY (asm_rewrite_tac[]) >>
            POP_ASSUM_LIST (K ALL_TAC) >> NO_TAC) >>
          disch_then (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac) >>
          `P en v Gv tv` by
            (qpat_assum `!a c ids u Gu tu v Gv tv. P a u Gu tu /\ _ ==> P c v Gv tv`
               (qspecl_then [`a`,`en`,`{}`,`u`,`Gu`,`tu`,`v`,`Gv`,`tv`] MATCH_MP_TAC) >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             simp[SUBSET_DEF]) >>
          `R a en u v` by
            (qpat_assum `!p a u v. emit_op MLOAD _ _ = _ /\ _ ==> _`
               (qspecl_then [`Var p`,`a`,`u`,`v`] mp_tac) >>
             impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                           metis_tac[window_phase_control]) >> simp[]) >>
          qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[abi_encode_values_path_def])
      >- simp[ci_mono_refl, abi_encode_values_path_def] >>
      rpt gen_tac >> strip_tac >>
      conj_tac >- metis_tac[ci_mono_trans] >>
      reverse conj_tac >- metis_tac[] >>
      fs[abi_encode_values_path_def] >> metis_tac[gas_origin_ptr_path_trans]) >>
  `~s.vs_halted` by (qpat_assum `!a u Gu tu. P a u Gu tu ==> _`
    (drule_then (ACCEPT_TAC o cj 5))) >>
  simp_tac bool_ss [abi_encode_values_path_def] >>
  qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
  simp_tac bool_ss [enc_def] >>
  disch_then (qx_choosel_then [`v`,`Gv`,`tv`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`Gv`,`tv`] >> asm_rewrite_tac[] >>
  metis_tac[cj 1 gas_origin_ptr_path_rules]
QED

Theorem abi_encode_values_execute =
  (PURE_REWRITE_RULE [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP] o BETA_RULE o
   PURE_REWRITE_RULE [abi_encode_values_path_laws_def])
    (Q.INST [`R` |-> `\(a:compile_state) (b:compile_state) (u:venom_state) (v:venom_state). T`]
      abi_encode_values_execute_with_path)
