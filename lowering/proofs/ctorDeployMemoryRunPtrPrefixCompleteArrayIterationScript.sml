(* Same-witness shifted array backedge and child composition. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArrayIteration
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixCompleteCode ctorDeployMemoryRunPtrPrefixLoopIteration
  ctorDeployLoweringEntryArrayRun ctorDeployLoweringEntryArrayFrame
  ctorDeployLoweringEntryCompleteArrayBody
  ctorDeployMemoryRunPtrPrefixLoopBackedge abiDecoderArrayBackedge
  abiDecoderContract abiDecoderReentry abiDecoderExecution abiDecoderLoop compileEnv
  valueEncoding valueEncodingProps venomMemDefs spillSim
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  words arithmetic list finite_map pred_set

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem prefix_complete_backedge_support_pair:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString nv)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  eval_operand ip s = SOME (n2w slot) /\ abi_decoder_operand_live next ip /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  ip = Var slot_var /\ FLOOKUP G slot_var = SOME (slot,32) /\
  op_taint tn ip = {} /\ op_taint tn (Var iv) = {} /\ lo <= slot /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  FLOOKUP G dst = SOME (b,sz) /\ op_taint tn (Var dst) = {} /\
  abi_decoder_operand_live next (Var dst) /\
  FINITE B /\ B SUBSET {a | d <= a /\ a < d + 32 + SUC j * type_memory_size tv} /\
  DISJOINT B tn.t_mem ==>
  ?t H qt.
    (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst = SOME (b,sz) /\
    op_taint qt ip = {} /\ op_taint qt (Var dst) = {} /\
    qt.t_mem SUBSET tn.t_mem /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
    FINITE B /\ DISJOINT B qt.t_mem /\
    (!a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. abi_decoder_older_vars next x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x s) /\
    (!a. a < lo ==> read_byte a t.vs_memory = read_byte a s.vs_memory) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  qabbrev_tac `fresh = STRING #"%" (toString nv)` >>
  `ip <> Var fresh /\ Var dst <> Var fresh` by
    metis_tac[abi_decoder_live_excludes_output] >>
  drule_all deploy_ctor_array_observation_backedge >>
  disch_then (qspec_then `hdr` (strip_assume_tac o BETA_RULE)) >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  qpat_x_assum `ip = Var slot_var` SUBST_ALL_TAC >>
  `slot_var <> fresh` by metis_tac[] >>
  qpat_assum `eval_operand (Var iv) s = SOME (n2w j)`
    (mp_then (Pos (el 3)) mp_tac prefix_loop_increment_steps) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`id`,`func`,`PG`,`Ddead`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ _ = OK raw` >>
  qmatch_asmsub_abbrev_tac `ghost_step _ _ _ _ _ _ _ = (H,q)` >>
  qmatch_asmsub_abbrev_tac `op_taint qt (Var fresh) = {}` >>
  qexistsl [`jump_to hdr raw`,`H`,`qt`] >>
  `!x. abi_decoder_older_vars next x ==> x <> fresh` by
    (simp[Abbr `fresh`,abi_decoder_older_vars_def] >> metis_tac[]) >>
  `~(jump_to hdr raw).vs_halted /\ (jump_to hdr raw).vs_current_bb = hdr /\
   (jump_to hdr raw).vs_inst_idx = 0 /\ allocas_from lo (jump_to hdr raw) /\
   lo <= (jump_to hdr raw).vs_alloca_next` by
    (simp[Abbr `raw`,jump_to_def,mstore_def,update_var_def,
       write_memory_with_expansion_def,allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  simp[] >> suspend "remaining"
QED

Resume prefix_complete_backedge_support_pair[remaining]:
  `!x. abi_decoder_older_vars next x ==>
     lookup_var x (jump_to hdr raw) = lookup_var x s` by
    (rpt strip_tac >>
     simp[Abbr `raw`,jump_to_def,mstore_def,update_var_def,
       write_memory_with_expansion_def,lookup_var_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!a. a < lo ==> read_byte a (jump_to hdr raw).vs_memory = read_byte a s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `raw`,jump_to_def] >>
     irule EQ_TRANS >> irule_at Any spillSimTheory.read_byte_mstore_outside >>
     simp[update_var_def] >> decide_tac) >>
  `(jump_to hdr raw).vs_code = s.vs_code /\
   (jump_to hdr raw).vs_gas_readings = s.vs_gas_readings /\
   (jump_to hdr raw).vs_outcomes = s.vs_outcomes /\
   (jump_to hdr raw).vs_tx_ctx = s.vs_tx_ctx /\
   (jump_to hdr raw).vs_block_ctx = s.vs_block_ctx` by
    simp[Abbr `raw`,jump_to_def,mstore_def,update_var_def,
      write_memory_with_expansion_def] >>
  simp[] >> suspend "support"
QED

Resume prefix_complete_backedge_support_pair[support]:
  `!a. a IN B ==> mem_bytes_at a 1 (jump_to hdr raw).vs_memory =
      mem_bytes_at a 1 s.vs_memory` by
     (rpt strip_tac >>
      simp[Abbr `raw`,jump_to_def] >>
      irule EQ_TRANS >> irule_at Any mstore_mem_bytes_at_disjoint >>
      simp[update_var_def] >>
      gvs[SUBSET_DEF,venomMemDefsTheory.regions_disjoint_def] >>
      qpat_x_assum `!x. x IN B ==> _` (qspec_then `a` mp_tac) >>
      simp[] >>
      `SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
        simp[LE_MULT_RCANCEL] >> decide_tac) >>
  simp[] >> reverse (rpt conj_tac)
  >- (simp[Abbr `raw`,Abbr `H`,Abbr `qt`,Abbr `q`] >>
      drule_all prefix_loop_increment_run >> simp[LET_THM]) >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  `dst <> fresh` by metis_tac[] >>
  qpat_assum `!x. x <> fresh ==> _`
    (qspec_then `dst` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  qpat_assum `!x. x <> fresh ==> _`
    (qspec_then `slot_var` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  simp[Abbr `raw`,Abbr `fresh`] >>
  simp[SUBSET_DEF,DISJOINT_DEF,EXTENSION]
  >- (qpat_x_assum `DISJOINT B tn.t_mem` mp_tac >>
      simp[DISJOINT_DEF,EXTENSION] >> metis_tac[])
  >- (rpt gen_tac >> tautLib.TAUT_TAC) >>
  qpat_x_assum `fresh_vars_wrt limit_st (jump_to _ _)` mp_tac >>
  simp[jump_to_def]
QED

Finalise prefix_complete_backedge_support_pair

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_complete_child_iteration:
 (^CshiftCode) ty tv ==>
 !middle end_st child_dst child_src prepared ctx func site limit_st
  sb d D N ids root_di av vs j next slot_id slot initial outsz
  G tn b sz dst slot_var iv nv id hdr bb hdr_bb prefix B header Ddead lo PG.
 compile_abi_decode_to_buf (Var child_dst) child_src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av (EL j vs) /\
 type_memory_bytes ce ty = type_memory_size tv /\
 eval_operand child_src prepared = SOME (n2w sb) /\
 eval_operand (Var child_dst) prepared = SOME (n2w (d+32+j*type_memory_size tv)) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) prepared.vs_data_section =
   enc (vyper_to_abi_type env ty) av /\
 (!x. child_src = Var x \/ Var child_dst = Var x \/ Lit 0w = Var x ==>
   not_fresh_at middle x) /\
 end_st.cs_next_var <= limit_st.cs_next_var /\
 fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
 (middle.cs_blocks = end_st.cs_blocks \/ !bb.
   lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
   phi_prefix_length bb.bb_instructions = 0) /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 frag_ids middle end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 FLOOKUP G child_dst = SOME (b,sz) /\ b <= d+32+j*type_memory_size tv /\
 d+32+SUC j*type_memory_size tv <= b+sz /\
 op_taint tn child_src = {} /\ op_taint tn (Var child_dst) = {} /\
 allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ ~ctx_has_dalloca ctx /\ lo <= d /\
 (^Ok) k ctx func site ids D N d outsz next limit_st
   tv vs slot_id slot initial j j prepared /\
 j < LENGTH vs /\ all_have_type tv vs /\ D <= d /\ d+outsz <= D+N /\
 32+LENGTH vs*type_memory_size tv <= outsz /\
 venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
 next <= middle.cs_next_var /\ slot_id IN ctor_actual_sites func ids /\
 lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
   (STRING #"%" (toString nv)) (Var slot_var) hdr /\
 LENGTH end_st.cs_current_insts = LENGTH prefix /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 next <= nv /\ nv < limit_st.cs_next_var /\
 eval_operand (Var iv) prepared = SOME (n2w j) /\
 eval_operand (Var slot_var) prepared = SOME (n2w slot) /\
 slot < dimword (:256) /\ LENGTH vs < dimword (:256) /\ lo <= slot /\
 FLOOKUP G slot_var = SOME (slot,32) /\ FLOOKUP G dst = SOME (b,sz) /\
 op_taint tn (Var slot_var) = {} /\ op_taint tn (Var iv) = {} /\
 op_taint tn (Var dst) = {} /\
 abi_decoder_operand_live next (Var slot_var) /\
 abi_decoder_operand_live next (Var dst) /\
 not_fresh_at middle slot_var /\ not_fresh_at middle iv /\ not_fresh_at middle dst /\
 FINITE B /\ B SUBSET range_bytes [(d,32+j*type_memory_size tv)] /\
 DISJOINT B tn.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 prepared.vs_memory) ==>
   mem_bytes_at d 32 mem = header /\ elems_in_memory (TAKE j vs) (d+32) tv mem) ==>
 ?t H qt A.
 (^Ok) k ctx func site ids D N d outsz next limit_st
   tv vs slot_id slot initial (SUC j) (SUC j) t /\
 ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
 abi_decode_sim ctx func prepared t /\
 allocas_from lo t /\ lo <= t.vs_alloca_next /\
 FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst = SOME (b,sz) /\
 op_taint qt (Var slot_var) = {} /\ op_taint qt (Var dst) = {} /\
 qt.t_mem SUBSET tn.t_mem /\ DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. abi_decoder_older_vars next x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 FINITE A /\ A SUBSET range_bytes [(d,32+SUC j*type_memory_size tv)] /\
 DISJOINT A qt.t_mem /\ B SUBSET A /\
 (!a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 prepared.vs_memory) /\
 (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 t.vs_memory) ==>
   mem_bytes_at d 32 mem = header /\ elems_in_memory (TAKE (SUC j) vs) (d+32) tv mem) /\
 t.vs_code = prepared.vs_code /\ t.vs_gas_readings = prepared.vs_gas_readings /\
 t.vs_outcomes = prepared.vs_outcomes /\ t.vs_tx_ctx = prepared.vs_tx_ctx /\
 t.vs_block_ctx = prepared.vs_block_ctx /\
 (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x prepared) /\
 (!a. a < lo ==> read_byte a t.vs_memory = read_byte a prepared.vs_memory) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn prepared)
Proof
 disch_then (mk_asm "child") >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next /\
  fresh_vars_wrt limit_st prepared` by
   (qpat_assum `_ k ctx func site ids D N d outsz next limit_st tv vs slot_id slot initial j j prepared`
     (mp_tac o BETA_RULE) >> simp[]) >>
 `d+32+SUC j*type_memory_size tv <= D+N` by
   (`SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
     simp[LE_MULT_RCANCEL] >> decide_tac) >>
 asm "child" (fn th =>
   qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ _ = _`
     (mp_then Any mp_tac (BETA_RULE th))) >>
 disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ prepared`)) >>
 disch_then (drule_at (Pat `fresh_vars_wrt _ prepared`)) >>
 disch_then (drule_at (Pat `FLOOKUP G child_dst = _`)) >>
 disch_then (drule_at (Pat `op_taint tn child_src = _`)) >>
 disch_then (drule_at (Pat `eval_operand child_src prepared = _`)) >>
 disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ prepared`)) >>
 disch_then (qspecl_then [`sb`,`Ddead`,`lo`,`PG`] mp_tac) >>
 (impl_tac >- (asm_x "child" kall_tac >>
   asm_simp_tac (srw_ss()) [MULT_CLAUSES] >>
   conj_tac >- metis_tac[operand_distinct,operand_11] >>
   gvs[MULT_CLAUSES] >> decide_tac)) >>
 asm_x "child" kall_tac >> strip_tac >> suspend "compose"
QED

Resume prefix_complete_child_iteration[compose]:
 `SUC j*type_memory_size tv <= LENGTH vs*type_memory_size tv` by
   simp[LE_MULT_RCANCEL] >>
 `d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  venomMemDefs$regions_disjoint (slot,32)
    (d+32+j*type_memory_size tv,type_memory_size tv)` by
   (qpat_x_assum `SUC j * _ <= _` mp_tac >>
    qpat_assum `32+LENGTH vs * _ <= outsz` mp_tac >>
    qpat_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def,MULT_CLAUSES] >>
    decide_tac) >>
 qpat_x_assum `abi_encoder_registered_effect _ _ prepared actual` mp_tac >>
 asm_simp_tac bool_ss [] >> disch_tac >>
 `(^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j actual` by
   (irule deploy_ctor_array_observation_child >> asm_rewrite_tac[] >>
    goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
    qexists `middle` >> asm_rewrite_tac[] >>
    qpat_assum `_ k ctx func site ids D N d outsz next limit_st tv vs slot_id slot initial j j prepared`
      (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
    asm_simp_tac bool_ss []) >>
 qpat_x_assum `B' SUBSET _` mp_tac >> asm_simp_tac bool_ss [] >> disch_tac >>
 drule_all prefix_loop_child_support >>
 strip_tac >> suspend "backedge"
QED

Resume prefix_complete_child_iteration[backedge]:
 `FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst = SOME (b,sz) /\
  op_taint qt (Var slot_var) = {} /\ op_taint qt (Var iv) = {} /\
  op_taint qt (Var dst) = {}` by metis_tac[] >>
 `eval_operand (Var iv) actual = SOME (n2w j) /\
  eval_operand (Var slot_var) actual = SOME (n2w slot)` by
   (simp[eval_operand_def] >> metis_tac[eval_operand_def]) >>
 `B UNION B' SUBSET {a | d <= a /\ a < d+32+SUC j*type_memory_size tv}` by
   gvs[range_bytes_def] >>
 `lookup_block actual.vs_current_bb func.fn_blocks = SOME bb /\
  actual.vs_inst_idx = LENGTH prefix` by metis_tac[] >>
 qpat_assum `_ k ctx func site ids D N d outsz next limit_st tv vs slot_id slot initial (SUC j) j actual`
   (mp_then Any mp_tac prefix_complete_backedge_support_pair) >>
 disch_then (drule_at (Pat `FLOOKUP H slot_var = _`)) >>
 disch_then (drule_at (Pat `FLOOKUP H dst = _`)) >>
 disch_then (drule_at (Pat `lookup_block actual.vs_current_bb _ = _`)) >>
 disch_then (drule_at (Pat `DISJOINT _ _`)) >>
 disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
 disch_then (qspecl_then [`lo`,`hdr_bb`,`PG`,`Ddead`] mp_tac) >>
 (impl_tac >- asm_rewrite_tac[]) >>
 strip_tac >> suspend "finish"
QED

Resume prefix_complete_child_iteration[finish]:
 rule_assum_tac BETA_RULE >>
 qexistsl [`t`,`H'`,`qt'`,`B UNION B'`] >>
 asm_rewrite_tac[] >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- (irule SUBSET_TRANS >> qexists `qt.t_mem` >> asm_rewrite_tac[]) >>
 conj_tac
 >- (rpt strip_tac >>
     `not_fresh_at middle x` by
       (gvs[abi_decoder_older_vars_def,not_fresh_at_def,IN_DEF] >> decide_tac) >>
     metis_tac[]) >>
 conj_tac >- simp[] >>
 conj_tac >- metis_tac[IN_UNION] >>
 conj_tac >- (gen_tac >> disch_tac >>
   qpat_x_assum `!mem. _ ==> _ /\ elems_in_memory (TAKE (SUC j) vs) _ _ _` irule >>
   metis_tac[]) >>
 conj_tac
 >- (rpt strip_tac >>
     `not_fresh_at middle x` by
       (gvs[abi_decoder_older_vars_def,not_fresh_at_def,IN_DEF] >> decide_tac) >>
     metis_tac[]) >>
 conj_tac >- metis_tac[] >>
 metis_tac[]
QED

Finalise prefix_complete_child_iteration
