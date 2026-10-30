Theory abiDecoderMemberBody
Ancestors
  abiDecoderMembers abiDecoderMemberSlice abiDecoderArraySetupInputs abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderDynamic abiDecodeRanges vyperABI
  compileEnv valueEncoding contractABI venomState words list rich_list arithmetic
  abiDecoderDynamicLoopSetup abiDecoderReentry abiCanonicalHeadSize abiDecoderMemberCode
  abiDecoderMemberSetup abiDecoderEmpty abiDecoderEmptyMember abiDecoderOffset abiDecoderCorrect
  abiDecoderArraySetupCode abiDecoderArrayInitExec abiDecoderEffect abiDecoderCounters
  abiDecoderAppend abiDecoderAllocation abiDecoderLoop fragExec abiEncoder venomExecSemantics
  emitHelperProps

(* Coherent heterogeneous members supply canonical child inputs.
   TOP-LEVEL: abi_decoder_member_pre.
   Helpers: member metadata, source slices and output cell bounds. *)
Theorem abi_decoder_members_child_facts:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  has_types (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) /\
  LENGTH pretys = LENGTH preavs /\
  type_memory_size tv = type_memory_bytes ce ty
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`pretys`, `pretvs`, `preavs`, `prevs`] abi_decoder_members_relations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`ty::tys`, `tv::tvs`, `av::avs`, `v::vs`] abi_decoder_members_relations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH pretys = LENGTH preavs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `abi_decoder_coherent ce env sf ty tv /\
   abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v`
    by fs[Once abi_decoder_members_def] >>
  asm_simp_tac (srw_ss()) [MAP_APPEND, has_types_LIST_REL, LIST_REL_APPEND_EQ] >>
  fs[abi_decoder_metadata_def]
QED

Theorem abi_decoder_member_source:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) ==>
  mem_bytes_at (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc s) =
    enc (vyper_to_abi_type env ty) av /\
  abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) + LENGTH (enc (vyper_to_abi_type env ty) av) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) /\
  SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty <=
    SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))
Proof
  strip_tac >> mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  qpat_x_assum `has_types _ _` mp_tac >>
  simp_tac bool_ss [MAP_APPEND, MAP] >> strip_tac >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
  simp_tac bool_ss [MAP_APPEND, MAP] >> strip_tac >>
  drule_all abi_tuple_child_offset_source >> strip_tac >>
  drule_all abi_tuple_child_offset_ranges >> strip_tac >>
  gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"]
QED

Theorem abi_decoder_member_pre:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  fresh_vars_wrt child_st s /\ abi_decoder_reservation child_st.cs_next_id last b cap s /\
  eval_operand childsrc s = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst s = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap s
Proof
  strip_tac >> mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_decoder_member_source >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def] >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`,
    `LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs)))`,
    `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`, `sb`, `src`] >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC] >> gvs[Excl "enc_def"] >> decide_tac
QED

(* Canonical member pointer inputs and recursive preconditions after address setup.
   TOP-LEVEL: abi_decoder_member_pre_address.
   Helper: canonical pointer load, guard and offset agreement. *)
Theorem abi_decoder_canonical_member_inputs:
  has_types (pre ++ aty::post) (pvs ++ av::avs) /\ LENGTH pre = LENGTH pvs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs))))
    (abi_decode_source opc s) = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs))) < dimword (:256) ==>
  (is_dynamic aty ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size pre)) : bytes32) s =
      n2w (head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)) /\
    sb + (head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)) < dimword (:256)) /\
  abi_tuple_child_offset (pre ++ aty::post) (pvs ++ av::avs) (LENGTH pre) =
    if is_dynamic aty then
      head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)
    else SUM (MAP abi_member_head_size pre)
Proof
  strip_tac >>
  `TAKE (LENGTH pre) (pvs ++ av::avs) = pvs` by
    (qpat_assum `LENGTH pre = LENGTH pvs`
      (fn th => pure_rewrite_tac [th, TAKE_LENGTH_APPEND]) >> REFL_TAC) >>
  conj_tac
  >- (strip_tac >> drule_all canonical_member_offset_load >> strip_tac >>
      drule_all canonical_member_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
      asm_simp_tac bool_ss [] >> gvs[head_lengths_acc, Excl "enc_def"] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_tuple_child_offset_append]
QED

Theorem abi_decoder_member_pre_address:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap before /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc before) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_address_frame next before after /\ next <= child_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_reservation child_st.cs_next_id last b cap before /\
  abi_decoder_operand_live child_st.cs_next_var childsrc /\
  abi_decoder_operand_live child_st.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst after = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live child_st.cs_next_var src /\
   abi_decoder_operand_live child_st.cs_next_var dst /\
   abi_decoder_operand_live child_st.cs_next_var hi` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_reservation >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `fresh_vars_wrt child_st (abi_decoder_prune_vars child_st.cs_next_var after)`
    by irule abi_decoder_prune_fresh >>
  `abi_decoder_reservation child_st.cs_next_id last b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)` by simp[] >>
  `abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)`
    by gvs[abi_decoder_prune_ranges, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))))
    (abi_decode_source opc (abi_decoder_prune_vars child_st.cs_next_var after)) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs))`
    by gvs[Excl "enc_def"] >>
  `eval_operand childsrc (abi_decoder_prune_vars child_st.cs_next_var after) = SOME (n2w (sb +
    abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))) /\
   eval_operand childdst (abi_decoder_prune_vars child_st.cs_next_var after) =
    SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys)))`
    by gvs[abi_decoder_prune_eval, Excl "enc_def"] >>
  drule_all (Q.INST [`s` |-> `abi_decoder_prune_vars child_st.cs_next_var after`]
    abi_decoder_member_pre) >> simp[]
QED

(* Reach a heterogeneous child's real entry point from canonical parent bytes.
   TOP-LEVEL: abi_decoder_member_prepare.
   Helper: canonical inputs for the emitted setup. *)
Theorem abi_decoder_member_prepare_inputs:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) ==>
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) : bytes32) s =
      n2w (head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
        SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)) /\
    sb + (head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
      SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)) < dimword (:256)) /\
  abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) =
    if abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) then
      head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
        SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)
    else SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `av` |-> `av`, `avs` |-> `avs`]
    abi_decoder_canonical_member_inputs) >>
  impl_tac >- gvs[MAP_APPEND, Excl "enc_def"] >> strip_tac >>
  gvs[MAP_APPEND, Excl "enc_def"]
QED

Theorem abi_decoder_member_prepare:
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  fn_has_code st middle func /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation middle.cs_next_id last b cap initial /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      middle last (FST ops) (SND ops) opc hi
      (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
        (preavs ++ av::avs) (LENGTH pretys))
      (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap
      (abi_decoder_prune_vars middle.cs_next_var prepared) /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_member_prepare_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= middle.cs_next_var` by
    (Cases_on `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` >>
     Cases_on `hi = Lit 0w` >> gvs[Excl "enc_def"]) >>
  mp_tac (Q.INST [`st'` |-> `middle`,
    `dyn` |-> `abi_decoder_dynamic (type_to_abi_dec_info
      (sf:string |-> (string # vyperAST$type # num) list) ce ty)`,
    `ao` |-> `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`,
    `payload_off` |-> `head_lengths (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) 0 +
      SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs)`]
    abi_decode_member_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys)))`
    by asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`child_st` |-> `middle`, `childsrc` |-> `FST (ops:operand # operand)`,
    `childdst` |-> `SND (ops:operand # operand)`,
    `next` |-> `st.cs_next_var`, `before` |-> `initial:venom_state`, `after` |-> `prepared:venom_state`]
    abi_decoder_member_pre_address) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* Execute an actual heterogeneous member using recursive child correctness.
   TOP-LEVEL: abi_decoder_member_body.
   Helper: split the containing code at member setup. *)
Theorem abi_decoder_member_body_code:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di middle = ((),end_st) /\
  abi_decode_source_opcode opc /\ fn_has_code st end_st func ==>
  fn_has_code st middle func /\ fn_has_code middle end_st func /\
  st.cs_next_id < middle.cs_next_id /\ middle.cs_next_var <= end_st.cs_next_var /\
  st.cs_next_var <= middle.cs_next_var
Proof
  strip_tac >> drule_all abi_decode_member_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `end_st`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[]
QED

Theorem abi_decoder_member_body_helper:
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_reservation middle.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  mp_tac abi_decoder_member_prepare >> impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
      abi_decoder_budget_transport) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`dst` |-> `SND (ops:operand # operand)`,
    `src` |-> `FST (ops:operand # operand)`, `start` |-> `middle`,
    `initial` |-> `prepared:venom_state`,
    `sb` |-> `sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys)`,
    `d` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`] abi_decoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`,
      `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac arith_ss []) >>
  `abi_decode_sim ctx func initial actual` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_empty_canonical_member:
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >> impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  qpat_x_assum `has_types _ _` (assume_tac o SIMP_RULE bool_ss [MAP_APPEND, MAP]) >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  drule_all abi_tuple_child_offset_ranges >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [MAP_APPEND, MAP]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) <= hb /\
    hb < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      rename1 `eval_operand hi initial = SOME (n2w hb)` >>
      qexists_tac `hb` >> asm_simp_tac arith_ss [] >> decide_tac) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex T []`
    (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, dec_info_needs_offset_def])) >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`, `dynamic` |-> `T`]
    abi_decode_empty_member_reach) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) 0 b cap initial actual` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_member_body:
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (mp_tac abi_decoder_empty_canonical_member >>
      impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac abi_decoder_member_body_helper >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED
