Theory ctorDeployLoweringEntryCompleteArrayRun
Ancestors
 ctorDeployLoweringEntryCompleteArrayBody ctorDeployLoweringEntryArrayOps
 ctorDeployLoweringEntryArrayRun ctorDeployLoweringEntryArrayFrame
 abiDecoderArrayBackedge abiDecoderPrimitiveLoopEntry abiDecoderLoop abiDecoderLoopRegisters abiDecoderLoopSetup abiDecoderExecution
 abiDecoderContract abiDecoderReentry abiDecoderTypedContract
 abiEncoderRegisteredEffect ctorAbiActualSites ctorDeployMemoryFrontier
 compileEnv venomState venomExecSemantics venomMemDefs valueEncoding
 ASCIInumbers words list finite_map arithmetic fragGasPath
 abiDecoderRecursiveLoopContext abiDecoderRecursiveLoopLayout abiCanonicalHeadSize abiDecoderHeaderGasPath

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

Theorem deploy_ctor_array_entry_complete_jump:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >> drule_all deploy_ctor_array_observation_jump >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all abi_decoder_loop_entry_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `jump_to hdr s` >> simp[jump_to_def]
QED

Theorem deploy_ctor_array_header_complete_run:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid ip src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[] >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) srcaddr (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all deploy_ctor_array_header_observation >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem deploy_ctor_array_header_complete_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (`!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op s = SOME w` by
       (rpt strip_tac >> drule_all deploy_ctor_array_observation_operand >> simp[]) >>
     fs[abi_decoder_ranges_def, Excl "enc_def"] >> conj_tac >>
     first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all deploy_ctor_array_header_complete_run >> simp[]
QED

val Ccomplete = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx``;

val Pk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  fn_inst_ids_distinct func /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  slot_id IN ctor_actual_sites func ids /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem deploy_ctor_array_loop_complete_step:
  (^Ccomplete) ty tv /\ ^Pk /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all deploy_ctor_array_header_complete_reach >>
  disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `h.vs_current_bb = st.cs_current_bb` by gvs[] >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `32 + LENGTH vs * type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (asm_simp_tac bool_ss [] >> simp[]) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb _ = _ /\ _` strip_assume_tac >>
  `~h.vs_halted /\ h.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  asm "child" assume_tac >>
  drule_all deploy_ctor_array_iteration_complete >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_array_complete_finite_bridge[local]:
  i <= n /\ R i s /\
  (!j u. j < n /\ R j u ==> ?v. R (SUC j) v /\ abi_decode_sim ctx func u v) /\
  (!u. R n u ==> ?v. Post v /\ abi_decode_sim ctx func u v) ==>
  ?v. Post v /\ abi_decode_sim ctx func s v
Proof
  strip_tac >> irule abi_decode_finite_iteration >>
  qexistsl [`n`, `i`, `R`] >> simp[]
QED

Theorem deploy_ctor_array_loop_complete_finite:
  (^Ccomplete) ty tv /\ ^Pk /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial i i s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) t /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `R = \j u. (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    u.vs_outcomes = s.vs_outcomes /\ u.vs_tx_ctx = s.vs_tx_ctx /\
    u.vs_block_ctx = s.vs_block_ctx` >>
  qabbrev_tac `Post = \u. (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u /\
    ~u.vs_halted /\ u.vs_current_bb = exit_lbl /\ u.vs_inst_idx = 0 /\
    u.vs_outcomes = s.vs_outcomes /\ u.vs_tx_ctx = s.vs_tx_ctx /\
    u.vs_block_ctx = s.vs_block_ctx` >>
  `i <= LENGTH vs /\ R i s` by
    (simp[Abbr `R`] >> fs[]) >>
  `!j u. j < LENGTH vs /\ R j u ==>
    ?v. R (SUC j) v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`] >> rpt strip_tac >> asm "child" assume_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial j j u` by simp[] >>
     drule_all deploy_ctor_array_loop_complete_step >>
     disch_then (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qexists `v` >> fs[]) >>
  `!u. R (LENGTH vs) u ==> ?v. Post v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`, Abbr `Post`] >> rpt strip_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u` by simp[] >>
     drule_all (Q.INST [`s` |-> `u:venom_state`, `j` |-> `LENGTH (vs:vyperValue$value list)`]
       deploy_ctor_array_header_complete_reach) >>
     disch_then (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qexists `v` >> fs[]) >>
  `?t. Post t /\ abi_decode_sim ctx func s t` by
    (irule deploy_ctor_array_complete_finite_bridge >> qexistsl [`R`, `i`, `LENGTH vs`] >>
     asm_simp_tac bool_ss []) >>
  gvs[Abbr `Post`] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_array_prepared_complete_run:
 (^Ccomplete) ty tv /\ ^(subst [``initial:venom_state`` |-> ``prepared:venom_state``] Pk) /\
 (^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
 lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH prefix /\
 abi_decode_sim ctx func initial prepared /\
 prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
 prepared.vs_block_ctx = initial.vs_block_ctx ==>
 ?actual.
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   (^Ok) k ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
     tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   abi_decode_sim ctx func initial actual /\
   actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
   actual.vs_block_ctx = initial.vs_block_ctx
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule deploy_ctor_array_observation_self >> goal_assum (drule_at Any)) >>
 drule_all deploy_ctor_array_entry_complete_jump >>
 disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 asm "child" assume_tac >>
 drule_all deploy_ctor_array_loop_complete_finite >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual` by
   (irule deploy_ctor_array_observation_compose >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> conj_tac
 >- (irule deploy_ctor_array_observation_exit >> goal_assum (drule_at Any)) >>
 irule abi_decode_sim_trans >> qexists `prepared` >> asm_simp_tac bool_ss [] >>
 irule abi_decode_sim_trans >> qexists `h` >> simp[]
QED

Theorem deploy_ctor_array_entry_complete_gas_path:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix ==>
  ?h. gas_path ctx func s 0 (OK h) /\
    (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >> drule_all deploy_ctor_array_observation_jump >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all gas_path_jump >> disch_then (qspec_then `ctx` assume_tac) >>
  `abi_decode_sim ctx func s (jump_to hdr s)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexists `jump_to hdr s` >> simp[jump_to_def]
QED

Theorem deploy_ctor_array_header_complete_gas_run:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid ip src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx /\ gas_path ctx func s 0 (OK h)
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[] >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) srcaddr (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_decode_ready_header_gas_path >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all deploy_ctor_array_header_observation >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem deploy_ctor_array_header_complete_gas_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    h.vs_outcomes = s.vs_outcomes /\ h.vs_tx_ctx = s.vs_tx_ctx /\
    h.vs_block_ctx = s.vs_block_ctx /\ gas_path ctx func s 0 (OK h)
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (`!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op s = SOME w` by
       (rpt strip_tac >> drule_all deploy_ctor_array_observation_operand >> simp[]) >>
     fs[abi_decoder_ranges_def, Excl "enc_def"] >> conj_tac >>
     first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all deploy_ctor_array_header_complete_gas_run >> simp[]
QED
