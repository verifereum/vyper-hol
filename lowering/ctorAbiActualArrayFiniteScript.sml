(* Finite actual-site array execution; compiled/data contexts contain no credit. *)
Theory ctorAbiActualArrayFinite
Ancestors
  ctorAbiActualArrayHeader ctorAbiActualArrayBody ctorAbiActualArrayInvariant
  abiDecoderRecursiveLoopContext abiDecoderArrayInvariant abiDecoderLoop
  abiCanonicalHeadSize abiDecoderContract abiDecoderExecution abiDecoderTypedContract
  ctorAbiActualSites abiEncoderRegisteredEffect compileEnv venomState words list arithmetic

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels``;

Theorem ctor_actual_array_header_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD (Lit 0w) hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) hi ip src dst
    0 sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (fs[abi_decoder_ranges_def, Excl "enc_def"] >>
     metis_tac[ctor_actual_array_observation_operand]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[ctor_actual_array_observation_def, abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  fs[abi_decode_position_header_delta_def] >>
  `abi_decode_loop_cfg func hdr st.cs_current_bb exit_lbl hid ip src DLOAD
     (STRING #"%" (toString header_var))
     (STRING #"%" (toString (header_var+1)))
     (STRING #"%" (toString (header_var+2)))
     (STRING #"%" (toString (header_var+3)))` by
    fs[abi_decode_loop_cfg_def, abi_decode_position_loop_cfg_def,
       abi_decode_position_header_zero] >>
  drule_all ctor_actual_array_header_run >> simp[]
QED

(* Pure shared hypotheses for header/body composition. *)
val P = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD (Lit 0w) hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) hi ip src dst
    0 sb d slot b cap next initial /\
  fn_inst_ids_distinct func /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  slot_id IN ctor_actual_sites func ids /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem ctor_actual_array_loop_step:
  (^C) ty tv /\ ^P /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_actual_array_header_reach >>
  disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `h.vs_current_bb = st.cs_current_bb` by gvs[] >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `32 + LENGTH vs * type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (asm_simp_tac bool_ss [] >> simp[]) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb _ = _ /\ _` strip_assume_tac >>
  `~h.vs_halted /\ h.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  asm "child" assume_tac >>
  drule_all ctor_actual_array_iteration >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

Theorem ctor_actual_finite_bridge[local]:
  i <= n /\ R i s /\
  (!j u. j < n /\ R j u ==> ?v. R (SUC j) v /\ abi_decode_sim ctx func u v) /\
  (!u. R n u ==> ?v. Post v /\ abi_decode_sim ctx func u v) ==>
  ?v. Post v /\ abi_decode_sim ctx func s v
Proof
  strip_tac >> irule abi_decode_finite_iteration >>
  qexistsl [`n`, `i`, `R`] >> simp[]
QED

Theorem ctor_actual_array_loop_finite:
  (^C) ty tv /\ ^P /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial i i s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) t /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `R = \j u. ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` >>
  qabbrev_tac `Post = \u. ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u /\
    ~u.vs_halted /\ u.vs_current_bb = exit_lbl /\ u.vs_inst_idx = 0` >>
  `i <= LENGTH vs /\ R i s` by
    (simp[Abbr `R`] >> fs[ctor_actual_array_observation_def]) >>
  `!j u. j < LENGTH vs /\ R j u ==>
    ?v. R (SUC j) v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`] >> rpt strip_tac >> asm "child" assume_tac >>
     drule_all ctor_actual_array_loop_step >> simp[CONJ_ASSOC]) >>
  `!u. R (LENGTH vs) u ==> ?v. Post v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`, Abbr `Post`] >> rpt strip_tac >>
     drule_all ctor_actual_array_header_reach >> simp[CONJ_ASSOC]) >>
  `?t. Post t /\ abi_decode_sim ctx func s t` by
    (irule ctor_actual_finite_bridge >> qexistsl [`R`, `i`, `LENGTH vs`] >>
     asm_simp_tac bool_ss []) >>
  gvs[Abbr `Post`] >> goal_assum (drule_at Any) >> simp[]
QED
