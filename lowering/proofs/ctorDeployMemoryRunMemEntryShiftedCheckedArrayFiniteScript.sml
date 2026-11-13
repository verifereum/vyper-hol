Theory ctorDeployMemoryRunMemEntryShiftedCheckedArrayFinite
Ancestors
  ctorDeployMemoryRunMemEntryShiftedCheckedArrayBody ctorDeployMemoryRunMemEntryArrayFinite
  ctorDeployMemoryRunMemEntryShiftedCheckedArrayEdges ctorDeployMemoryFrontier
  ctorAbiActualArrayFinite abiDecoderRecursiveLoopContext fragGasPathMem arithmetic abiDecoderLoop
  abiDecodeRanges abiDecoderTypedContract abiDecoderContract compileEnv words list
  abiDecoderCoherence abiEncoder contractABI abiEncoderRegisteredEffect abiDecoderReentry
  ctorAbiActualObservations ctorAbiActualSites abiEncoderProps pred_set

val Ck = ``\ty tv.
 !r dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

val O = ``\k ctx func site ids D N d outsz next limit_st
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
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s``;

val P = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD (Lit 0w) hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) hi ip src dst
    0 sb d slot b cap next initial /\
  fn_inst_ids_distinct func /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH initial.vs_data_section /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  slot_id IN ctor_actual_sites func ids /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem ctor_checked_array_loop_step_from:
  (^Ck) ty tv /\ ^P /\
  (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^O) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\ gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_checked_array_header_reach_from >>
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
  drule_all ctor_checked_array_iteration_from >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >> conj_tac
  >- metis_tac[abi_decode_sim_trans] >>
  qpat_x_assum `gas_path_mem ctx func s 0 (OK h)` mp_tac >>
  qpat_x_assum `gas_path_mem ctx func h 0 (OK t)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_path_mem_then, ADD]
QED

Theorem ctor_checked_array_loop_finite_from:
  (^Ck) ty tv /\ ^P /\
  (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial i i s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^O) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) t /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\ gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `R = \j u. (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` >>
  qabbrev_tac `Post = \u. (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u /\
    ~u.vs_halted /\ u.vs_current_bb = exit_lbl /\ u.vs_inst_idx = 0` >>
  `i <= LENGTH vs /\ R i s` by (simp[Abbr `R`] >> fs[]) >>
  `!j u. j < LENGTH vs /\ R j u /\ alloca_history func u ==>
    ?v. R (SUC j) v /\ abi_decode_sim ctx func u v /\
      gas_path_mem ctx func u 0 (OK v) /\
      v.vs_gas_readings = u.vs_gas_readings /\ alloca_history func v` by
    (simp[Abbr `R`] >> rpt strip_tac >>
     `(^O) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial j j u` by asm_simp_tac bool_ss [] >>
     asm "child" assume_tac >>
     drule_all ctor_checked_array_loop_step_from >> simp[CONJ_ASSOC]) >>
  `!u. R (LENGTH vs) u /\ alloca_history func u ==>
    ?v. Post v /\ abi_decode_sim ctx func u v /\
      gas_path_mem ctx func u 0 (OK v) /\
      v.vs_gas_readings = u.vs_gas_readings /\ alloca_history func v` by
    (simp[Abbr `R`, Abbr `Post`] >> rpt strip_tac >>
     `(^O) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u` by simp[] >>
     drule_at (Pat `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ctor_checked_array_header_reach_from >>
     disch_then (drule_at (Pat `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     (impl_tac >- asm_simp_tac bool_ss []) >> simp[CONJ_ASSOC]) >>
  `?t. Post t /\ abi_decode_sim ctx func s t /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t` by
    (asm_x "child" kall_tac >> irule ctor_checked_finite_bridge >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`R`, `i`, `LENGTH vs`] >> asm_simp_tac bool_ss []) >>
  gvs[Abbr `Post`] >> goal_assum (drule_at Any) >> simp[]
QED
