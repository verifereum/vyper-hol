(* Reusable actual-site index allocation, independent of executing function. *)
Theory exprSimAbiDecodeArraySetup
Ancestors
  exprSimAbiDecodeArrayPrefix exprSimAbiDecodeSiteOwnership
  abiDecoderSiteEffect abiDecoderReentryAddress actualDecoderSites
  abiDecoderIndexInit venomExecSemantics venomExecProofs venomMemProps
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomMemDefs venomState venomInst finite_map words list rich_list arithmetic

Theorem abi_decode_index_site_registers[local]:
  exec_alloca inst s (32w:bytes32) = OK t /\ inst.inst_outputs = [out] /\
  lookup_var out t = SOME w ==>
  t.vs_vars = s.vs_vars |+ (out,w) /\ t.vs_labels = s.vs_labels
Proof
  rw[exec_alloca_def] >>
  gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_site_other_ids[local]:
  exec_alloca inst s (32w:bytes32) = OK t ==>
  !id. id <> inst.inst_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  rw[exec_alloca_def] >> gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_site_insts[local]:
  abi_decode_index_init st = (ip,st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE [ip; Lit 0w] []]
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]
QED

Theorem abi_decode_index_site_origin[local]:
  exec_alloca inst s (32w:bytes32) = OK t /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME(p,32) ==>
  p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas inst.inst_id = SOME(p,32)
Proof
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  simp[exec_alloca_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decode_index_init_site_sequence:
  abi_decode_index_init st = (ip,st') /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME(n2w p) /\ mload p t = 0w /\
    fresh_vars_wrt limit_st t /\
    decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32} s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME(p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas st.cs_next_id = SOME(p,32)) /\
    p + 32 <= t.vs_alloca_next /\ p < dimword(:256) /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   MEM inst (fn_insts func)` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all decode_site_allocation >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> strip_tac >>
  rename1 `exec_alloca inst s 32w = OK allocated` >>
  rename1 `FLOOKUP allocated.vs_allocas inst.inst_id = SOME(p,32)` >>
  drule_all abi_decode_index_site_registers >> strip_tac >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `p < dimword(:256)` by
    (fs[decode_site_resources_def, alloca_room_def] >> decide_tac) >>
  drule abi_decode_index_site_insts >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (qpat_x_assum `emitted_insts _ _ = _` (fn th => rewrite_tac[th]) >>
     `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]) s (32w:bytes32) = OK allocated` by
       (qunabbrev_tac `inst` >> first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
     qpat_x_assum `exec_alloca (mk_inst _ _ _ _) _ _ = _`
       (fn th => rewrite_tac[SRULE [mk_inst_def] th]) >>
     simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w]) >>
  `decode_site_effect ctx func st.cs_next_var {} s allocated` by
    (simp_tac bool_ss [decode_site_effect_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt gen_tac >> PairCases_on `entry` >> strip_tac >>
       first_x_assum irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     conj_tac
     >- (simp_tac bool_ss [decode_static_frame_def] >>
         qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[venom_state_component_equality]) >>
     simp_tac bool_ss [decode_memory_frame_def] >> rpt strip_tac >>
     `allocated.vs_memory = s.vs_memory` by
       (qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     simp[]) >>
  `decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32}
     allocated (mstore p 0w allocated)` by
    (`mstore p 0w allocated =
        write_memory_with_expansion p (word_to_bytes (0w:bytes32) T) allocated` by
       simp[mstore_def, write_memory_with_expansion_def] >>
     pop_assum SUBST1_TAC >> irule decode_site_effect_write >>
     simp[]) >>
  `decode_site_effect ctx func st.cs_next_var {a | p <= a /\ a < p+32}
     s (mstore p 0w allocated)` by
    (drule_all decode_site_effect_trans >> simp[]) >>
  `p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas inst.inst_id = SOME(p,32)` by
    (drule_all abi_decode_index_site_origin >> simp[]) >>
  drule abi_decode_index_site_other_ids >> strip_tac >>
  qexistsl [`mstore p 0w allocated`, `p`] >>
  simp[eval_operand_def, fresh_vars_wrt_mstore, mload_mstore_same,
       mstore_def, write_memory_with_expansion_def, Abbr `inst`, mk_inst_def] >>
  fs[mk_inst_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  qpat_x_assum `allocated = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* Existing source windows may be below the allocation frontier, including
   when the scratch allocation was made on a previous loop entry. *)
Theorem abi_decode_index_slot_separation:
  (p = s.vs_alloca_next \/ FLOOKUP s.vs_allocas site = SOME(p,32)) /\
  q+len <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas site = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) ==>
  venomMemDefs$regions_disjoint (q,len) (p,32)
Proof
  strip_tac >- simp[regions_disjoint_def] >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_index_slot_output:
  decode_site_resources ctx func s /\
  decode_site_effect ctx func next writes s t /\
  FLOOKUP s.vs_allocas output = SOME(d,outsz) /\ output <> site /\
  FLOOKUP t.vs_allocas site = SOME(p,32) /\ off+len <= outsz ==>
  venomMemDefs$regions_disjoint (d+off,len) (p,32)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas output = SOME(d,outsz)` by
    (drule_all decode_site_effect_allocation >> simp[]) >>
  `alloca_inv t` by fs[decode_site_effect_def, decode_site_resources_def] >>
  `venomMemDefs$regions_disjoint (d,outsz) (p,32)` by
    (irule allocaSiteResourceTheory.alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_index_slot_source:
  decode_site_effect ctx func next {a | p <= a /\ a < p+32} s t /\
  venomMemDefs$regions_disjoint (q,len) (p,32) ==>
  mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory
Proof
  strip_tac >> irule decode_site_effect_protected >>
  goal_assum (drule_at Any) >> qexists `{(q,len)}` >>
  simp[decode_protects_def, regions_disjoint_def] >> rpt strip_tac >>
  fs[regions_disjoint_def] >> decide_tac
QED
