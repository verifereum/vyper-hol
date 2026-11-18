Theory bodyFullStoreSlotsStaticWrites
Ancestors
  exprSimAbiDecodeSuffixWrites context compileEnv emitHelper fragExec
  exprSimAbiGasBridge exprLoweringProps loweringStateRelDefs venomInst list arithmetic

(* Thread an ambient allocation bound through counter reassignments. *)
Theorem slots_writes_bound_bind[local]:
  (!st v st'. b <= st.cs_next_var /\ action st = (v,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?n. b <= n /\ x = STRING #"%" (toString n)) /\
  (!v st r st'. b <= st.cs_next_var /\ next v st = (r,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?n. b <= n /\ x = STRING #"%" (toString n)) ==>
  !st r st'. b <= st.cs_next_var /\ comp_bind action next st = (r,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?n. b <= n /\ x = STRING #"%" (toString n)
Proof
  strip_tac >> rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >>
  strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `b <= cs'.cs_next_var` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- decide_tac >>
  rpt strip_tac >> drule_all abi_decode_frag_code_split >>
  metis_tac[]
QED

Theorem slots_writes_bound_lift[local]:
  abi_decode_fresh_writes action ==>
  !st v st'. b <= st.cs_next_var /\ action st = (v,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?n. b <= n /\ x = STRING #"%" (toString n)
Proof
  simp[abi_decode_fresh_writes_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem slots_writes_bound_emit[local]:
  (!x. MEM x outs ==> ?n. b <= n /\ x = STRING #"%" (toString n)) ==>
  !st v st'. b <= st.cs_next_var /\ emit_inst opc ops outs st = (v,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?n. b <= n /\ x = STRING #"%" (toString n)
Proof
  simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def,
       emit_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       mk_inst_def, cs_extends_def, DROP_APPEND] >> metis_tac[]
QED

Theorem slots_writes_counter[local]:
  (!n st v st'. n <= st.cs_next_var /\
      next (STRING #"%" (toString n)) st = (v,st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
      ?k. n <= k /\ x = STRING #"%" (toString k)) ==>
  abi_decode_fresh_writes (comp_bind fresh_var next)
Proof
  simp[abi_decode_fresh_writes_def, comp_bind_def, fresh_var_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`st.cs_next_var`,
    `st with cs_next_var := st.cs_next_var + 1`, `v`, `st'`] mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac >- gvs[cs_extends_def] >>
  gvs[frag_code_def, emitted_blocks_def, emitted_insts_def] >> metis_tac[]
QED

val slots_writes_simps = [ETA_THM, abi_decode_fresh_writes_return,
  abi_decode_fresh_writes_prims, abi_decode_fresh_writes_bind];
val SLOTS_WRITES_BIND = ho_match_mp_tac abi_decode_fresh_writes_bind >> conj_tac
  >- simp slots_writes_simps >> gen_tac;
val SLOTS_BOUND_PRIM = FIRST [
  ho_match_mp_tac slots_writes_bound_lift >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp slots_writes_simps >> NO_TAC,
  ho_match_mp_tac slots_writes_bound_emit >> simp[] >> NO_TAC];
val SLOTS_BOUND_BIND = BETA_TAC >> ho_match_mp_tac slots_writes_bound_bind >> conj_tac
  >- SLOTS_BOUND_PRIM >> gen_tac >> BETA_TAC;

Theorem slots_writes_word_loop[local]:
  !src dst cnt tr. abi_decode_fresh_writes
    (compile_word_copy_loop_op src dst cnt LocMemory
      (if tr then LocTransient else LocStorage) F)
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
       word_scale_def, compile_ptr_load_def, compile_ptr_store_def] >>
  ntac 3 SLOTS_WRITES_BIND >>
  irule slots_writes_counter >> gen_tac >>
  simp_tac pure_ss [comp_ignore_bind_def] >> BETA_TAC >>
  rpt SLOTS_BOUND_BIND >> SLOTS_BOUND_PRIM
QED

Theorem slots_writes_simple[local]:
  (!src. abi_decode_fresh_writes (compile_bytestring_word_count src)) /\
  (!src off. abi_decode_fresh_writes (compile_lit_byte_offset src off))
Proof
  conj_tac
  >- (gen_tac >> simp[compile_bytestring_word_count_def] >>
      ntac 2 SLOTS_WRITES_BIND >> simp slots_writes_simps) >>
  rpt gen_tac >> simp[compile_lit_byte_offset_def] >> IF_CASES_TAC >>
  simp slots_writes_simps >> Cases_on `src` >> simp slots_writes_simps
QED

Theorem store_slots_fresh_writes_family:
  (!cenv src dst ty tr.
    abi_decode_fresh_writes (compile_store_slots cenv src dst ty tr)) /\
  (!cenv src dst members mo so tr.
    abi_decode_fresh_writes (compile_store_slots_members cenv src dst members mo so tr)) /\
  (!cenv src dst elem cnt tr.
    abi_decode_fresh_writes (compile_copy_elements_to_slots cenv src dst elem cnt tr))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_slots_def, abi_decode_fresh_writes_return]
  >- (rpt gen_tac >> strip_tac >>
      simp[Once compile_store_slots_def, abi_decode_fresh_writes_bind,
        abi_decode_fresh_writes_ignore_bind, slots_writes_simple]) >>
  suspend "elements"
QED

Resume store_slots_fresh_writes_family[dispatch]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty`
  >- (simp[] >> IF_CASES_TAC
      >- simp[abi_decode_fresh_writes_bind, abi_decode_fresh_writes_prims] >>
      irule abi_decode_fresh_writes_ignore_bind >>
      simp[abi_decode_fresh_writes_return] >> Cases_on `tr` >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
        compile_word_copy_loop_def] >> metis_tac[slots_writes_word_loop]) >>
  simp[] >> Cases_on `is_bytestring_type ty`
  >- simp[abi_decode_fresh_writes_bind, abi_decode_fresh_writes_ignore_bind,
           abi_decode_fresh_writes_return, slots_writes_simple, slots_writes_word_loop] >>
  simp[] >> IF_CASES_TAC >- simp[abi_decode_fresh_writes_prims] >>
  Cases_on `ty` >> gvs[abi_decode_fresh_writes_prims]
  >- (rename1 `ArrayT elem bd` >> Cases_on `bd` >>
      gvs[abi_decode_fresh_writes_bind, abi_decode_fresh_writes_ignore_bind,
          abi_decode_fresh_writes_prims])
QED

Resume store_slots_fresh_writes_family[elements]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  ntac 3 SLOTS_WRITES_BIND >>
  irule slots_writes_counter >> gen_tac >>
  simp_tac pure_ss [comp_ignore_bind_def] >> BETA_TAC >>
  rpt SLOTS_BOUND_BIND >> SLOTS_BOUND_PRIM
QED

Finalise store_slots_fresh_writes_family

Theorem store_slots_fragment_outputs_fresh:
  compile_store_slots cenv src dst ty tr sa = ((),sb) ==>
  !i x. MEM i (frag_code sa sb) /\ MEM x i.inst_outputs ==>
    ~not_fresh_at sa x
Proof
  mp_tac (cj 1 store_slots_fresh_writes_family) >>
  simp[abi_decode_fresh_writes_def, not_fresh_at_def] >> metis_tac[]
QED
