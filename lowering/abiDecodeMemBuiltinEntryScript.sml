(* Establish the canonical actual decoder entry after the builtin's setup. *)
Theory abiDecodeMemBuiltinEntry
Ancestors
  abiDecodeMemBuiltinSetup abiDecodeMemHeader exprSimAbiDecodeBuiltin
  exprSimAbiDecodeBuiltinSetup abiBuiltinDecodeSetup abiBuiltinSetupReach
  abiBuiltinAllocation abiDecoderCoherence abiDecoderWordTyped abiDecoderAppend
  abiDecoderCounters abiDecoderReentry abiDecoderContract actualDecoderSites
  freshVarLimit exprLoweringProps loweringStateRelDefs fragExec
  valueEncodingDefs valueEncoding valueEncodingProps compileEnv
  venomExecSemantics venomState words finite_map list arithmetic

Theorem abi_decode_mem_builtin_entry:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty)
    (abi_static_size sf ty) (abi_size_bound sf ty) (type_memory_bytes ce ty)
    st = (out,fin) /\
  abi_decoder_coherent ce env sf ty tv /\ fn_has_code st fin func /\
  abi_builtin_decode_site_resources ctx func st fin.cs_next_id
    (abi_static_size sf ty) (abi_size_bound sf ty) (type_memory_bytes ce ty)
    (LENGTH bs) p d s /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME(n2w p) /\ alloca_history func s /\
  abi_decoder_operand_live st.cs_next_var data /\
  abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ops ready limit_st t.
    abi_builtin_decode_setup data (abi_static_size sf ty) (abi_size_bound sf ty)
      (type_memory_bytes ce ty) st = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (Lit 0w) MLOAD
      (FST (SND ops)) (SND (SND ops)) (type_to_abi_dec_info sf ce ty)
      ready = ((),fin) /\ out = FST ops /\
    fn_has_code ready fin func /\ fn_inst_ids_distinct func /\
    gas_path_mem ctx func s 0 (OK t) /\
    fin.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st t /\
    EVERY (abi_decoder_operand_live ready.cs_next_var)
      [Lit 0w; FST ops; FST (SND ops); SND (SND ops)] /\
    decode_site_resources ctx func t /\ alloca_history func t /\
    eval_operand (FST ops) t = SOME(n2w d) /\
    eval_operand (FST (SND ops)) t = SOME(n2w (p+32)) /\
    eval_operand (SND (SND ops)) t = SOME(n2w (LENGTH bs)) /\
    FST (SND ops) <> Lit 0w /\ SND (SND ops) <> Lit 0w /\
    p+32+LENGTH bs < dimword(:256) /\
    p+32+LENGTH bs <= t.vs_alloca_next /\
    mem_bytes_at (p+32) (LENGTH bs) t.vs_memory = bs /\
    d+type_memory_bytes ce ty < dimword(:256) /\
    FLOOKUP t.vs_allocas
      (abi_builtin_decode_output_site st (abi_static_size sf ty) (abi_size_bound sf ty)) =
      SOME(d,type_memory_bytes ce ty) /\
    abi_builtin_decode_output_site st (abi_static_size sf ty) (abi_size_bound sf ty) <
      ready.cs_next_id /\
    (p+32+LENGTH bs <= d \/ d+type_memory_bytes ce ty <= p+32) /\
    (!id b sz. ready.cs_next_id <= id /\ id < fin.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
      p+32+LENGTH bs <= b \/ b+sz <= p+32) /\
    (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> 32 <= LENGTH bs) /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st (abi_static_size sf ty) (abi_size_bound sf ty))
      (type_memory_bytes ce ty) s t /\ decode_static_frame s t /\
    t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~t.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_bounded_setup >> strip_tac >>
  Cases_on `decoded` >> gvs[] >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st ready /\ cs_extends ready fin` by
    metis_tac[cs_extends_same_block, cs_extends_abi_decode] >>
  drule_all fn_has_code_split >> strip_tac >>
  `ready.cs_next_var <= fin.cs_next_var` by
    metis_tac[abi_decoder_variable_counter] >>
  qspecl_then [`s`, `fin`] strip_assume_tac log_fresh_limit_exists >>
  `ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `decode_site_resources ctx func s /\ fn_inst_ids_distinct func` by
    fs[abi_builtin_decode_site_resources_def] >>
  `alloca_inv s` by fs[decode_site_resources_def] >>
  `p+32 <= s.vs_alloca_next /\ abi_size_bound sf ty < dimword(:256) /\
   type_memory_bytes ce ty < dimword(:256)` by
    (fs[abi_builtin_decode_site_resources_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >> metis_tac[decode_site_resources_def]) >>
  `p < dimword(:256)` by decide_tac >>
  `mload (w2n (n2w p:bytes32)) s = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload, w2n_n2w] >>
  `w2n (n2w p:bytes32)+32 <= s.vs_alloca_next` by simp[w2n_n2w] >>
  suspend "execute"
QED

Resume abi_decode_mem_builtin_entry[execute]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  rename1 `eval_operand data s = SOME(n2w source_p)` >>
  mp_tac (Q.INST [
    `data` |-> `data`, `min_size` |-> `abi_static_size (sf:string |-> (string # type # num) list) ty`,
    `max_size` |-> `abi_size_bound (sf:string |-> (string # type # num) list) ty`, `outsz` |-> `type_memory_bytes ce ty`,
    `st` |-> `st`, `ops` |-> `ops`, `ready` |-> `ready`, `func` |-> `func`,
    `s` |-> `s`, `p` |-> `n2w source_p`, `cnt` |-> `LENGTH (bs:word8 list)`, `d` |-> `d`,
    `limit_st` |-> `limit_st`, `ctx` |-> `ctx`] abi_decode_setup_path_mem) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    fs[abi_builtin_decode_site_resources_def])) >> strip_tac >>
  `decode_site_resources ctx func t /\ decode_static_frame s t` by metis_tac[] >>
  drule_all abi_decode_mem_setup_resources >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "package"
QED

Resume abi_decode_mem_builtin_entry[package]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> 32 <= LENGTH bs` by
    (rpt strip_tac >> drule_all abi_decoder_primitive_cases >> strip_tac >>
     gvs[abi_static_size_def] >>
     Cases_on `bt` >> gvs[is_word_type_def, abi_static_size_def] >>
     Cases_on `b` >> gvs[is_word_type_def, abi_static_size_def]) >>
  qexistsl_tac [`limit_st`, `t`] >>
  gvs[GSYM word_add_n2w, EVERY_DEF] >> metis_tac[]
QED

Finalise abi_decode_mem_builtin_entry
