(* Uniform memory execution for scratch-free decoder constructors. *)
Theory abiDecodeMemNoScratch
Ancestors
  abiDecodeMemPrimitive abiDecodeMemBytes abiDecodeMemBulkExecution
  abiDecoderArrayHeader abiDecoderBytesEdges abiDecoderBytes
  abiDecoderFrameCompose abiDecoderFrame abiDecoderContract abiDecoderClamp
  abiDecoderReentry moduleLoweringProps localPtrsProps
  exprLoweringProps loweringStateRelDefs fragGasPathMem fragGasMode
  abiEncoder emitHelperProps compileEnv venomExecSemantics venomState
  venomMemDefs valueEncodingProps words arithmetic list

Theorem abi_decode_mem_noscratch_frame[local]:
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  fresh_vars_wrt st s /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  bop <> Lit 0w /\ hi <> Lit 0w /\ p < dimword (:256) /\
  B+H < dimword (:256) /\ B+H <= s.vs_alloca_next /\
  d+N < dimword (:256) /\ d+N <= s.vs_alloca_next /\
  (B+H <= d \/ d+N <= B) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn.
      di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
      asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\
      maxn*asz < dimword (:256))) ==>
  (?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt en t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_frame d N s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?clamp. _) \/ _` strip_assume_tac
  >- suspend "word"
  >- suspend "bytes"
  >> suspend "bulk"
QED
Resume abi_decode_mem_noscratch_frame[word]:
  gvs[] >> (
  `B+p < dimword (:256) /\ B+p+32 <= s.vs_alloca_next /\
   w2n (n2w d:bytes32)+32 <= s.vs_alloca_next` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_all abi_decode_primitive_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `abi_clamp_ok clamp (mload (B+p) s)` >> gvs[]
  >- (disj1_tac >> qexists_tac `t` >> simp[] >>
      mp_tac (Q.INST [`d` |-> `d`, `w` |-> `mload (B+p) s`]
        abi_decode_mstore_frame) >>
      fs[w2n_n2w, vars_pc_only_def, venom_state_component_equality,
         abi_decode_frame_def, mstore_def, write_memory_with_expansion_def]) >>
  metis_tac[])
QED
Resume abi_decode_mem_noscratch_frame[bytes]:
  gvs[] >> (
  mp_tac (Q.INST [`dst` |-> `dst`, `pos` |-> `src`, `base_op` |-> `bop`,
    `hi` |-> `hi`, `st` |-> `st`, `st'` |-> `en`, `s` |-> `s`,
    `func` |-> `func`, `p` |-> `p`, `b` |-> `B`, `h` |-> `H`,
    `d` |-> `d`, `n` |-> `n`, `ctx` |-> `ctx`]
    abi_decode_bytes_bounded_path_mem) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac
  >- metis_tac[] >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  mp_tac (Q.INST [`d` |-> `d`, `a` |-> `B+p`, `c` |-> `c`,
    `n` |-> `n`, `s` |-> `s`] abi_decode_bytes_rounded_capacity_frame) >>
  simp[abi_decode_bytes_copy_size_def, abi_decode_frame_def] >>
  metis_tac[])
QED
Resume abi_decode_mem_noscratch_frame[bulk]:
  gvs[] >> (
  rename1 `compile_abi_decode_to_buf dst src MLOAD bop hi
    (DecDynArray ei msz msz F maxn) st = ((),en)` >>
  mp_tac (Q.INST [`dst` |-> `dst`, `pos` |-> `src`, `base_op` |-> `bop`,
    `hi` |-> `hi`, `st` |-> `st`, `st'` |-> `en`, `s` |-> `s`,
    `func` |-> `func`, `p` |-> `p`, `b` |-> `B`, `h` |-> `H`,
    `d` |-> `d`, `ei` |-> `ei`, `asz` |-> `msz`, `msz` |-> `msz`,
    `maxn` |-> `maxn`, `ctx` |-> `ctx`] abi_decode_bulk_bounded_path_mem) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac
  >- metis_tac[] >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32+c*msz`] >>
  simp[LE_MULT_RCANCEL])
QED
Finalise abi_decode_mem_noscratch_frame

Theorem abi_decode_mem_noscratch:
  !(protected:num -> bool).
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  fresh_vars_wrt st s /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ alloca_room ctx func s /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var hi /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  bop <> Lit 0w /\ hi <> Lit 0w /\ p < dimword (:256) /\
  B+H < dimword (:256) /\ B+H <= s.vs_alloca_next /\
  d+N < dimword (:256) /\ d+N <= s.vs_alloca_next /\
  (B+H <= d \/ d+N <= B) /\
  (!q. protected q ==> q+32 <= s.vs_alloca_next /\ (q+32 <= d \/ d+N <= q)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn.
      di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
      asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\
      maxn*asz < dimword (:256))) ==>
  (?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt en t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    mem_bytes_at B H t.vs_memory = mem_bytes_at B H s.vs_memory /\
    (!q. protected q ==> mload q t = mload q s) /\
    abi_decode_frame d N s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ alloca_inv t /\ alloca_room ctx func t) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  qx_gen_tac `protected` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_mem_noscratch_frame >>
  disch_then (qspec_then `ctx` strip_assume_tac)
  >- (disj1_tac >> qexists_tac `t` >> simp[] >>
      `alloca_inv t /\ alloca_room ctx func t` by
        (conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
         irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
      simp[] >> conj_tac
      >- (fs[abi_decode_frame_def, venomMemDefsTheory.regions_disjoint_def] >>
          first_x_assum irule >> simp[]) >>
      rpt strip_tac >>
      irule abi_decode_footprint_frame_mload >> qexists_tac `[(d,N)]` >>
      simp[GSYM abi_decode_frame_footprint, abi_footprint_disjoint_def] >>
      qpat_x_assum `!q. protected q ==> _` (qspec_then `q` mp_tac) >>
      simp[ADD_COMM]) >>
  metis_tac[]
QED
