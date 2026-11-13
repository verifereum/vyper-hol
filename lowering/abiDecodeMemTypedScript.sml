(* Typed outcomes over the canonical actual-site memory decoder boundary. *)
Theory abiDecodeMemTyped
Ancestors
  abiDecoderCoherence abiDecoderFrame abiDecoderFrameCompose
  exprSimAbiDecodePrimitiveOwned exprSimAbiDecodeMemberExecute
  extcallDecoderStaticSuffix abiCanonicalHeadSize
  abiDecoderMemberFrames abiDecoderSiteEffect allocaHistoryFragment
  abiDecoderTypedContract abiDecoderContract localPtrsProps
  allocationGrowth exprLoweringProps emitHelperProps loweringStateRelDefs compileEnv instIdxIndep
  valueEncodingDefs valueEncoding vyperTypeSystem vyperTypeABI vyperTyping
  vyperABI contractABI venomExecSemantics venomState fragGasPathMem fragGasMode
  fragGasSeqMem bodyUnopFragMemory fragExec finite_map alist list rich_list words arithmetic

(* Shared statement syntax only; these quotations add no HOL constants.
   Free parameters: ctx func limit B P H snap keep_word. *)

val typed_decoder_entry = ``\ce env sf ty tv dst src st fin s sb d.
  abi_decoder_coherent ce env sf ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\
  fin.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  alloca_inv s /\ alloca_room ctx func s /\ fmp_room ctx func s /\
  alloca_history func s /\
  (!inst w p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) ==> n = w2n w) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w H) /\
  hi <> Lit 0w /\ base_op <> Lit 0w /\
  H <= P /\ B+P < dimword(:256) /\ B+P <= s.vs_alloca_next /\
  sb < dimword(:256) /\ d+type_memory_bytes ce ty < dimword(:256) /\
  LENGTH snap = P /\ mem_bytes_at B P s.vs_memory = snap /\
  (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> sb+32 <= H) /\
  (?oid root sz. oid < st.cs_next_id /\
    FLOOKUP s.vs_allocas oid = SOME (root,sz) /\
    root <= d /\ d+type_memory_bytes ce ty <= root+sz) /\
  (B+P <= d \/ d+type_memory_bytes ce ty <= B) /\
  (!id p n. st.cs_next_id <= id /\ id < fin.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (p,n) ==>
    B+P <= p \/ p+n <= B) /\
  (!q. keep_word q ==> (B <= q /\ q+32 <= B+P) \/
    ?id. id < st.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (q,32)) /\
  (!q. keep_word q ==> q+32 <= d \/ d+type_memory_bytes ce ty <= q) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts``;

val typed_decoder_good = ``\env ty tv sb v.
  let at = vyper_to_abi_type env ty; xs = DROP sb (TAKE H snap) in
  sb <= H /\ vyper_decode_valid_enc at xs /\
  (is_dynamic at \/ static_length at <= LENGTH xs) /\
  abi_to_vyper env ty (dec at xs) = SOME v /\ value_has_type tv v``;

val typed_decoder_result = ``\ce env ty tv st fin s sb d.
  (?t v. gas_path_mem ctx func s 0 (OK t) /\
    ^typed_decoder_good env ty tv sb v /\ val_in_memory tv v d t.vs_memory /\
    alloca_inv t /\ alloca_room ctx func t /\ fmp_room ctx func t /\
    alloca_history func t /\
    (!inst w p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) ==> n = w2n w) /\
    fresh_vars_wrt limit t /\ allocation_growth s t /\ decode_static_frame s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id. id < st.cs_next_id \/ fin.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    mem_bytes_at B P t.vs_memory = snap /\
    (!q. keep_word q ==> mload q t = mload q s) /\
    (?fp. (!p n. MEM (p,n) fp <=> ?id.
        st.cs_next_id <= id /\ id < fin.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,n)) /\
      abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::fp) s t) /\
    t.vs_current_bb = fin.cs_current_bb /\
    t.vs_inst_idx = LENGTH fin.cs_current_insts /\ ~t.vs_halted) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t) /\
    ~(?v. ^typed_decoder_good env ty tv sb v))``;

Theorem abi_decode_typed_scalar_view[local]:
  let good = ^typed_decoder_good in
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  sb+32 <= H /\ H <= P /\ LENGTH snap = P /\
  mem_bytes_at B P s.vs_memory = snap ==>
  (good env ty tv sb v <=>
   abi_decode_source_accepts env ty (mem_bytes_at (B+sb) 32 s.vs_memory) v)
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  drule_all abi_decode_scalar_source_shape >> strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `LENGTH (DROP sb (TAKE H snap)) = H-sb` by simp[LENGTH_TAKE, MIN_DEF] >>
  `TAKE 32 (DROP sb (TAKE H snap)) =
   mem_bytes_at (B+sb) 32 s.vs_memory` by
    (simp_tac (srw_ss()) [DROP_TAKE, TAKE_TAKE_MIN] >>
     `MIN 32 (H-sb) = 32` by simp[MIN_DEF] >> simp[] >>
     qpat_x_assum `mem_bytes_at B P s.vs_memory = snap` (SUBST1_TAC o SYM) >>
     irule mem_bytes_at_window >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
     (TAKE 32 (DROP sb (TAKE H snap))) <=>
   vyper_decode_valid_enc (vyper_to_abi_type env ty)
     (DROP sb (TAKE H snap))` by
    (mp_tac (Q.SPECL [`vyper_to_abi_type env ty`, `DROP sb (TAKE H snap)`]
      static_decode_valid_suffix) >> simp[]) >>
  simp_tac std_ss [Abbr `good`, markerTheory.Abbrev_def, LET_THM,
    abi_decode_source_accepts_def] >>
  `sb <= H /\ static_length (vyper_to_abi_type env ty) <=
    LENGTH (DROP sb (TAKE H snap))` by decide_tac >>
  asm_simp_tac std_ss [] >> eq_tac >> strip_tac
  >- (drule_all static_dec_suffix >> metis_tac[]) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP sb (TAKE H snap))`
    by metis_tac[] >>
  `dec (vyper_to_abi_type env ty) (TAKE 32 (DROP sb (TAKE H snap))) =
   dec (vyper_to_abi_type env ty) (DROP sb (TAKE H snap))` by
    (drule_all static_dec_suffix >> simp[]) >>
  `abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
    (DROP sb (TAKE H snap))) = SOME v` by metis_tac[] >>
  simp[] >> irule (CONJUNCT1 abi_to_vyper_well_typed) >> metis_tac[]
QED

Theorem abi_decode_typed_finite_success[local]:
  let entry = ^typed_decoder_entry;
      good = ^typed_decoder_good;
      result = ^typed_decoder_result in
  entry ce env sf ty tv dst src st fin s sb d /\ inst_extends st fin /\
  fin.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts st fin) /\
  run_inst_seq_mem_ok (emitted_insts st fin) s /\
  run_inst_seq (emitted_insts st fin) s = OK t /\
  good env ty tv sb v /\ val_in_memory tv v d t.vs_memory /\
  fresh_vars_wrt limit t /\ decode_static_frame s t /\
  abi_decode_frame d (type_memory_bytes ce ty) s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) ==>
  result ce env ty tv st fin s sb d
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `entry ce env sf ty tv _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `entry`] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fn_has_code st fin func`, `inst_extends st fin`,
        `fin.cs_current_bb = st.cs_current_bb`,
        `s.vs_current_bb = st.cs_current_bb`,
        `s.vs_inst_idx = LENGTH st.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     gvs[fn_has_code_def, inst_extends_def, IS_PREFIX_APPEND] >>
     rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts st fin) = LENGTH fin.cs_current_insts /\
   fin.cs_current_bb = st.cs_current_bb` by
    (qpat_assum `inst_extends st fin`
       (mp_tac o Q.AP_TERM `LENGTH` o REWRITE_RULE [inst_extends_def]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by fs[EVERY_MEM] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st fin)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  drule_all exec_block_run_inst_seq >> strip_tac >>
  `~t.vs_halted` by metis_tac[run_inst_seq_preserves_halted] >>
  `alloca_inv t /\ alloca_room ctx func t` by
    (conj_tac
     >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
     irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  `t.vs_fmp = s.vs_fmp` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `fmp_room ctx func t` by
    (irule fmp_room_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st fin)` by
       fs[EVERY_MEM] >>
     qpat_assum `isPREFIX (emitted_insts st fin) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     drule_all alloca_history_run_inst_seq >> simp[]) >>
  suspend "package"
QED

Resume abi_decode_typed_finite_success[package]:
  markerLib.RESUME_TAC >>
  `decode_static_frame s (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `alloca_inv (t with vs_inst_idx := LENGTH fin.cs_current_insts) /\
   alloca_room ctx func (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (conj_tac
     >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `t` >> simp[]) >>
     irule alloca_room_fields >> qexists_tac `t` >> simp[]) >>
  `abi_decode_frame d (type_memory_bytes ce ty) s
    (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (fs[abi_decode_frame_def] >> first_assum ACCEPT_TAC) >>
  `fmp_room ctx func (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (irule fmp_room_fields >> qexists_tac `t` >> simp[]) >>
  `gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH fin.cs_current_insts))` by
    (qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts st fin) = LENGTH fin.cs_current_insts`
       (fn idx => qpat_assum `LENGTH (FILTER _ (emitted_insts st fin)) = 0`
       (fn cnt => qpat_assum `!ctx'. gas_path_mem _ _ _ _ _`
       (fn path => ACCEPT_TAC (REWRITE_RULE [idx,cnt] (Q.SPEC `ctx` path)))))) >>
  `fresh_vars_wrt limit (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (fs[fresh_vars_wrt_def] >> first_assum ACCEPT_TAC) >>
  `t.vs_current_bb = fin.cs_current_bb` by
    (qpat_assum `!fuel ctx'.
       (!s'. run_inst_seq (emitted_insts st fin) s = OK s' ==> _) /\ _`
       (qspecl_then [`0`, `ctx`] mp_tac) >> simp[]) >>
  `allocation_growth s (t with vs_inst_idx := LENGTH fin.cs_current_insts)` by
    (rw[allocation_growth_def] >> gvs[]) >>
  suspend "normal_package"
QED

Resume abi_decode_typed_finite_success[normal_package]:
  markerLib.RESUME_TAC >> (
  simp[Abbr `result`, markerTheory.Abbrev_def] >> disj1_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH fin.cs_current_insts`, `v`] >>
  simp[eval_op_inst_idx] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >-
    (fs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac)
  >-
    (rpt strip_tac >> irule abi_decode_footprint_frame_mload >>
      qexists_tac `[(d,type_memory_bytes ce ty)]` >>
      simp[GSYM abi_decode_frame_footprint, abi_footprint_disjoint_def] >> metis_tac[]) >>
  qexists_tac `MAP SND (FILTER (\e. st.cs_next_id <= FST e /\
    FST e < fin.cs_next_id) (fmap_to_alist t.vs_allocas))` >>
  conj_tac
  >- (simp[MEM_MAP, MEM_FILTER, MEM_fmap_to_alist_FLOOKUP] >>
      rpt gen_tac >> eq_tac >> strip_tac
      >- (qexists_tac `FST y` >> simp[])
      >> qexists_tac `(id,(p,n))` >> simp[]) >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d,type_memory_bytes ce ty)]` >>
  simp[GSYM abi_decode_frame_footprint] >> rpt strip_tac >>
  qexistsl_tac [`d`, `type_memory_bytes ce ty`] >> simp[])
QED

Finalise abi_decode_typed_finite_success

Theorem abi_decode_typed_finite_reject[local]:
  let entry = ^typed_decoder_entry;
      good = ^typed_decoder_good;
      result = ^typed_decoder_result in
  entry ce env sf ty tv dst src st fin s sb d /\ inst_extends st fin /\
  fin.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts st fin) /\
  run_inst_seq_mem_ok (emitted_insts st fin) s /\
  run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t /\
  ~(?v. good env ty tv sb v) ==>
  result ce env ty tv st fin s sb d
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `entry ce env sf ty tv _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `entry`] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fn_has_code st fin func`, `inst_extends st fin`,
        `fin.cs_current_bb = st.cs_current_bb`,
        `s.vs_current_bb = st.cs_current_bb`,
        `s.vs_inst_idx = LENGTH st.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     gvs[fn_has_code_def, inst_extends_def, IS_PREFIX_APPEND] >>
     rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >>
  simp[Abbr `result`, markerTheory.Abbrev_def] >> disj2_tac >> metis_tac[]
QED
