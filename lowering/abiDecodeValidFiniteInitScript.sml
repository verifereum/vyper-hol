(* The real index-zero cut of allocation-backed, nonbulk dynamic decoding. *)
Theory abiDecodeValidFiniteInit
Ancestors
  abiValidAllocatedArrayInit abiValidAllocatedArrayPrefix abiValidAllocatedContract
  abiDecodeValidArrayHeader actualIndexInitPtr abiMalformedRecursiveInterface abiMalformedTraversal
  abiDecoderRecursiveArray abiDecoderRecursiveLoopEntry abiDecoderPrimitiveLoopEntry abiDecoderLoop
  abiDecoderArrayInit abiDecoderArrayInitReentry ctorAbiActualWorld allocaHistory
  abiValidAllocatedObservations logStoreDataOriginPtr entryDecodeStaticProps
  abiMalformedMemberSetup abiMalformedSiteFrame loweringStateRelDefs
  abiDecoderSequenceReach entryDecoderHistoryFrame decoderNavigationPtr
  abiDecodePtrMemberFrame decoderGhostFramePtr abiCallerAllocation
  allocaSiteResource stateRelProj abiDecodeStaticProps
  bodyPtrBopHashSuffix fragGasOriginPtr freshWrites
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderIndexInit abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv fragExec instIdxIndep
  ptrDiscipline ghostPcTransportPtr venomState venomExecSemantics venomInst
  finite_map pred_set words list rich_list arithmetic

Theorem finite_init_cuts[local]:
  abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
    ((ip,cnt),ls) /\ fn_has_code st ls func /\
  run_inst_seq (emitted_insts st ls) s = OK t ==>
  ?a gs hs g u.
    abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride st = (a,gs) /\
    abi_decode_array_header (Var output) a MLOAD gs = (cnt,hs) /\
    abi_decode_index_init hs = (ip,ls) /\
    fn_has_code st gs func /\ fn_has_code gs hs func /\ fn_has_code hs ls func /\
    st.cs_next_var <= gs.cs_next_var /\ gs.cs_next_var <= hs.cs_next_var /\
    gs.cs_current_bb = st.cs_current_bb /\ hs.cs_current_bb = st.cs_current_bb /\
    run_inst_seq (emitted_insts st gs) s = OK g /\
    run_inst_seq (emitted_insts gs hs) (g with vs_inst_idx := LENGTH gs.cs_current_insts) =
      OK (u with vs_inst_idx := LENGTH gs.cs_current_insts) /\
    run_inst_seq (emitted_insts hs ls) (u with vs_inst_idx := LENGTH hs.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH hs.cs_current_insts)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  rename1 `abi_decode_index_init hs = (_,ls)` >>
  rename1 `abi_decode_array_header _ _ MLOAD gs = (_,hs)` >>
  `cs_extends st gs /\ cs_extends gs hs /\ cs_extends hs ls` by
    (rpt conj_tac >> irule cs_extends_same_block >> simp[] >>
     metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
  `fn_has_code st gs func /\ fn_has_code gs hs func /\ fn_has_code hs ls func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `emitted_insts gs ls = emitted_insts gs hs ++ emitted_insts hs ls` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `inst_extends gs ls` by metis_tac[inst_extends_trans] >>
  `emitted_insts st ls = emitted_insts st gs ++ emitted_insts gs ls` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?g u. run_inst_seq (emitted_insts st gs) s = OK g /\
        run_inst_seq (emitted_insts gs hs) g = OK u /\
        run_inst_seq (emitted_insts hs ls) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts st ls) s = OK t` mp_tac >>
     simp[bop_run_inst_seq_append_ok] >> metis_tac[]) >>
  qexistsl_tac [`g`,`u`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts gs hs) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts hs ls)` by fs[EVERY_MEM] >>
  simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]
QED

(* Compose the count setup at the actual cursor left by the guard. *)
Theorem finite_init_header_cut[local]:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride st = (addr,gs) /\
  abi_decode_array_header (Var output) addr MLOAD gs = (cnt,hs) /\
  run_inst_seq (emitted_insts st gs) s = OK g /\
  run_inst_seq (emitted_insts gs hs)
    (g with vs_inst_idx := LENGTH gs.cs_current_insts) = OK u /\
  fn_has_code st gs func /\ fn_has_code gs hs func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  not_fresh_at st source /\ not_fresh_at st output /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  (!x. hi = Var x ==> not_fresh_at st x) /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  lookup_var output s = SOME (n2w d) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\ ptr_covers G tn output s cap /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  32 <= cap /\ d+cap < dimword (:256) /\ d+cap <= s.vs_alloca_next /\
  (B+L <= d \/ d+cap <= B) /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ allocas_from lo s ==>
  ?H th.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH hs.cs_current_insts),H,th)) /\
    abi_decode_ptr_window H th u source (n2w B) L /\ ptr_covers H th output u cap /\
    op_prov H cnt = NONE /\ op_taint th cnt = {} /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    th.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d+32} /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\ allocas_from lo u
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `p < dimword (:256) /\ B+p+32 < dimword (:256) /\ B+p+32 <= s.vs_alloca_next`
    by decide_tac >>
  drule_all abi_decode_dynarray_position_prefix_success_joint >>
  disch_then (qspec_then `PG` (qx_choosel_then [`ar`,`Gg`,`tg`] strip_assume_tac)) >>
  gvs[] >>
  qabbrev_tac `g0 = g with vs_inst_idx := LENGTH gs.cs_current_insts` >>
  `~g0.vs_halted /\ g0.vs_current_bb = gs.cs_current_bb /\
   g0.vs_inst_idx = LENGTH gs.cs_current_insts /\
   g0.vs_allocas = s.vs_allocas /\ g0.vs_alloca_next = s.vs_alloca_next /\
   allocas_from lo g0 /\ lookup_var output g0 = SOME (n2w d) /\
   abi_decode_ptr_window Gg tg g0 ar (n2w (B+p)) 32 /\
   ptr_covers Gg tg output g0 cap` by
    (simp[Abbr `g0`] >>
     `g.vs_halted = s.vs_halted /\ g.vs_current_bb = s.vs_current_bb /\
      g.vs_allocas = s.vs_allocas /\ g.vs_alloca_next = s.vs_alloca_next` by
        (qpat_assum `g = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     `ptr_covers Gg tg output g cap` by
       (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
     fs[abi_decode_ptr_window_def, lookup_var_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  `not_fresh_at gs output` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `B+p+32 < dimword (:256) /\ B+p+32 <= g0.vs_alloca_next /\
   d+cap < dimword (:256) /\ d+cap <= g0.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  drule_all abi_decode_array_header_success_joint >>
  disch_then (qspec_then `PG` (qx_choosel_then [`H`,`th`] strip_assume_tac)) >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> fs[Abbr `g0`, lookup_var_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `B < dimword (:256)` by decide_tac >>
  `abi_decode_ptr_window H th u source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl [`G`,`s`,`tn`] >>
     simp[IN_DIFF, w2n_n2w] >> rpt strip_tac >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts gs hs)` by fs[EVERY_MEM] >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl [`H`,`th`] >> simp[] >> rpt gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

(* The ghost replay uses the counter slot registered by the physical run. *)
Theorem finite_init_index_cut[local]:
  abi_decode_index_init hs = (ip,ls) /\ fn_has_code hs ls func /\
  run_inst_seq (emitted_insts hs ls) (u with vs_inst_idx := LENGTH hs.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH hs.cs_current_insts) /\
  ~ctx_has_dalloca ctx /\ ~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\
  allocas_from lo u /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  alloca_room ctx func s /\ alloca_inv s /\
  MEM (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (ls.cs_next_var-1))]) (fn_insts func) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
  FLOOKUP t.vs_allocas (ls.cs_next_id-2) = SOME (slot,32) /\
  eval_operand ip t = SOME (n2w slot) /\ slot+32 < dimword (:256) ==>
  ?J tj q.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u with vs_inst_idx := LENGTH hs.cs_current_insts,G,tn) []
      (OK (t with vs_inst_idx := LENGTH ls.cs_current_insts),J,tj)) /\
    ip = Var q /\ ptr_covers J tj q t 32 /\
    tj.t_mem = tn.t_mem DIFF {i | slot <= i /\ i < slot+32} /\
    tj.t_stor = tn.t_stor /\ tj.t_trans = tn.t_trans /\ tj.t_imm = tn.t_imm /\
    (!x. not_fresh_at hs x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP J x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `ls.cs_next_id - 2 = hs.cs_next_id` by decide_tac >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `((FLOOKUP s.vs_allocas hs.cs_next_id = NONE /\
        s.vs_alloca_next + 32 < dimword (:256)) \/
     (?b. FLOOKUP s.vs_allocas hs.cs_next_id = SOME (b,32) /\
        b+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)))` by
    (Cases_on `FLOOKUP s.vs_allocas hs.cs_next_id` >> simp[]
     >- (qpat_assum `MEM (mk_inst _ ALLOCA _ _) _` (mp_then Any mp_tac alloca_room_fresh) >>
         simp[mk_inst_def] >> disch_then (qspecl_then [`s`,`ctx`] mp_tac) >>
         fs[flookup_thm]) >>
     `x = (slot,32)` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
     metis_tac[alloca_site_registered_below]) >>
  qabbrev_tac `u0 = u with vs_inst_idx := LENGTH hs.cs_current_insts` >>
  qabbrev_tac `t0 = t with vs_inst_idx := LENGTH hs.cs_current_insts` >>
  `~u0.vs_halted /\ u0.vs_allocas = s.vs_allocas /\ u0.vs_alloca_next = s.vs_alloca_next /\
   u0.vs_current_bb = hs.cs_current_bb /\ u0.vs_inst_idx = LENGTH hs.cs_current_insts /\
   allocas_from lo u0 /\ eval_operand ip t0 = SOME (n2w slot)` by
    (fs[Abbr `u0`, Abbr `t0`, allocas_from_def, eval_operand_def, lookup_var_def,
        AllCaseEqs()] >> metis_tac[]) >>
  `?J tj q replayed_slot.
     (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u0,G,tn) []
        (OK (t0 with vs_inst_idx := LENGTH ls.cs_current_insts),J,tj)) /\
     ip = Var q /\ eval_operand ip t0 = SOME (n2w replayed_slot) /\
     replayed_slot+32 < dimword (:256) /\ ptr_covers J tj q t 32 /\
     tj.t_mem = tn.t_mem DIFF {i | replayed_slot <= i /\ i < replayed_slot+32} /\
     tj.t_stor = tn.t_stor /\ tj.t_trans = tn.t_trans /\ tj.t_imm = tn.t_imm /\
     (!x. not_fresh_at hs x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP J x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x))` by
    (`(FLOOKUP u0.vs_allocas hs.cs_next_id = NONE /\
         u0.vs_alloca_next + 32 < dimword (:256)) \/
       (?p. FLOOKUP u0.vs_allocas hs.cs_next_id = SOME (p,32) /\
         p+32 <= u0.vs_alloca_next /\ u0.vs_alloca_next < dimword (:256))`
       suffices_by
         (disch_tac >> drule_all actual_index_init_endpoint_ptr_origin_core >>
          disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`H`,`G`]
            (qx_choosel_then [`HG`,`z`,`v`,`p`] strip_assume_tac)) >>
          qexistsl [`HG`,`z`,`v`,`p`] >>
          fs[Abbr `u0`, Abbr `t0`, lookup_var_def] >>
          rpt conj_tac >> rpt gen_tac >> first_x_assum irule >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `replayed_slot < dimword (:256) /\ slot < dimword (:256)` by decide_tac >>
  `replayed_slot = slot` by gvs[n2w_11, LESS_MOD] >>
  qexistsl [`J`,`tj`,`q`] >>
  fs[Abbr `u0`, Abbr `t0`, lookup_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Move the physical post along the same emitted entry jump used for replay. *)
Theorem finite_init_physical_head[local]:
  abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
    ((ip,cnt),ls) /\
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz ip cnt ls =
    ((),en) /\ fn_has_code st ls func /\ fn_has_code ls en func /\
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st ls) s = OK t /\
  abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var sites dstid d outsz s t /\
  fresh_vars_wrt ceiling t /\ mem_word_at d t.vs_memory = n2w (LENGTH vs) /\
  eval_operand ip t = SOME (n2w slot) /\ mload slot t = 0w /\
  slot+32 < dimword (:256) /\
  MEM (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (ls.cs_next_var-1))]) (fn_insts func) /\
  FLOOKUP t.vs_allocas (ls.cs_next_id-2) = SOME (slot,32) /\
  ls.cs_next_id-2 IN sites ==>
  abi_decode_sim ctx func s (jump_to (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) (t with
    vs_inst_idx := LENGTH ls.cs_current_insts)) /\
  abi_valid_allocated_array_inv H ctx func cenv cx es st ceiling
    sites dstid live (Var source) hi pos (Var output) B L xs p d outsz
    ip slot (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
      [STRING #"%" (toString (ls.cs_next_var-1))])
    (STRING #"%" (toString (ls.cs_next_var-1))) (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) tv
      vs s 0 (jump_to (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) (t with vs_inst_idx :=
      LENGTH ls.cs_current_insts))
Proof
  strip_tac >> simp[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  qabbrev_tac `t0 = t with vs_inst_idx := LENGTH ls.cs_current_insts` >>
  `frag_exec ctx st ls (\r. r = s) (\r. r = t0) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[Abbr `t0`] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >>
  disch_then (qspecl_then [`s`,`func`] mp_tac) >> simp[] >> strip_tac >>
  `abi_decode_sim ctx func t0 (jump_to (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) t0)` by
    (irule abi_decoder_loop_entry_sim >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    fs[abi_valid_allocated_effect_def] >>
  `abi_malformed_allocated_window live B L xs s /\ live NOTIN sites /\ live <> dstid /\
   abi_malformed_destination func cenv es.scopes dstid d outsz s` by
    fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_resource_window >> strip_tac >>
  drule_all abi_malformed_resource_destination >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString (ls.cs_next_var-1)))` by
    (drule abi_decode_array_loop_init_trace >> strip_tac >>
     drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >>
     drule abi_decode_index_init_shape >> strip_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `header_st` >> simp[] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_malformed_entry H ctx func cenv cx es st sites dstid live
     (Var source) hi pos (Var output) B L xs p d outsz t` by
    (fs[abi_malformed_entry_def] >>
     fs[abi_malformed_resource_post_def] >> simp[] >> metis_tac[]) >>
  simp[abi_valid_allocated_array_inv_def] >>
  conj_tac
  >- (pop_assum mp_tac >>
      simp_tac bool_ss [abi_malformed_entry_def, stmt_state_rel_jump_to,
                         Abbr `t0`, stmt_state_rel_inst_idx] >>
      simp[NoAsms, abi_malformed_allocated_window_def, abi_malformed_destination_def,
           jump_to_def, eval_operand_def, lookup_var_def]) >>
  simp[abi_valid_allocated_array_prefix_zero, abi_valid_allocated_effect_def,
       abi_malformed_resource_jump, abi_malformed_resource_post_inst_idx,
       jump_to_def, fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
       mload_def, mk_inst_def, Abbr `t0`] >>
  fs[mload_def, fresh_vars_wrt_def, abi_valid_allocated_effect_def,
     abi_valid_allocated_frame_def, abi_malformed_site_range_def,
     abi_malformed_entry_def] >> metis_tac[]
QED

(* Stop at the loop header, before executing the first counter test. *)
Theorem abi_valid_allocated_finite_init_joint:
  abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
    ((ip,cnt),ls) /\
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz ip cnt ls =
    ((),en) /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz s /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  LENGTH vs = abi_head_word (DROP p xs) /\ LENGTH vs <= maxn /\
  p+32+LENGTH vs*stride <= L /\
  MEM (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (ls.cs_next_var-1))]) (fn_insts func) /\
  ls.cs_next_id-2 IN sites /\
  ~ctx_has_dalloca ctx /\ abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?h slot Gh th.
    abi_decode_sim ctx func s h /\
    abi_valid_allocated_array_inv H ctx func cenv cx es st ceiling
      sites dstid live (Var source) hi pos (Var output) B L xs p d outsz
      ip slot (mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
        [STRING #"%" (toString (ls.cs_next_var-1))])
      (STRING #"%" (toString (ls.cs_next_var-1)))
      (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) tv vs s 0 h /\
    eval_operand cnt h = SOME (n2w (LENGTH vs)) /\
    ip = Var (STRING #"%" (toString (ls.cs_next_var-1))) /\
    ptr_covers Gh th (STRING #"%" (toString (ls.cs_next_var-1))) h 32 /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN th.t_mem) /\
    op_prov Gh cnt = NONE /\ op_taint th cnt = {} /\
    op_prov Gh pos = NONE /\ op_prov Gh hi = NONE /\
    op_taint th pos = {} /\ op_taint th hi = {} /\
    abi_decode_ptr_window Gh th h source (n2w B) L /\ ptr_covers Gh th output h outsz /\
    (!m. mem_agree_outside th.t_mem h.vs_memory m ==> mem_word_at d m = n2w (LENGTH vs)) /\
    (!a. d <= a /\ a < d+32 ==> a NOTIN th.t_mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP Gh x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    h.vs_accounts = s.vs_accounts /\ h.vs_transient = s.vs_transient /\
    h.vs_call_ctx = s.vs_call_ctx /\ h.vs_immutables = s.vs_immutables /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+outsz) /\ ~abi_malformed_site_range sites s h a 1 ==>
       (a IN th.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func h /\ allocas_from lo h /\ lo <= h.vs_alloca_next /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK h,Gh,th))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `cs_extends st ls` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st ls func /\ fn_has_code ls en func` by metis_tac[fn_has_code_split] >>
  `ls.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`n` |-> `LENGTH vs`] abi_valid_allocated_array_init_effect)) >>
  disch_then (qx_choosel_then [`t`,`slot`] (strip_assume_tac o SRULE [])) >>
  `mem_word_at d t.vs_memory = n2w (LENGTH vs)` by simp[] >>
  drule_all (Q.INST [`tv` |-> `tv`, `vs` |-> `vs`] finite_init_physical_head) >>
  disch_then (strip_assume_tac o SRULE []) >>
  drule_all finite_init_cuts >>
  disch_then (qx_choosel_then [`addr`,`gs`,`hs`,`g`,`u`] strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx es s /\
   abi_malformed_allocated_window live B L xs s /\ live <> dstid /\
   abi_malformed_destination func cenv es.scopes dstid d outsz s /\
   not_fresh_at st source /\ not_fresh_at st output /\
   (!x. pos = Var x ==> not_fresh_at st x) /\
   (!x. hi = Var x ==> not_fresh_at st x) /\ hi <> Lit 0w /\
   eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
   lookup_var output s = SOME (n2w d) /\ d+outsz < dimword (:256)` by
    (qhdtm_x_assum `abi_malformed_entry` mp_tac >>
     Cases_on `pos` >> Cases_on `hi` >>
     simp[NoAsms, abi_malformed_entry_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def, eval_operand_def] >>
     strip_tac >> simp[]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  Q.SUBGOAL_THEN
    `B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
     d+outsz <= s.vs_alloca_next /\ (B+L <= d \/ d+outsz <= B)`
    (map_every assume_tac o CONJUNCTS)
  >- (fs[abi_malformed_allocated_window_def, abi_malformed_destination_def] >>
      drule_all abi_caller_allocation_separate >> strip_tac >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      imp_res_tac alloca_site_registered_below >> decide_tac) >>
  `p+32 <= L` by decide_tac >>
  qabbrev_tac `u0 = u with vs_inst_idx := LENGTH gs.cs_current_insts` >>
  drule_all (Q.INST [`cap` |-> `outsz`, `u` |-> `u0`] finite_init_header_cut) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Ghead`,`thd`] strip_assume_tac)) >>
  `~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\ allocas_from lo u /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (fs[Abbr `u0`, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e` by
    fs[abi_valid_allocated_effect_def, abi_malformed_resource_post_def] >>
  drule_all finite_init_index_cut >>
  disch_then (qspecl_then [`thd`,`PG`,`Ghead`]
    (qx_choosel_then [`J`,`tj`,`q`] strip_assume_tac)) >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_decoder_recursive_entry_code >> strip_tac >>
  qabbrev_tac `t0 = t with vs_inst_idx := LENGTH ls.cs_current_insts` >>
  `allocas_from lo t0` by
    (simp[Abbr `t0`, allocas_from_def] >> rpt strip_tac >>
     fs[abi_valid_allocated_effect_def] >>
     first_x_assum drule >> strip_tac >> fs[allocas_from_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t0,J,tj) []
     (OK (jump_to (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) t0),J,tj)` by
    (rpt gen_tac >> irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
     simp[Abbr `t0`] >> rename1 `lookup_block ls.cs_current_bb _ = SOME entry_bb` >>
     qexistsl_tac [`entry_bb`,`ls.cs_next_id`] >>
     simp[get_instruction_def, EL_LENGTH_APPEND] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK t0,J,tj)` by
    (qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _` mp_tac >>
     simp[Abbr `u0`, Abbr `t0`] >> metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  qabbrev_tac `head = jump_to (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) t0` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK head,J,tj)` by metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `alloca_history func t0` by
    (simp[Abbr `t0`] >> irule entry_straight_line_alloca_history >>
     simp[] >> qexistsl_tac [`s`,`st`] >> fs[EVERY_MEM]) >>
  `alloca_history func head /\ allocas_from lo head /\ lo <= head.vs_alloca_next` by
    (conj_tac
     >- (irule alloca_history_jump >> simp[Abbr `head`, jump_to_def] >>
         qexists_tac `t0` >> simp[]) >>
     conj_tac
     >- ((qpat_assum `allocas_from lo t0` mp_tac >>
         simp[Abbr `head`, jump_to_def, allocas_from_def] >> (metis_tac[Abbr `head`, jump_to_def, allocas_from_def]))) >>
     `s.vs_alloca_next <= t.vs_alloca_next` by
       fs[abi_valid_allocated_effect_def, abi_malformed_resource_post_def] >>
     simp[Abbr `head`, Abbr `t0`, jump_to_def] >> decide_tac) >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x head = lookup_var x s /\
       FLOOKUP J x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at hs x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
     fs[Abbr `head`, Abbr `u0`, Abbr `t0`, jump_to_def, lookup_var_def] >> metis_tac[]) >>
  `!a. slot <= a /\ a < slot+32 ==> abi_malformed_site_range sites s head a 1` by
    (simp[abi_malformed_site_range_def, Abbr `head`, Abbr `t0`, jump_to_def] >> rpt strip_tac >>
     qhdtm_assum `abi_valid_allocated_effect`
       (strip_assume_tac o REWRITE_RULE [abi_valid_allocated_effect_def]) >>
     qpat_x_assum `!id b sz. _ ==> _ \/ _` drule >> strip_tac
     >- (disj1_tac >> qexistsl_tac [`ls.cs_next_id-2`,`slot`,`32`] >> simp[]) >>
     disj2_tac >> conj_tac >- decide_tac >>
     `slot+32 <= t.vs_alloca_next` suffices_by decide_tac >>
     qhdtm_assum `abi_malformed_resource_post`
       (strip_assume_tac o CONJUNCT1 o REWRITE_RULE [abi_malformed_resource_post_def]) >>
     `alloca_inv t` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     metis_tac[alloca_site_registered_below]) >>
  `!a. d <= a /\ a < d+32 ==> a NOTIN tj.t_mem` by simp[IN_DIFF] >>
  `!a. ~(d <= a /\ a < d+outsz) /\ ~abi_malformed_site_range sites s head a 1 ==>
     (a IN tj.t_mem <=> a IN tn.t_mem)` by
    (rpt strip_tac >> simp[IN_DIFF] >>
     `~(slot <= a /\ a < slot+32)` by metis_tac[] >>
     `~(d <= a /\ a < d+32)` by decide_tac >> simp[]) >>
  `!a. B <= a /\ a < B+L ==> ~abi_malformed_site_range sites s head a 1` by
    (`live NOTIN sites` by fs[abi_malformed_entry_def] >>
     qhdtm_assum `abi_malformed_allocated_window`
       (strip_assume_tac o REWRITE_RULE [abi_malformed_allocated_window_def]) >>
     rpt strip_tac >> drule_all abi_malformed_site_range_protected >> decide_tac) >>
  `abi_decode_ptr_window J tj head source (n2w B) L` by
    (`B < dimword (:256)` by decide_tac >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     simp[w2n_n2w] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  `ptr_covers J tj output head outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `(!m. mem_agree_outside tj.t_mem head.vs_memory m ==> mem_word_at d m = n2w (LENGTH vs))` by
    (rpt strip_tac >>
     `mem_bytes_at d 32 head.vs_memory = mem_bytes_at d 32 m` by
       (irule mem_agree_outside_window >> qexists_tac `tj.t_mem` >> simp[]) >>
     qpat_assum `mem_word_at d t.vs_memory = n2w (LENGTH vs)` mp_tac >>
     fs[abiStaticAggregatePropsTheory.mem_word_at_bytes, Abbr `head`, Abbr `t0`, jump_to_def]) >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `cnt = Var (STRING #"%" (toString gs.cs_next_var))` by
    (qpat_x_assum `abi_decode_array_header _ _ MLOAD gs = _` mp_tac >>
     simp[NoAsms, abiDecoderArrayHeaderTheory.abi_decode_array_header_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, pairTheory.UNCURRY]) >>
  `op_prov J cnt = NONE /\ op_taint tj cnt = {}` by
    (`not_fresh_at hs (STRING #"%" (toString gs.cs_next_var))` by
       simp[not_fresh_at_def, builtinIntClampTheory.fresh_var_name_eq] >>
     fs[op_prov_def]) >>
  `!op. (!x. op = Var x ==> not_fresh_at st x) ==>
      op_prov J op = op_prov G op /\ op_taint tj op = op_taint tn op` by
    (Cases >> simp[op_prov_def, op_taint_def] >> metis_tac[op_taint_def]) >>
  `op_prov J pos = NONE /\ op_prov J hi = NONE /\
   op_taint tj pos = {} /\ op_taint tj hi = {}` by metis_tac[] >>
  `q = STRING #"%" (toString (ls.cs_next_var-1))` by
    (`ls.cs_next_var-1 = hs.cs_next_var` by decide_tac >>
     metis_tac[operand_11]) >>
  `ptr_covers J tj q head 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`J`,`t`,`tj`] >>
     simp[Abbr `head`, Abbr `t0`, jump_to_def, lookup_var_def]) >>
  qpat_x_assum `!v. abi_decode_sim ctx func s _ /\ _`
    (qspec_then `tv` strip_assume_tac) >>
  `eval_operand cnt head = SOME (n2w (LENGTH vs))` by
    (fs[Abbr `head`, Abbr `t0`, jump_to_def, eval_operand_def, lookup_var_def]) >>
  `head.vs_accounts = s.vs_accounts /\ head.vs_transient = s.vs_transient /\
   head.vs_call_ctx = s.vs_call_ctx /\ head.vs_immutables = s.vs_immutables` by
    simp[Abbr `head`, Abbr `t0`, jump_to_def] >>
  `!a. slot <= a /\ a < slot+32 ==> a NOTIN tj.t_mem` by simp[IN_DIFF] >>
  qexistsl_tac [`head`,`slot`,`J`,`tj`] >>
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
  gs[Abbr `head`, Abbr `t0`]
QED
