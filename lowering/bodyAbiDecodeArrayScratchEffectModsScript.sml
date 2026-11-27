Theory bodyAbiDecodeArrayScratchEffectMods
Ancestors
  bodyFullAbiDecodeArrayScratch bodyAbiDecodeGuardedEffectBaseMods
  bodyPtrIfExpAllocKept decoderGhostFramePtr
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeStoreContents
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeInterface bodyPtrIfExpAllocSeparation
  bodyFullAbiDecodeScratchCode bodyPtrIfExpAllocCompiler actualIndexInitPtr
  calldataDynInit allocationPtr venomMemProps allocaFootprint
  bodyFullAllocaFresh bodyFullUnwrapRun fragExecMem fragGasSeqPtr ghostPcTransportPtr logInstSeqPtr
  exprPtrUnwrapAllocation exprPtrUnwrapCopyEdges
  loweringHalt exprLoweringProps
  stateRelProj finite_map words list pair arithmetic
  bodyFullHashKeccakFixed
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

(* Use the exact old packet, with a single new fact under its existing
   witnesses. The compatibility check also checks the horizon scopes. *)
val scratch_old = concl abi_decode_array_scratch_loop_entry_horizon_joint;
val scratch_input_origin =
  let
    val (entry, _) = dest_imp (snd (strip_forall scratch_old))
    fun origin_redex t =
      case strip_comb t of (f, [s]) => is_abs f andalso is_var s andalso fst (dest_var s) = "s"
      | _ => false
  in rator (valOf (List.find origin_redex (strip_conj entry))) end;
val scratch_all =
  let
    val (vs, imp) = strip_forall (beta scratch_old)
    val (entry, post) = dest_imp imp
    val (ws, body) = strip_exists post
    val [t, _, tf, _, _, _] = ws
    val ps = free_vars imp @ vs
    val tm = checked "scratch loop entry" scratch_old
      (list_mk_forall (vs, mk_imp (entry, list_mk_exists (ws,
         mk_conj (body, effect (param ps "s") (param ps "tn") t tf)))))
  in list_mk_forall (free_vars tm, tm) end;

(* Local physical adapters for the old selector's private raw and
   separation proofs. No second scratch store producer is needed. *)
Theorem scratch_effect_actual_separation[local]:
  stmt_state_rel H ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w 32)] [out]) (fn_insts fn) /\
  not_local_ptr ce es.scopes out /\ output_id < id /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  ((?aid ib isz. aid < output_id /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
      ib <= w2n (input_word:256 word) /\
      w2n input_word + LENGTH (input_bytes:8 word list) <= ib+isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
      ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib+isz)) /\
  EVERY (\(a,bytes:8 word list). output_base <= a /\
    a+LENGTH bytes <= output_base+output_cap) protected ==>
  (output_base+output_cap <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= output_base) /\
  (w2n input_word+LENGTH input_bytes <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= w2n input_word) /\
  EVERY (\(a,bytes). a+LENGTH bytes <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= a) protected /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= buffer_allocation_base s id \/ buffer_allocation_base s id+32 <= b)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `output_id <> id` by decide_tac >>
  `output_base+output_cap <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= output_base` by
    (irule ifexp_alloca_old_site_separate >> metis_tac[]) >>
  ((conj_tac >- simp[]) >>
   (conj_tac >-
    (qpat_x_assum `(?aid ib isz. _) \/ (?name ib isz. _)` strip_assume_tac
     >- (`aid <> id` by decide_tac >>
         drule_all ifexp_alloca_old_site_separate >> strip_tac >> decide_tac)
     >> drule_all ifexp_alloca_local_separate >> strip_tac >> decide_tac)) >>
   (conj_tac >-
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     PairCases_on `e` >> gvs[] >>
     first_x_assum drule >> simp[] >> decide_tac)) >>
   metis_tac[ifexp_alloca_local_separate])
QED

Theorem scratch_effect_raw[local]:
  abi_decode_index_init sa = (ip,loop_st) /\
  stmt_state_rel H ctx fn ce cx es s /\ fn_has_code sa loop_st fn /\
  local_ptrs_reserved ce sa ==>
  ?buf sb counter u.
    compile_alloc_buffer 32 sa = (buf,sb) /\ fn_has_code sa sb fn /\
    buf.buf_operand = Var counter /\ ip = Var counter /\
    ~not_fresh_at sa counter /\ not_local_ptr ce es.scopes counter /\
    abi_decoder_operand_live loop_st.cs_next_var ip /\
    sa.cs_next_id < loop_st.cs_next_id /\
    loop_st.cs_current_bb = sa.cs_current_bb /\
    loop_st.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter];
       mk_inst sb.cs_next_id MSTORE [ip;Lit 0w] []] /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]) (fn_insts fn) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]) s = OK u /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (buffer_allocation_base s sa.cs_next_id,32) /\
    run_inst_seq (emitted_insts sa loop_st) s =
      OK (mstore (buffer_allocation_base s sa.cs_next_id) 0w u)
Proof
  strip_tac >> drule abi_decode_scratch_code >> strip_tac >>
  `fn_has_code sa sb fn` by metis_tac[] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `out` (qx_choose_then `u` strip_assume_tac)) >>
  `out = counter` by fs[] >>
  qpat_x_assum `out = counter` SUBST_ALL_TAC >>
  `counter = STRING #"%" (toString sa.cs_next_var)` by
    (drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp[]) >>
  `not_local_ptr ce es.scopes counter` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sa` >> simp[]) >>
  drule_all ifexp_alloca_step_site >> strip_tac >>
  drule_all ifexp_alloca_step_base >> strip_tac >>
  drule_all ifexp_alloca_base_bound >> strip_tac >>
  `loop_st.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter];
       mk_inst sb.cs_next_id MSTORE [ip;Lit 0w] []]` by
    (pure_asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> REFL_TAC) >>
  qexistsl_tac [`buf`,`sb`,`counter`,`u`] >> simp[] >>
  `eval_operand ip u = SOME (n2w (buffer_allocation_base s sa.cs_next_id))` by
    gvs[venomStateTheory.eval_operand_def] >>
  gvs[] >> irule (cj 1 calldata_index_init_after_alloca) >> simp[]
QED

Theorem abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods:
  ^scratch_all
Proof
  rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
  `stmt_state_rel H0 ctx fn ce cx es s` by metis_tac[] >>
  drule_all scratch_effect_raw >>
  disch_then (qx_choose_then `buf` (qx_choose_then `sb`
    (qx_choose_then `counter` (qx_choose_then `u` strip_assume_tac)))) >>
  drule_all scratch_effect_actual_separation >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `cell = buffer_allocation_base s sa.cs_next_id` >>
  `input <> counter /\ ~not_fresh_at origin counter` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(!H. V H ==> stmt_state_rel H ctx fn ce cx es s) /\
   ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn` by metis_tac[] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  qabbrev_tac `al = mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]` >>
  qabbrev_tac `Ga = step_prov PG G al u` >>
  qabbrev_tac `tna = step_taint al s u tn` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]) s = OK u` by
    metis_tac[Abbr `al`] >>
  drule_all bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es u` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx fn ce cx es s` by metis_tac[] >>
     drule_all (Q.INST [`H` |-> `H`]
       (cj 1 bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources)) >>
     simp[]) >>
  `ptr_covers Ga tna counter u 32` by
    (unabbrev_all_tac >> drule_all alloca_step_ptr_covers >> simp[]) >>
  `(!x. x <> counter ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
   (!i. ~(cell <= i /\ i < cell+32) ==> (i IN tna.t_mem <=> i IN tn.t_mem))` by
    (unabbrev_all_tac >>
     drule_all bodyPtrHashBuiltinsAllocFrameTheory.hash_alloca_exterior_effects >>
     disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >> simp[]) >>
  `abi_decode_ptr_window Ga tna u input input_word (LENGTH input_bytes)` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >>
     rpt strip_tac >>
     `i < s.vs_alloca_next` by decide_tac >>
     metis_tac[alloca_step_taint_below_frontier, Abbr `al`, Abbr `tna`]) >>
  suspend "alloc_frame"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[alloc_frame]:
  `u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
   s.vs_alloca_next <= u.vs_alloca_next /\
   tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
   (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
        (s.vs_alloca_next <= i /\ i < u.vs_alloca_next))` by
    (unabbrev_all_tac >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (drule_all fresh_alloca_ghost >>
         disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
         drule_all step_alloca_fresh >> disch_then (qspec_then `counter` assume_tac) >>
         gnvs[venomStateTheory.update_var_def, pred_setTheory.IN_UNION,
              venomStateTheory.venom_state_component_equality]) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
     PairCases_on `site` >>
     `site1 = 32` by
       (irule (cj 1 stmt_state_rel_alloca_site_bound) >>
        simp[] >> rpt (goal_assum (drule_at Any) >> simp[]) >> metis_tac[]) >>
     qpat_x_assum `site1 = 32` SUBST_ALL_TAC >>
     drule reused_alloca_step >> disch_then (qspec_then `counter` assume_tac) >>
     `u = update_var counter (n2w site0) s` by
       (qpat_assum `step_inst_base _ s = OK u` mp_tac >> simp[]) >>
     qpat_x_assum `u = update_var _ _ _` SUBST_ALL_TAC >>
     drule reused_alloca_ghost >>
     disch_then (qspecl_then [`counter`,`PG`,`G`,`tn`] strip_assume_tac) >>
     simp[venomStateTheory.update_var_def] >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `abi_decode_guarded_effect_core s tn u tna` by
    (simp[abi_decode_guarded_effect_core_def] >> decide_tac) >>
  `allocas_from lo s` by metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `allocas_from lo u` by
    (`step_inst 0 ctx al s = OK u` by
       simp[Abbr `al`, venomExecSemanticsTheory.step_inst_non_invoke,
            venomInstTheory.mk_inst_def] >>
     drule_all ptrSafetyTransportTheory.step_inst_allocas_from >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint tna (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     `x <> counter` by (strip_tac >> fs[]) >> simp[]) >>
  `!x. not_fresh_at origin x ==>
    FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     `x <> counter` by (strip_tac >> fs[]) >> simp[]) >>
  `local_ptrs_rel fn ce es.scopes s` by
    (qpat_assum `stmt_state_rel H0 ctx fn ce cx es s`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es Ga tna u` by
    (qx_gen_tac `H` >> disch_tac >>
     `ghost_inv_at (DF H) lo delta ce cx es G tn s` by
       (qpat_assum `!h. V h ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     irule alloc_buffer_ghost_inv_at_locals >> (conj_tac >- asm_rewrite_tac[]) >>
     qexistsl_tac [`G`,`u.vs_alloca_next`,`fn`,`s`,`sa`,`tn`] >>
     asm_rewrite_tac[]) >>
  `ghost_kept_at lo ce es0 origin G0 tn0 s0 Ga tna` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`,`u.vs_alloca_next`,`s`,`tn`] >> asm_rewrite_tac[]) >>
  `stmt_state_rel H0 ctx fn ce cx es u` by metis_tac[] >>
  qpat_assum `stmt_state_rel H0 ctx fn ce cx es u`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `cell+32 <= u.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  `lo <= cell` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `cell < dimword (:256) /\ lookup_var counter u = SOME (n2w cell)` by
    (unabbrev_all_tac >>
     conj_tac >-
       (`buffer_allocation_base s sa.cs_next_id+32 < dimword (:256)` by
          metis_tac[ifexp_alloca_base_bound] >> decide_tac) >>
     drule_all ifexp_alloca_step_base >> simp[]) >>
  `!name b k. local_region ce es.scopes u name b k <=>
             local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  `!name b k. local_region ce es.scopes u name b k ==>
      cell+32 <= b \/ b+k <= cell` by metis_tac[] >>
  `w2n (n2w cell:256 word) = cell` by simp[w2n_n2w, LESS_MOD] >>
  qabbrev_tac `m = mstore cell 0w u` >>
  qabbrev_tac `st = mk_inst sb.cs_next_id MSTORE [Var counter;Lit 0w] []` >>
  qabbrev_tac `Gf = step_prov PG Ga st m` >>
  qabbrev_tac `tnf = step_taint st u m tna` >>
  suspend "store"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[store]:
  `!H. V H ==>
    abi_decode_ptr_write_frame tna u tnf m cell 32 /\
    abi_decode_ptr_window Gf tnf m input input_word (LENGTH input_bytes) /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf m /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
    (!H'. V H' ==> stmt_state_rel H' ctx fn ce cx es m)` by
    (qx_gen_tac `H` >> disch_tac >>
     `ghost_inv_at (DF H) lo delta ce cx es Ga tna u` by metis_tac[] >>
     simp[NoAsms, Abbr `Gf`, Abbr `tnf`, Abbr `st`, Abbr `m`] >>
     qpat_assum `w2n (n2w cell:256 word) = cell` (fn cell_eq =>
       MATCH_MP_TAC (SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_AND_THM, cell_eq]
         (Q.INST [`a` |-> `n2w cell:256 word`, `inst` |-> `al`,
                  `b` |-> `cell`, `sz` |-> `32`, `out` |-> `counter`]
            abi_decode_output_write_frame_joint))) >>
     simp[Abbr `al`, venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `loop_st.cs_current_insts = sa.cs_current_insts ++ [al;st]` by
    (qpat_assum `loop_st.cs_current_insts = _` mp_tac >>
     qpat_assum `ip = Var counter` (fn ip_eq => simp[NoAsms, Abbr `st`, ip_eq])) >>
  `emitted_insts sa loop_st = [al;st]` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND,
         rich_listTheory.DROP_LENGTH_NIL] >>
  `run_inst_seq [al;st] s = OK m` by metis_tac[] >>
  qabbrev_tac `t = m with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  `!obs. fn_has_code sa loop_st obs ==> gas_path ctx obs s 0 (OK t)` by
    (simp[NoAsms, Abbr `t`] >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`[al;st]`,`sa`] >>
     simp[] >> simp[Abbr `al`, Abbr `st`, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]) >>
  `~is_terminator st.inst_opcode` by
    simp[Abbr `st`, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `step_inst_base st u = OK m /\ inst_mem_below_frontier st u` by
    (simp[NoAsms, Abbr `st`, Abbr `m`] >>
     irule scratch_mstore_mem_ok >>
     simp[venomStateTheory.eval_operand_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H0 ctx fn ce cx es s`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H0 ctx fn ce cx es u`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `ctx_has_dalloca ctx ==>
    allocas_below_fmp (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[ptrDisciplineTheory.allocas_below_fmp_def] >>
  suspend "path"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[path]:
  `!D. inst_seq_ptr D lo ctx fn PG G tn [al;st] s Gf tnf` by
    (gen_tac >>
     `ptr_inst_ok D lo 0 ctx fn G tn al s` by
       (irule (Q.INST [`lo0` |-> `0`] ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport) >>
        simp[Abbr `al`, fragExecPtrTheory.ptr_inst_ok_alloca]) >>
     `ptr_inst_ok D lo 0 ctx fn Ga tna st
        (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[NoAsms, Abbr `st`] >> irule ptr_inst_ok_mstore_tainted >>
        simp[ptrDisciplineTheory.allocas_from_def]) >>
     `step_inst_base st (u with vs_inst_idx := SUC s.vs_inst_idx) =
        OK (m with vs_inst_idx := SUC s.vs_inst_idx)` by
       simp[instIdxIndepTheory.step_inst_inst_idx_indep,
            instIdxIndepTheory.exec_result_map_def] >>
     qpat_x_assum `ptr_inst_ok D lo 0 ctx fn Ga tna st _` mp_tac >>
     simp[NoAsms, Abbr `Ga`, Abbr `tna`] >> disch_tac >>
     drule_all (Q.INST [`i` |-> `al`, `j` |-> `st`] logInstSeqPtrTheory.inst_seq_ptr_pair) >>
     simp[]) >>
  `run_inst_seq_mem_ok [al;st] s` by
    (simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last] >>
     simp[Abbr `al`, Abbr `st`, venomInstTheory.mk_inst_def,
          memSafeRunTheory.inst_dload_in_section_other,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
         ~is_terminator i.inst_opcode) [al;st]` by
    simp[Abbr `al`, Abbr `st`, venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def] >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)` by
    (qx_gen_tac `H` >> disch_tac >> simp[NoAsms, Abbr `t`] >>
     irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`[al;st]`,`sa`] >> simp[] >>
     rpt strip_tac >>
     `MEM i [al;st]` by (pure_asm_rewrite_tac[] >> simp[MEM_APPEND]) >>
     qpat_x_assum `MEM i [al;st]` (strip_assume_tac o REWRITE_RULE [MEM]) >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     asm_rewrite_tac [] >> simp[NoAsms, Abbr `al`, Abbr `st`, venomInstTheory.mk_inst_def]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history fn t` by
    (simp[NoAsms, Abbr `t`] >> irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`[al;st]`,`s`,`sa`] >>
     simp[Abbr `al`, Abbr `st`, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]) >>
  suspend "store_effect"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[store_effect]:
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                         vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s`
       mp_tac >> simp[venomStateTheory.venom_state_component_equality]) >>
  `t.vs_alloca_next = u.vs_alloca_next /\ t.vs_allocas = u.vs_allocas /\
   t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
   t.vs_memory = m.vs_memory /\ (!p. lookup_var p t = lookup_var p u)` by
    simp[Abbr `t`, Abbr `m`, venomStateTheory.mstore_def,
         venomStateTheory.lookup_var_def] >>
  `Gf = Ga /\ tnf.t_var = tna.t_var /\
   tnf.t_mem = tna.t_mem DIFF {i | cell <= i /\ i < cell+32}` by
    (simp[NoAsms, Abbr `Gf`, Abbr `tnf`, Abbr `st`, Abbr `m`] >>
     qpat_assum `w2n (n2w cell:256 word) = cell` (fn cell_eq =>
       let
         val frame = SIMP_RULE (srw_ss())
           [cell_eq, venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]
           (Q.INST [`a` |-> `n2w cell:256 word`, `value` |-> `Lit 0w`, `w` |-> `0w`]
             bodyPtrMakeArrayCopyStepTheory.mstore_raw_ghost_frame)
       in
         (conj_tac >- (irule (cj 1 frame) >> simp[])) >>
         (conj_tac >- (irule (cj 2 frame) >> simp[])) >>
         irule (cj 6 frame) >> simp[]
       end)) >>
  `tnf.t_stor = tna.t_stor /\ tnf.t_trans = tna.t_trans /\ tnf.t_imm = tna.t_imm` by
    (simp[NoAsms, Abbr `tnf`] >>
     irule step_taint_nonmemory_frame >> simp[Abbr `st`, venomInstTheory.mk_inst_def]) >>
  `abi_decode_guarded_effect_core u tna t tnf` by
    simp[abi_decode_guarded_effect_core_def, pred_setTheory.IN_DIFF] >>
  `abi_decode_guarded_effect_core s tn t tnf` by
    (drule_all abi_decode_guarded_effect_compose_core >> simp[]) >>
  `!p. op_taint tnf (Var p) = op_taint tna (Var p)` by
    simp[ptrDisciplineTheory.op_taint_def] >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> `x <> counter` by metis_tac[] >> simp[]) >>
  `!p k. p <> counter /\ ptr_covers G tn p s k ==> ptr_covers Gf tnf p t k` by
    (rpt gen_tac >> strip_tac >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `ptr_covers Gf tnf counter t 32` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`Ga`,`u`,`tna`] >> simp[]) >>
  suspend "resources"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[resources]:
  `!a k. a+k <= cell \/ cell+32 <= a ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt gen_tac >> disch_tac >> simp[] >>
     irule EQ_TRANS >> qexists_tac `mem_bytes_at a k u.vs_memory` >>
     (conj_tac >- (simp[NoAsms, Abbr `m`] >>
                   irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[])) >>
     simp[]) >>
  `!name b k. local_region ce es.scopes t name b k <=>
             local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  `(^scratch_input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`sa`] >> simp[]) >>
  `sa.cs_next_var <= loop_st.cs_next_var` by
    (drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> simp[]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
     ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
     ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
     abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. V H ==> abi_decode_ptr_write_frame _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     (conj_tac >- simp[Abbr `t`, exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
     (conj_tac >- simp[Abbr `t`, ghostPcTransportPtrTheory.ghost_inv_at_inst_idx]) >>
     (conj_tac >- simp[]) >>
     irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qexistsl_tac [`Gf`,`m`,`tnf`] >>
     simp[NoAsms, Abbr `t`, venomStateTheory.lookup_var_def] >> simp[]) >>
  suspend "live"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[live]:
  `!aid p b k bytes. MEM (aid,p,b,k,bytes) live ==>
      aid <> sa.cs_next_id /\ (b+k <= cell \/ cell+32 <= b)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) live`
       (qspec_then `(aid,p,b,k,bytes)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[] >> strip_tac >>
     `aid <> sa.cs_next_id` by decide_tac >> simp[] >>
     `FLOOKUP u.vs_allocas aid = SOME (b,k)` by simp[] >>
     qpat_assum `alloca_inv u` (mp_tac o REWRITE_RULE
       [venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`,`sa.cs_next_id`,`b`,`k`,`cell`,`32`] mp_tac o CONJUNCT1) >>
     simp[]) >>
  `EVERY (\(aid,p,b,k,bytes). aid <> sa.cs_next_id /\
      (b+k <= cell \/ cell+32 <= b)) live` by
    (simp[NoAsms, EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_assum `!aid p b k bytes. MEM (aid,p,b,k,bytes) live ==> _`
       (qspecl_then [`e0`,`e1`,`e2`,`e3`,`e4`] mp_tac) >> simp[]) >>
  `EVERY (\(aid,p,b,k,bytes).
      aid < loop_st.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) /\
      lookup_var p t = SOME (n2w b) /\ ptr_covers Gf tnf p t k /\
      op_taint tnf (Var p) = {} /\ k = LENGTH bytes /\
      mem_bytes_at b k t.vs_memory = bytes /\ b+k <= t.vs_alloca_next) live` by
    (simp[NoAsms, EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) live`
       (qspec_then `(e0,e1,e2,e3,e4)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). not_fresh_at sa p) live`
       (qspec_then `(e0,e1,e2,e3,e4)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[NoAsms] >>
     disch_then (drule_then assume_tac) >>
     disch_then (drule_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
     `e1 <> counter` by metis_tac[] >>
     `ptr_covers Gf tnf e1 t e3` by metis_tac[] >>
     `e2+e3 <= cell \/ cell+32 <= e2` by metis_tac[] >>
     `mem_bytes_at e2 e3 t.vs_memory = e4` by metis_tac[] >>
     `e0 < loop_st.cs_next_id /\ e2+e3 <= t.vs_alloca_next` by decide_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `e1` mp_tac) >> simp[]) >>
  suspend "finish"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[finish]:
  `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes)
         protected` by
    (simp[NoAsms, EVERY_MEM] >> gen_tac >> disch_tac >> PairCases_on `e` >>
     qpat_assum `EVERY (\(a,bytes). mem_bytes_at a _ _ = bytes) protected`
       (qspec_then `(e0,e1)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ _) protected`
       (qspec_then `(e0,e1)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[] >> metis_tac[]) >>
  `mem_word_at cell t.vs_memory = 0w` by
    simp[Abbr `m`, valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
       i IN tn.t_mem` by
    (gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     `i IN tna.t_mem` by
       (qpat_assum `i IN tnf.t_mem` mp_tac >>
        qpat_assum `tnf.t_mem = _` (fn th =>
          simp[NoAsms, th, pred_setTheory.IN_DIFF])) >>
     `~(cell <= i /\ i < cell+32)` by decide_tac >>
     qpat_assum `!j. ~(cell <= j /\ j < cell+32) ==> (j IN tna.t_mem <=> _)`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `op_taint tnf (Var counter) = {}` by
    (qpat_assum `ptr_covers Gf tnf counter t 32` mp_tac >>
     simp[NoAsms, bodyPtrDefsTheory.ptr_covers_def]) >>
  `!i. cell <= i /\ i < cell+32 ==> i NOTIN tnf.t_mem` by
    (qpat_assum `tnf.t_mem = _` (fn th => simp[NoAsms, th, pred_setTheory.IN_DIFF])) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]) (fn_insts fn)` by
    (qpat_assum `MEM al (fn_insts fn)` mp_tac >> simp[NoAsms, Abbr `al`]) >>
  qpat_assum `(^scratch_input_origin) t` (assume_tac o BETA_RULE) >>
  suspend "owned"
QED

Resume abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods[owned]:
  `abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes)` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `eval_operand (Var input) t = SOME input_word` by
    (qpat_assum `abi_decode_ptr_window Gf tnf t input input_word _` mp_tac >>
     simp[NoAsms, abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
          venomStateTheory.eval_operand_def]) >>
  `mem_bytes_at (w2n input_word) (LENGTH input_bytes) t.vs_memory = input_bytes` by
    (qpat_assum `!a k. a+k <= cell \/ cell+32 <= a ==> _`
       (qspecl_then [`w2n input_word`,`LENGTH input_bytes`] mp_tac) >> simp[]) >>
  `output <> counter` by metis_tac[] >>
  `ptr_covers Gf tnf output t output_cap` by
    (qpat_assum `!p k. p <> counter /\ ptr_covers G tn p s k ==> _`
       (qspecl_then [`output`,`output_cap`] mp_tac) >> simp[]) >>
  `lookup_var output t = SOME (n2w output_base)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `output` mp_tac) >> simp[]) >>
  `FLOOKUP t.vs_allocas output_id = SOME (output_base,output_cap)` by simp[] >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   w2n input_word+LENGTH input_bytes <= t.vs_alloca_next /\
   output_id < loop_st.cs_next_id /\ origin.cs_next_var <= loop_st.cs_next_var` by
    decide_tac >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= t.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     `off+sz <= s.vs_alloca_next` by
       (qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
     decide_tac) >>
  `!name b sz. local_region ce es0.scopes s0 name b sz ==> b+sz <= t.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >>
     `b+sz <= s.vs_alloca_next` by
       (qpat_assum `!name b sz. local_region ce es0.scopes s0 name b sz ==> _`
          (qspecl_then [`name`,`b`,`sz`] mp_tac) >> simp[]) >>
     decide_tac) >>
  `not_fresh_at loop_st output /\
    EVERY (\(aid,p,b,k,bytes). not_fresh_at loop_st p) live` by
    ((conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     simp[NoAsms, EVERY_MEM] >> gen_tac >> disch_tac >> PairCases_on `e` >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). not_fresh_at sa p) live`
       (qspec_then `(e0,e1,e2,e3,e4)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[NoAsms] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`,`counter`,`cell`,`w2n input_word`] >>
  asm_rewrite_tac [n2w_w2n]
QED

Finalise abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods
