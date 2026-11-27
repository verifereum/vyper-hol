Theory bodyAbiDecodeGuardedMemberDestinationMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeFiniteObserved
  abiDecodePtrBytesTail instSeqPtrLo fragGasOriginPtrLoop fragGasPath
  emitHelperProps exprLoweringProps loweringShapeRules stateFrame fragExecMem
  venomInst venomState words list rich_list finite_map

(* Use the same owned state packet as the checked relative-load boundary. *)
local
  val (_,post) = dest_imp (concl abi_decode_owned_relative_load_exact)
  val (_,body) = strip_exists post
in
  val owned_decoder_state = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) body))
end

(* ADD advances the covered output pointer without changing any memory or
   non-variable taint. Replay both paths on the selected ADD successor. *)
Theorem destination_add_observed[local]:
  emit_op ADD [Var dst;pos] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ptr_covers Gf tnf out t k /\ lookup_var out t = SOME (b+n2w q) /\
    FLOOKUP Gf out = FLOOKUP G dst /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all (abi_decode_ptr_output_address |> Q.INST [`D` |-> `ARB`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_covers Gf tnf out u k` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `FLOOKUP Gf out = FLOOKUP G dst` by
    (qpat_x_assum `ptr_covers G tn dst s cap` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> strip_tac >>
     simp[Abbr `Gf`, ptrDisciplineTheory.step_prov_def,
          ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
          ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
          mk_inst_def, FLOOKUP_UPDATE]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
     drule_all abi_decode_ptr_output_address >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
     simp[Abbr `Gf`, Abbr `tnf`]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_emit_op] >>
  `sb.cs_current_bb = sa.cs_current_bb` by (drule emit_op_facts >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[run_inst_seq_mem_ok_def, instMemFrontierTheory.below_frontier_no_ranges,
          mk_inst_def] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
     emitted_insts sa sb = pre ++ i::post /\
     run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by
       (qpat_assum `emitted_insts sa sb = pre ++ i::post`
          (fn th => pure_rewrite_tac[th]) >> simp[MEM_APPEND]) >>
     gvs[mk_inst_def]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  conj_tac >-
    (`t = (u with vs_inst_idx := s.vs_inst_idx) with
           vs_inst_idx := LENGTH sb.cs_current_insts` by simp[Abbr `t`] >>
     pop_assum (fn th => pure_once_rewrite_tac[th]) >>
     rpt strip_tac >> irule abi_decode_finite_success_observed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  reverse conj_tac >-
    (`t = u` by simp[Abbr `t`, Abbr `u`] >>
     asm_rewrite_tac[] >> simp[Abbr `u`, update_var_def]) >>
  gen_tac >>
  qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  simp[Abbr `t`, Abbr `u`]
QED

(* Keep the frontier and taint effects on the same owned result tuple. *)
Theorem abi_decode_member_destination_owned_effect_mods:
  !dst pos sa out sb G tn s cap b q ctx k fn lo explicit PG
   s0 input input_word input_bytes output_id output_base output_cap output
   origin ce es0 live protected V cx es DF delta G0 tn0.
  emit_op ADD [Var dst;pos] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ptr_covers Gf tnf out t k /\ lookup_var out t = SOME (b+n2w q) /\
    FLOOKUP Gf out = FLOOKUP G dst /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    tnf.t_mem = tn.t_mem /\ t.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    abi_decode_guarded_effect_core s tn t tnf
Proof
  rpt gen_tac >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all destination_add_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule emit_op_facts >> strip_tac >>
  `sa.cs_next_id <= sb.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[]) >>
  `(^owned_decoder_state) sb t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >>
     simp[] >> metis_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  asm_rewrite_tac[] >> simp[abi_decode_guarded_effect_core_def]
QED
