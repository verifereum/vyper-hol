Theory bodyAbiDecodeBulkCopyGhostMods
Ancestors
  bodyFullAbiDecodeOwnedCopyEffect[qualified]
  bodyFullAbiDecodeCopyFrame typedCopyOriginPtrDynArray
  bodyFullGhostFrame abiDecodePtrMemberFrame allocaHistory bodyPtrDefs
  loweringStateRelDefs stateRelProj codegenRel freshWrites stateFrame
  exprLoweringProps emitHelperProps emitHelper compileEnv venomState
  venomExecSemantics venomInst ptrDiscipline ptrSafeRun memSafeRun
  unitTransformDefs contextCodegenRel memLocDefs
  words arithmetic list rich_list finite_map pred_set pair
  bodyFullAbiDecodeRelativeLoadExact[qualified]

local
  val old = concl (BETA_RULE
    bodyFullAbiDecodeOwnedCopyEffectTheory.abi_decode_owned_mcopy_joint_effect)
  val (pre,post) = dest_imp old
  val (ws as [_,_,tnf],body) = strip_exists post
  val tn = valOf (List.find (fn v => fst (dest_var v) = "tn") (free_vars pre))
  val fields = ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
    ^tnf.t_imm = ^tn.t_imm``
  val tm = mk_imp (pre,list_mk_exists (ws,mk_conj (body,fields)))
in
  val copy_all = list_mk_forall (free_vars old,tm)
end

(* Select the physical copy and its transfer ghosts together, before advancing
   the instruction cursor. The added taint fields are from that very transfer. *)
Theorem abi_decode_owned_mcopy_joint_exact_effect_mods:
  ^copy_all
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?inst. MEM inst (fn_insts fn) /\ _`
    (qx_choose_then `inst` strip_assume_tac) >>
  `local_ptrs_rel fn ce es.scopes s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `eval_operand (Var dst) s = SOME (n2w b) /\
   eval_operand (Var src) s = SOME (n2w a)` by simp[eval_operand_def] >>
  `EVERY (\(aid,p,base,k,bytes).
    FLOOKUP s.vs_allocas aid = SOME (base,k) /\
    lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at base k s.vs_memory = bytes /\ base+k <= s.vs_alloca_next /\
    (base+k <= b \/ b+n <= base)) live` by
    (gvs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >>
  `EVERY (\(base,bytes). mem_bytes_at base (LENGTH bytes) s.vs_memory = bytes /\
    (base+LENGTH bytes <= b \/ b+n <= base)) protected` by
    (gvs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >>
  `lo <= b` by decide_tac >>
  mp_tac (abi_decode_mcopy_frame_joint |>
    Q.INST [`dst` |-> `Var dest`, `src` |-> `Var source`] |>
    Q.INST [`dest` |-> `dst`, `source` |-> `src`, `id` |-> `sa.cs_next_id`] |>
    Q.INST [`ob` |-> `output_base`, `cap` |-> `output_cap`, `iw` |-> `input_word`]) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    first_x_assum (drule_then ACCEPT_TAC))) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "edge"
QED

Resume abi_decode_owned_mcopy_joint_exact_effect_mods[edge]:
  qabbrev_tac `copy_inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []` >>
  `emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb)` by
    gvs[emit_void_def,emit_inst_def] >>
  `step_inst_base copy_inst s = OK u` by
    simp[Abbr `copy_inst`,Once step_inst_base_def,mk_inst_def,
         eval_operand_def,w2n_n2w,LESS_MOD] >>
  `inst_mem_below_frontier copy_inst s /\ inst_dload_in_section copy_inst s` by
    simp[Abbr `copy_inst`,inst_mem_below_frontier_def,inst_dload_in_section_def,
         mk_inst_def,source_memory_read_ranges_def,source_memory_write_ranges_def,
         sized_source_write_range_def,eval_operand_def,w2n_n2w,LESS_MOD] >>
  `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn copy_inst s` by
    (gen_tac >>
     `step_inst 0 ctx copy_inst s = OK u` by
       (qpat_assum `step_inst_base copy_inst s = _` (SUBST1_TAC o SYM) >>
        simp[step_inst_non_invoke,Abbr `copy_inst`,mk_inst_def]) >>
     simp[ptr_inst_ok_def,mcopy_def,write_memory_with_expansion_def] >> rpt conj_tac
     >- (simp[Abbr `copy_inst`,access_ok_def,mk_inst_def,
             source_memory_write_ranges_def,fixed_source_write_range_def,
             source_memory_read_ranges_def,sized_source_write_range_def,
             eval_operand_def,mem_write_ops_def,mem_read_ops_def] >>
         rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[])
     >- (simp[Abbr `copy_inst`,taint_ok_def,mk_inst_def,
             source_memory_read_ranges_def,sized_source_write_range_def,
             eval_operand_def,w2n_n2w,LESS_MOD] >>
         rpt strip_tac >>
         Cases_on `op = Var dst` >- gvs[ptr_covers_def] >>
         Cases_on `op = Var src` >- gvs[ptr_covers_def] >>
         Cases_on `op = count_op` >> gvs[op_taint_def])) >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >>
     qpat_assum `Gf = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_assum `tnf = step_taint _ _ _ _` SUBST1_TAC >>
     qunabbrev_tac `t` >> qunabbrev_tac `copy_inst` >>
     irule typed_copy_emit_inst_origin_ptr_path >> simp[is_terminator_def]) >>
  suspend "endpoint"
QED

Resume abi_decode_owned_mcopy_joint_exact_effect_mods[endpoint]:
  drule emit_inst_extends >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas` by
    simp[Abbr `t`,mcopy_def,write_memory_with_expansion_def] >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[Abbr `copy_inst`,mk_inst_def,IS_PREFIX_APPEND]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (ho_match_mp_tac (bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_scalar_joint_frame_lower |>
       Q.INST [`s` |-> `u`,`G` |-> `Gf`,`tn` |-> `tnf`]) >>
     simp[Abbr `t`,state_frame_def,lookup_var_def,mcopy_def,write_memory_with_expansion_def] >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _` mp_tac >>
     simp[mcopy_def,write_memory_with_expansion_def] >> metis_tac[]) >>
  `!p. lookup_var p t = lookup_var p u` by
    simp[Abbr `t`,lookup_var_def,mcopy_def,write_memory_with_expansion_def] >>
  `!p k. ptr_covers Gf tnf p t k = ptr_covers Gf tnf p u k` by
    simp[ptr_covers_def,Abbr `t`,lookup_var_def,mcopy_def,write_memory_with_expansion_def] >>
  `t.vs_alloca_next = u.vs_alloca_next /\ t.vs_memory = u.vs_memory` by simp[Abbr `t`] >>
  `!name base k. local_region ce es.scopes t name base k =
     local_region ce es.scopes s name base k` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     simp[Abbr `t`,lookup_var_def,mcopy_def,write_memory_with_expansion_def]) >>
  `abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes)` by
    (gvs[abi_decode_ptr_window_def] >> simp[abi_decode_ptr_window_def] >> metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  `!p. not_fresh_at sb p = not_fresh_at sa p` by simp[not_fresh_at_def] >>
  asm_rewrite_tac[] >> simp[Abbr `t`] >>
  gvs[EVERY_MEM,FORALL_PROD] >>
  (conj_tac >- (rpt gen_tac >> disch_tac >>
    qpat_assum `!aid p base k bytes. MEM (aid,p,base,k,bytes) live ==> aid < sa.cs_next_id /\ _` drule >>
    qpat_assum `!aid p base k bytes. MEM (aid,p,base,k,bytes) live ==> FLOOKUP s.vs_allocas aid = _ /\ _` drule >>
    simp[] >> rpt strip_tac >> simp[] >> decide_tac) >>
   qexists_tac `inst` >> simp[])
QED

Finalise abi_decode_owned_mcopy_joint_exact_effect_mods
