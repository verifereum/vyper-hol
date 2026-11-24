(* Count the payload copy, length increment and final header store from
   the actual nonstatic placed endpoint.  The sparse copy may be empty. *)
Theory bodyAppendSlotStoreTailMods
Ancestors
  bodyFullStoreSlotsPath bodyFullStoreSlotsAddresses bodyFullStoreSlotsFrame
  bodyFullStoreSlotsTaintStore bodySlotCopyFieldsMods stmtLoweringMono
  exprOperandVar placeStoreSlots fragGasOriginPtrLoop emitHelperProps
  lowerDloadMaskedStorage valueEncodingProps typedMemoryCopy typedCopyOriginPtrBase
  venomState ptrDiscipline exprLoweringProps stmtSimStoreCopy finite_map words

Theorem append_slot_operand_frame[local]:
  eval_operand op s = SOME w /\ op_taint ts op = {} /\
  t.vs_labels = s.vs_labels /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x s /\
                      op_taint tt (Var x) = op_taint ts (Var x)) ==>
  eval_operand op t = SOME w /\ op_taint tt op = {}
Proof
  Cases_on `op` >> simp[eval_operand_def,op_taint_def]
QED

Theorem append_slot_normalize_pc[local]:
  store_copy_normalize s (t with vs_inst_idx := pc) = store_copy_normalize s t
Proof
  simp[store_copy_normalize_def]
QED

Theorem append_slot_store_tail_mods:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv elem = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst elem tr sa = ((),sb) /\
  emit_op ADD [lop; Lit 1w] sb = (nop,sc) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sc = ((),sf) /\
  (!x. src = Var x \/ dst = Var x \/ lop = Var x \/ bop = Var x ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME k /\
  eval_operand lop s = SOME (n2w len) /\ eval_operand bop s = SOME slot /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  op_taint tn lop = {} /\ op_taint tn bop = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func /\
  fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ks u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    store_copy_normalize s u =
      (if tr then tstore else sstore) slot (n2w (len+1))
        (FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
          (mem_word_at (w2n sw+32*i) s.vs_memory) q) s ks) /\
    (if tr then tf.t_trans else tf.t_stor) SUBSET
      key_update
        (FOLDL (\X i. key_update X (k+n2w i) (mem_word_taint tn.t_mem (w2n sw+32*i)))
          (if tr then tn.t_trans else tn.t_stor) ks) slot {} /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_data_section = s.vs_data_section /\
    u.vs_immutables = s.vs_immutables /\
    allocas_from lo u /\ (allocas_below_fmp u <=> allocas_below_fmp s) /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!x. not_fresh_at sa x ==> not_fresh_at sf x /\
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  drule_all compile_store_slots_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`stored`,`ks`,`Gk`,`tk`] strip_assume_tac)) >>
  `allocas_from lo stored` by
    (pure_asm_rewrite_tac[allocas_from_def] >> fs[allocas_from_def]) >>
  `allocas_below_fmp stored <=> allocas_below_fmp s` by
    (drule store_slots_normalize_allocas_below_fmp >>
     simp[store_slots_fold_allocas_below_fmp]) >>
  `ci_mono sa sb` by metis_tac[cj 1 ci_mono_compile_store_slots,pairTheory.SND] >>
  `ci_mono sb sc` by metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono sc sf` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\ not_fresh_at sf x` by
    metis_tac[ci_mono_trans,compiler_ci_mono_not_fresh] >>
  suspend "increment"
QED

Resume append_slot_store_tail_mods[increment]:
  `eval_operand lop stored = SOME (n2w len) /\ op_taint tk lop = {}` by
    (irule append_slot_operand_frame >> qexistsl_tac [`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `eval_operand (Lit 1w) stored = SOME 1w /\ op_taint tk (Lit 1w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp stored)` by fs[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gk`] (qx_choose_then `out` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK (counted:venom_state),_,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK counted,Gc,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK counted,Gc,tc)` >>
  `counted.vs_labels = stored.vs_labels /\ counted.vs_call_ctx = stored.vs_call_ctx /\
   allocas_from lo counted /\ ~counted.vs_halted /\
   counted.vs_current_bb = sc.cs_current_bb /\ counted.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `allocas_from lo stored` mp_tac >>
     simp[Abbr `counted`,update_var_def,allocas_from_def] >> fs[allocas_from_def]) >>
  suspend "header"
QED

Resume append_slot_store_tail_mods[header]:
  `eval_operand bop counted = SOME slot /\ op_taint tc bop = {}` by
    (irule append_slot_operand_frame >> qexistsl_tac [`s`,`tn`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `allocas_below_fmp counted <=> allocas_below_fmp stored` by
    simp[Abbr `counted`,allocas_below_fmp_def,update_var_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp counted)` by fs[] >>
  `eval_operand nop counted = SOME (n2w (len+1))` by
    simp[Abbr `counted`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,GSYM word_add_n2w] >>
  `~counted.vs_call_ctx.cc_static` by simp[] >>
  drule_all storage_tainted_word_store_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gc`] assume_tac) >>
  qabbrev_tac `u = ((if tr then tstore else sstore) slot (n2w (len+1)) counted)
    with vs_inst_idx := LENGTH sf.cs_current_insts` >>
  qabbrev_tac `tf = if tr then tc with t_trans := key_update tc.t_trans slot {}
    else tc with t_stor := key_update tc.t_stor slot {}` >>
  qexistsl_tac [`ks`,`u`,`Gc`,`tf`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "normalize" >>
  conj_tac >- suspend "taint" >>
  suspend "fields"
QED

Resume append_slot_store_tail_mods[path]:
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gk`,`stored`,`tk`] >> simp[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gc`,`counted`,`tc`] >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (counted,Gc,tc) [] _` (qspec_then `D` mp_tac) >>
  Cases_on `tr` >> simp[Abbr `u`,Abbr `tf`]
QED

Resume append_slot_store_tail_mods[normalize]:
  `store_copy_normalize s counted = store_copy_normalize s stored` by
    simp[Abbr `counted`,store_copy_normalize_def,update_var_def] >>
  qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pure_rewrite_tac[append_slot_normalize_pc,store_slots_normalize_store,mem_word_at_eq_mload] >>
  simp[]
QED

Resume append_slot_store_tail_mods[taint]:
  Cases_on `tr` >> fs[Abbr `tf`] >> irule ld_key_update_mono >> simp[]
QED

Resume append_slot_store_tail_mods[fields]:
  `stored.vs_data_section = s.vs_data_section /\ stored.vs_immutables = s.vs_immutables` by
    (irule (Q.INST [`key` |-> `\j. k + n2w j`, `rd` |-> `\j. mload (w2n (sw:bytes32) + 32*j) s`]
       slot_copy_normalized_fields) >> qexistsl_tac [`k`,`ks`,`sw`,`tr`] >> simp[]) >>
  `sf.cs_current_bb = sc.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `allocas_below_fmp u <=> allocas_below_fmp counted` by
    (Cases_on `tr` >> simp[NoAsms,Abbr `u`,allocas_below_fmp_def,sstore_def,tstore_def]) >>
  `allocas_from lo u <=> allocas_from lo counted` by
    (Cases_on `tr` >> simp[NoAsms,Abbr `u`,allocas_from_def,sstore_def,tstore_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_data_section = s.vs_data_section /\
   u.vs_immutables = s.vs_immutables` by
    (Cases_on `tr` >> simp[Abbr `u`,Abbr `counted`,sstore_def,tstore_def,update_var_def]) >>
  `!x. lookup_var x u = lookup_var x counted /\ op_taint tf (Var x) = op_taint tc (Var x)` by
    (Cases_on `tr` >> simp[Abbr `u`,Abbr `tf`,sstore_def,tstore_def,lookup_var_def,op_taint_def]) >>
  `u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
   u.vs_current_bb = sf.cs_current_bb /\ u.vs_inst_idx = LENGTH sf.cs_current_insts` by
    (Cases_on `tr` >> simp[Abbr `u`,sstore_def,tstore_def]) >>
  `tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
   (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans)` by
    (qpat_x_assum `if tr then tk.t_stor = _ else tk.t_trans = _` mp_tac >>
     Cases_on `tr` >> simp[Abbr `tf`]) >>
  `allocas_below_fmp u <=> allocas_below_fmp s` by metis_tac[] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb x /\ _`
    (qspec_then `x` (strip_assume_tac o SRULE [])) >>
  qpat_assum `!x. not_fresh_at sa x ==> lookup_var x stored = _ /\ _`
    (qspec_then `x` (strip_assume_tac o SRULE [])) >>
  qpat_assum `!p. not_fresh_at sb p ==> p <> out /\ _`
    (qspec_then `x` (strip_assume_tac o SRULE [])) >>
  simp[]
QED

Finalise append_slot_store_tail_mods
