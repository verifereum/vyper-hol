(* Connect the head guard and member navigation to the mixed-prefix decoder. *)
Theory abiDecodeRejectMemberTable
Ancestors
  abiDecodeRejectMemberOffset abiDecodeRejectMemberSetup abiDecodeRejectMemberPrefix
  abiMalformedAggregateFirstBadChild abiDecoderComplexExecute abiMalformedBoundedContract
  abiMalformedRecursiveInterface abiMalformedMemberSetup abiDecoderReentry
  stateRelProj venomMemDefs loweringStateRelDefs bodyPtrBopScalarSeq
  bodyPtrSignedConvertSourceFrame abiDecodePtrMemberFrame decoderGhostFramePtr
  bodyFullPathHistory exprSimAbiDecodeCompositePrefix exprLoweringProps
  ptrDiscipline compileEnv fragExec fragGasOriginPtr venomState
  abiDecoderComplexGuard abiDecoderComplexHead abiEncoder abiDecoderMemberInfos abiDecoderMembers
  abiValidAllocatedContract abiDecoderCoherence abiVyperAdmissible vyperABIValid
  vyperABI contractABI valueEncodingTyping vyperTypeSystem vyperValue
  emitHelper emitHelperProps valueEncodingProps abiMalformedBoundedParents
  bodyPtrSubscriptMemoryRebuild abiCallerAbiShape
  finite_map pred_set list rich_list arithmetic words

val worlds = ``\s t. t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables``;
val path = ``\s G tn out H z. !D explicit.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (out,H,z)``;
val abort = ``\s G tn. ?u H z. (^worlds) s u /\ (^path) s G tn (Abort Revert_abort u) H z``;
val pc = ``\st s. fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts``;
val ghosts = ``\p x k s G tn. abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn x s k /\ op_prov G p = NONE /\ op_prov G hi = NONE /\
  op_taint tn p = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s``;
val entry = ``\st en p x q a k s.
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi p (Var x) B L xs q a k s``;
val old_live = ``\st (G:string |-> num # num) tn H z. !x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
  FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)``;
val source_pos = ``\ty ao. b + (if dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty)
  then abi_head_word (DROP (b+ao) (xs:word8 list)) else ao)``;
val setup_cut = ``!ty ao vo st mid child en ops s G tn.
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi
    (dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty)) ao vo st = (ops,mid) /\
  fn_has_code st mid func /\ cs_extends st mid /\
  st.cs_next_id < mid.cs_next_id /\ mid.cs_next_id <= child.cs_next_id /\
  child.cs_next_id <= en.cs_next_id /\ mid.cs_next_var <= ceiling.cs_next_var /\
  (^entry) st en pos output b d outsz s /\ (^pc) st s /\
  (^ghosts) pos output outsz s G tn /\ vo + type_memory_bytes ce ty <= outsz /\
  (if dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty) then b+ao+32 <= L
   else b+ao <= L) ==>
  (^abort) s G tn \/
  ?r H z x. SND ops = Var x /\
    (^entry) mid child (FST ops) x ((^source_pos) ty ao) (d+vo) (type_memory_bytes ce ty) r /\
    (^pc) mid r /\ (^ghosts) (FST ops) x (type_memory_bytes ce ty) r H z /\
    (^worlds) s r /\ (^path) s G tn (OK r) H z /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s r /\ (^old_live) st G tn H z``;

val scalar_abort = ``!R A code C G tn ctx lo s func bb t PG.
  bop_scalar_seq R A code C /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = Abort Revert_abort t ==>
  ?u H z. u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (^path) s G tn (Abort Revert_abort u) H z``;

Theorem malformed_table_setup_for_prefix[local]:
  (^scalar_abort) ==> (^setup_cut)
Proof
  simp_tac bool_ss [] >>
  disch_then (mk_asm "scalar") >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `abi_decode_member_setup _ _ _ _ _ dyn _ _ _` >>
  `b+ao+(if dyn then 32 else 0) <= L` by (Cases_on `dyn` >> fs[]) >>
  `hi <> Lit 0w /\ eval_operand pos s = SOME (n2w b) /\
   abi_malformed_allocated_window live B L xs s /\
   abi_decoder_operand_live st.cs_next_var pos /\ not_fresh_at st source /\
   stmt_state_rel H0 ctx func cenv cx es s` by
    fs[abi_malformed_entry_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >>
     fs[stmt_state_rel_def, fmp_room_def, allocas_below_fmp_def,
        alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  `B+L <= s.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     fs[abi_malformed_allocated_window_def, alloca_inv_def, alloca_next_valid_def] >>
     res_tac >> decide_tac) >>
  `!sm op. dyn /\ compile_getelemptr_abi pos T ao MLOAD (Var source) hi st = (op,sm) /\
    fn_has_code st sm func /\ sm.cs_next_var <= ceiling.cs_next_var ==>
    (?r H z. r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
      r.vs_immutables = s.vs_immutables /\ r.vs_call_ctx = s.vs_call_ctx /\
      (^path) s G tn (Abort Revert_abort r) H z) \/
    (b + abi_head_word (DROP (b+ao) xs) < dimword (:256) /\
     ?r H z. eval_operand op r = SOME (n2w (b + abi_head_word (DROP (b+ao) xs))) /\
      op_taint z op = {} /\ op_prov H op = NONE /\
      r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH sm.cs_current_insts|> /\
      fresh_vars_wrt ceiling r /\
      z.t_mem = tn.t_mem /\ z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==> lookup_var x r = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)) /\
      (^path) s G tn (OK r) H z)` by (
    (rpt gen_tac >> strip_tac >>
    `b+ao+32 <= L` by fs[] >>
    asm "scalar" assume_tac >>
    drule_all malformed_dynamic_member_offset_cut >>
    simp_tac bool_ss [LET_THM] >>
    disch_then (qspec_then `PG` strip_assume_tac)
    >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
    disj2_tac >> simp[] >> goal_assum (drule_at Any) >>
    simp[venom_state_component_equality] >> (gvs[venom_state_component_equality, malformed_dynamic_member_offset_cut]))) >>
  rule_assum_tac BETA_RULE >>
  drule_all malformed_table_member_setup_cut >>
  disch_then (DISJ_CASES_THEN2 (fn th => disj1_tac >> mp_tac th >> metis_tac[]) strip_assume_tac) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  simp_tac bool_ss [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `abi_malformed_scratch_sites mid child func SUBSET abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  simp_tac bool_ss [GSYM not_fresh_at_def] >>
  fs[abi_malformed_entry_def, SUBSET_DEF] >> metis_tac[]
QED

(* The scalar head cut is supplied by FirstFailure, without importing it. *)
val head_cut = ``!pos hi k st sh p L s G tn ctx func ceiling lo PG.
  abi_decode_complex_head_guard pos hi k st = ((),sh) /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  p < dimword(:256) /\ k < dimword(:256) /\ L < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  sh.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code st sh func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  if p+k <= L then
    ?u H z.
      u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sh.cs_current_insts|> /\
      fresh_vars_wrt ceiling u /\
      (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)) /\
      z.t_mem = tn.t_mem /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,H,z))
  else
    ?u H z.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,H,z))``;

Theorem malformed_table_head_reentry[local]:
  (^entry) st en pos output b d outsz s /\ (^pc) st s /\
  (^ghosts) pos output outsz s G tn /\ fn_inst_ids_distinct func /\
  sh.cs_current_bb = st.cs_current_bb /\ st.cs_next_var <= sh.cs_next_var /\
  st.cs_next_id <= sh.cs_next_id /\
  r = s with <|vs_vars := r.vs_vars; vs_inst_idx := LENGTH sh.cs_current_insts|> /\
  fresh_vars_wrt ceiling r /\
  (!x. not_fresh_at st x ==> lookup_var x r = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)) /\
  z.t_mem = tn.t_mem /\ (^path) s G tn (OK r) H z ==>
  (^entry) sh en pos output b d outsz r /\ (^pc) sh r /\
  (^ghosts) pos output outsz r H z /\ (^worlds) s r
Proof
  simp_tac bool_ss [] >> strip_tac >>
  `r.vs_labels = s.vs_labels /\ r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
   r.vs_alloca_next = s.vs_alloca_next /\ (^pc) sh r /\ (^worlds) s r` by
    (simp[] >> qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
      (fn th => ONCE_REWRITE_TAC[th]) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op r = eval_operand op s /\ op_prov H op = op_prov G op /\
    op_taint z op = op_taint tn op` by
    (namedCases_on `op` ["v", "x", "l"]
     >- simp[eval_operand_def, op_prov_def, op_taint_def]
     >- (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
              GSYM not_fresh_at_def] >> strip_tac >>
         qpat_assum `!x. not_fresh_at st x ==> _` drule >>
         simp[eval_operand_def, op_prov_def]) >>
     simp[eval_operand_def, op_prov_def, op_taint_def]) >>
  rule_assum_tac BETA_RULE >>
  `stmt_state_rel H0 ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [Var source;hi;pos;Var output]` by
    fs[abi_malformed_entry_def] >>
  `stmt_state_rel H0 ctx func cenv cx es r` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`s`,`st`] >> simp[]) >>
  `abi_malformed_scratch_sites sh en func SUBSET abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> simp[]) >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  conj_tac >-
    (gvs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
         abi_malformed_destination_def] >>
     metis_tac[abi_decoder_operand_live_mono, local_ptrs_reserved_next_var, SUBSET_DEF]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history func r` by metis_tac[body_full_path_alloca_history] >>
  fs[allocas_from_def] >> rpt conj_tac
  >- (irule abi_decode_ptr_window_frame >> metis_tac[])
  >- (irule ptr_covers_frame >> metis_tac[]) >>
  metis_tac[]
QED

Theorem malformed_table_head_compile[local]:
  abi_decode_complex_head_guard pos hi k st = ((),sh) ==>
  ci_mono st sh /\ sh.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >> drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  simp[ci_mono_def] >>
  `cs_extends st sh` by
    (irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _` mp_tac >>
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> disch_tac >> gvs[]
QED

val source_view = ``\ty q. if is_dynamic (vyper_to_abi_type env ty) then DROP q (xs:word8 list)
  else TAKE (static_length (vyper_to_abi_type env ty)) (DROP q xs)``;
val malformed_view = ``\ty bytes. ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes))``;
val child_contract = ``\ty. !st en p x q a s G tn.
  compile_abi_decode_to_buf (Var x) p MLOAD (Var source) hi
    (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty) st = ((),en) /\ fn_has_code st en func /\
  (^entry) st en p x q a (type_memory_bytes ce ty) s /\
  (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => q+32 <= L | _ => T) /\
  (^pc) st s /\ en.cs_next_var <= ceiling.cs_next_var /\
  (^malformed_view) ty ((^source_view) ty q) /\
  (^ghosts) p x (type_memory_bytes ce ty) s G tn ==> (^abort) s G tn``;
val valid_child = ``!ty tv v st en p x q a s G tn.
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es st en
    (Var source) hi p (Var x) B L xs q a dstid live ceiling s /\
  (^ghosts) p x (type_memory_bytes ce ty) s G tn ==>
  ?u H z. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      a (type_memory_bytes ce ty) s u /\ (^worlds) s u /\ (^path) s G tn (OK u) H z /\
    ptr_covers H z x u (type_memory_bytes ce ty) /\
    abi_decode_ptr_window H z u source (n2w B) L /\
    (!mem. mem_agree_outside z.t_mem u.vs_memory mem ==> val_in_memory tv v a mem) /\
    (^old_live) st G tn H z /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!k. ~(a <= k /\ k < a+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u k 1 ==>
      (k IN z.t_mem <=> k IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
val head_sum = ``\ts. SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) ts))``;
val dest_sum = ``\ts. SUM (MAP (type_memory_bytes ce) ts)``;
val good_view = ``\ty ao.
  (^source_pos) ty ao <= L /\
  (is_dynamic (vyper_to_abi_type env ty) \/
   (^source_pos) ty ao + static_length (vyper_to_abi_type env ty) <= L) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP ((^source_pos) ty ao) xs) /\
  (?v. abi_to_vyper env ty
         (dec (vyper_to_abi_type env ty) (DROP ((^source_pos) ty ao) xs)) = SOME v)``;
val prefix_members = ``\ts i. !j. j <= i ==>
  (?tv. abi_decoder_coherent ce env sf (EL j ts) tv /\
        assignable_type env (EL j ts) /\
        (?av. has_type (vyper_to_abi_type env (EL j ts)) av) /\
        abi_decode_bytes_widths env (EL j ts) /\
        type_memory_size tv < dimword (:256) /\ abi_size_bound sf (EL j ts) < dimword (:256) /\
        (^child_contract) (EL j ts)) /\
  (^dest_sum) (TAKE j ts) + type_memory_bytes ce (EL j ts) <= outsz /\
  (if j = i then
     (^malformed_view) (EL j ts)
       ((^source_view) (EL j ts) ((^source_pos) (EL j ts) ((^head_sum) (TAKE j ts))))
   else (^good_view) (EL j ts) ((^head_sum) (TAKE j ts)))``;

Theorem malformed_table_head_then_prefix[local]:
  (^head_cut) /\ (^scalar_abort) /\ (^valid_child) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (^entry) st en pos output b d outsz s /\ (^pc) st s /\ (^ghosts) pos output outsz s G tn /\
  en.cs_next_var <= ceiling.cs_next_var /\ fn_has_code st en func /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex dyn (abi_decoder_member_infos sf ce ts)) st = ((),en) /\
  FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce ts) = (^head_sum) ts /\
  (^head_sum) ts < dimword (:256) /\
  (L < b + (^head_sum) ts \/
   ?i. i < LENGTH ts /\ (^prefix_members) ts i) ==>
  (^abort) s G tn
Proof
  simp_tac bool_ss [] >> disch_then (CONJUNCTS_THEN2 (mk_asm "head")
    (fn th => let val cs = CONJUNCTS th in
      MAP_EVERY assume_tac (List.take (cs, length cs - 1)) >>
      mk_asm "scan" (List.last cs) end)) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def]) >>
  qpat_x_assum `FOLDR _ _ _ = _` (fn th => rewrite_tac[th] >> assume_tac th) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_complex_head_guard _ _ k st` >>
  Cases_on `abi_decode_complex_head_guard pos hi k st` >>
  Cases_on `q` >> fs[] >>
  rename1 `abi_decode_complex_head_guard _ _ _ st = ((),sh)` >>
  fs[Abbr `k`] >>
  drule malformed_table_head_compile >> strip_tac >>
  `ci_mono sh en` by
    metis_tac[CONJUNCT1 (CONJUNCT2 ci_mono_compile_abi_decode), pairTheory.SND] >>
  fs[ci_mono_def] >>
  `fn_has_code st sh func /\ fn_has_code sh en func /\ sh.cs_next_var <= ceiling.cs_next_var` by
    metis_tac[fn_has_code_split, LESS_EQ_TRANS] >>
  `hi <> Lit 0w /\ eval_operand pos s = SOME (n2w b) /\
   eval_operand hi s = SOME (n2w L) /\ b < dimword (:256) /\ L < dimword (:256) /\
   abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >> decide_tac) >>
  asm "head" (qspecl_then [`pos`,`hi`,`SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) ts))`,
    `st`,`sh`,`b`,`L`,`s`,`G`,`tn`,`ctx`,`func`,`ceiling`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >>
  Cases_on `b + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) ts)) <= L` >-
    (asm_simp_tac bool_ss [] >>
     disch_then (qx_choose_then `r` (qx_choose_then `H` (qx_choose_then `z`
       (MAP_EVERY assume_tac o CONJUNCTS)))) >>
     `(^entry) sh en pos output b d outsz r /\ (^pc) sh r /\
      (^ghosts) pos output outsz r H z /\ (^worlds) s r` by
       (BETA_TAC >> drule_all (SIMP_RULE bool_ss [] malformed_table_head_reentry) >>
        asm_simp_tac bool_ss []) >>
     rule_assum_tac BETA_RULE >>
     `(^setup_cut)` by
       (BETA_TAC >> mp_tac (SIMP_RULE bool_ss [] malformed_table_setup_for_prefix) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then ACCEPT_TAC) >>
     rule_assum_tac BETA_RULE >>
     `(?i. i < LENGTH ts /\ (^prefix_members) ts i)` by
       (BETA_TAC >> asm "scan" mp_tac >> simp[arithmeticTheory.NOT_LESS]) >>
     rename1 `i < LENGTH ts` >> rule_assum_tac (SIMP_RULE bool_ss [LET_THM]) >>
     `(^abort) r H z` suffices_by
       (BETA_TAC >> disch_then (qx_choose_then `u` (qx_choose_then `Hf`
          (qx_choose_then `zf` strip_assume_tac))) >>
        qexistsl [`u`,`Hf`,`zf`] >>
        conj_tac >- gvs[] >>
        rpt gen_tac >>
        qpat_assum `!D explicit. gas_origin_ptr_path _ (r,H,z) [] _`
          (qspecl_then [`D`,`explicit`] mp_tac) >>
        qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK r,H,z)`
          (qspecl_then [`D`,`explicit`] mp_tac) >>
        rpt (pop_assum kall_tac) >>
        metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
     BETA_TAC >> mp_tac (SIMP_RULE bool_ss [] malformed_table_prefix_reject_joint) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspecl_then [`i`,`ts`,`0`,`0`,`sh`,`en`,`r`,`H`,`z`] mp_tac) >>
     (simp_tac bool_ss [ADD] >> impl_tac >-
       (asm_simp_tac bool_ss [LET_THM] >> simp[])) >> disch_then ACCEPT_TAC) >>
  asm_simp_tac bool_ss [] >> rpt (pop_assum kall_tac) >> metis_tac[]
QED

(* Keep the source scan's ABI slice separate from the compiler's member cursor. *)
val abi_view = ``\a q. if is_dynamic a then DROP q (xs:word8 list)
                         else TAKE (static_length a) (DROP q xs)``;
val abi_ok = ``\e t z. vyper_decode_valid_enc (vyper_to_abi_type e t) z /\
                       abi_vyper_admissible e t (dec (vyper_to_abi_type e t) z)``;
val member_position = ``\ce (f:string |-> (string # type # num) list) b ao t. b +
  (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
   then abi_head_word (DROP (b+ao) xs) else ao)``;
val head_prefix = ``\e ts j. SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type e) (TAKE j ts)))``;
val member_meta = ``\ce e f par ts j.
  abi_decode_bytes_widths e (EL j ts) /\
  (?u. abi_decoder_coherent ce e f (EL j ts) u /\
       type_memory_size u = type_memory_bytes ce (EL j ts)) /\
  abi_size_bound f (EL j ts) < dimword (:256) /\
  SUM (MAP (type_memory_bytes ce) (TAKE j ts)) + type_memory_bytes ce (EL j ts) <=
    type_memory_bytes ce par``;
val member_good = ``\ce e f b ao t.
  (b + ao + abi_member_head_size (vyper_to_abi_type e t) <= LENGTH xs /\
   (^abi_ok) e t
     (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs))) /\
  (^member_position) ce f b ao t <= LENGTH xs /\
  (is_dynamic (vyper_to_abi_type e t) \/
   (^member_position) ce f b ao t + static_length (vyper_to_abi_type e t) <= LENGTH xs) /\
  vyper_decode_valid_enc (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs) /\
  dec (vyper_to_abi_type e t)
    (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)) =
  dec (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs) /\
  (?v. abi_to_vyper e t
         (dec (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs)) = SOME v)``;
val member_bad = ``\ce e f b ao t.
  LENGTH xs < b + ao + abi_member_head_size (vyper_to_abi_type e t) \/
  (b + ao + abi_member_head_size (vyper_to_abi_type e t) <= LENGTH xs /\
   ~(^abi_ok) e t
     (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)) /\
   ~(^abi_ok) e t ((^abi_view) (vyper_to_abi_type e t) ((^member_position) ce f b ao t)) /\
   (dimword (:256) <= (^member_position) ce f b ao t \/
    (LENGTH xs < (^member_position) ce f b ao t /\
     (^member_position) ce f b ao t < dimword (:256)) \/
    (^member_position) ce f b ao t <= LENGTH xs))``;
val source_table = ``\ce e f par b ts.
  0 < LENGTH ts /\ LENGTH ts < dimword (:256) /\
  (LENGTH xs < b + (^head_prefix) e ts (LENGTH ts) \/
   (b + (^head_prefix) e ts (LENGTH ts) <= LENGTH xs /\
    (LENGTH ts < dimword (:256) /\ ?i. i < LENGTH ts /\
     (!j. j < i ==> (^member_meta) ce e f par ts j /\
       (^member_good) ce e f b ((^head_prefix) e ts j) (EL j ts)) /\
     (^member_meta) ce e f par ts i /\
     (^member_bad) ce e f b ((^head_prefix) e ts i) (EL i ts))))``;

val member_reject = ``\ts. !ty tv. MEM ty ts /\
  abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
  assignable_type env ty /\ (?av. has_type (vyper_to_abi_type env ty) av) /\
  type_memory_size tv < dimword (:256) /\ abi_size_bound sf ty < dimword (:256) ==>
  (^child_contract) ty``;

Theorem malformed_table_scan_for_prefix[local]:
  (^source_table) ce env sf par b ts /\ L = LENGTH xs /\
  type_memory_bytes ce par <= outsz /\ outsz < dimword (:256) /\
  EVERY (assignable_type env) ts /\ has_types (vyper_to_abi_types env ts) avs /\
  (^member_reject) ts ==>
  L < b + (^head_sum) ts \/ ?i. i < LENGTH ts /\ (^prefix_members) ts i
Proof
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt, vyper_to_abi_types_MAP,
                   has_types_LIST_REL, LIST_REL_EL_EQN, LENGTH_MAP] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "table")
    (fn th => let val cs = CONJUNCTS th in
      MAP_EVERY assume_tac (List.take (cs, length cs - 1)) >>
      mk_asm "member_reject" (List.last cs) end)) >>
  qpat_x_assum `L = LENGTH xs` SUBST_ALL_TAC >>
  asm "table" (fn th =>
    DISJ_CASES_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `i` (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2
            (MAP_EVERY assume_tac o CONJUNCTS) (mk_asm "bad"))))))) (cj 3 th))
  >- asm_rewrite_tac[] >>
  asm_x "table" kall_tac >>
  disj2_tac >> qexists_tac `i` >>
  conj_tac >- simp[] >>
  qx_gen_tac `j` >> disch_tac >>
  `j < LENGTH ts` by decide_tac >>
  `MEM (EL j ts) ts` by simp[EL_MEM] >>
  `assignable_type env (EL j ts) /\ ?av. has_type (vyper_to_abi_type env (EL j ts)) av` by
    (conj_tac >- metis_tac[EVERY_MEM] >>
     qexists_tac `EL j avs` >> fs[EL_MAP]) >>
  Cases_on `j = i`
  >- (qpat_x_assum `j = i` SUBST_ALL_TAC >> simp_tac bool_ss [] >>
      `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE i ts))) +
       abi_member_head_size (vyper_to_abi_type env (EL i ts)) <= (^head_sum) ts` by
        (qspecl_then [`ts:type list`,`abi_member_head_size o vyper_to_abi_type env`,
                      `i`,`LENGTH ts`] mp_tac sum_take_element_before >>
         simp[MAP_MAP_o, combinTheory.o_THM]) >>
      qpat_x_assum `?u. abi_decoder_coherent _ _ _ _ u /\ _`
        (qx_choose_then `child_tv` strip_assume_tac) >>
      `type_memory_size child_tv < dimword (:256)` by (simp[] >> decide_tac) >>
      conj_tac >- (qexists_tac `child_tv` >> rpt conj_tac >>
                   FIRST [first_assum ACCEPT_TAC,
                          qexists_tac `av` >> first_assum ACCEPT_TAC,
                          rename1 `abi_decoder_coherent ce env sf (EL k ts) child_tv` >>
                          asm "member_reject" (qspecl_then [`EL k ts`,`child_tv`] mp_tac) >>
                          (impl_tac >- (simp[] >> qexists_tac `av` >> first_assum ACCEPT_TAC)) >>
                          disch_then ACCEPT_TAC]) >>
      conj_tac >- (irule LESS_EQ_TRANS >> qexists_tac `type_memory_bytes ce par` >> simp[]) >>
      asm "bad" mp_tac >> disch_then (DISJ_CASES_THEN2 assume_tac (assume_tac o cj 3))
      >- (`F` suffices_by simp[] >> pop_assum mp_tac >>
          qpat_assum `b + SUM _ <= LENGTH xs` mp_tac >>
          qpat_assum `SUM _ + abi_member_head_size _ <= _` (mp_tac o BETA_RULE) >>
          rpt (pop_assum kall_tac) >> numLib.ARITH_TAC) >> first_assum ACCEPT_TAC) >>
  `j < i` by decide_tac >>
  qpat_assum `!k. k < i ==> _` (qspec_then `j`
    (drule_then (CONJUNCTS_THEN2 (MAP_EVERY STRIP_ASSUME_TAC o CONJUNCTS)
      (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  rename1 `abi_decoder_coherent ce env sf (EL j ts) child_tv` >>
  `type_memory_size child_tv < dimword (:256)` by (simp[] >> decide_tac) >>
  conj_tac >- (qexists_tac `child_tv` >> rpt conj_tac >>
                   FIRST [first_assum ACCEPT_TAC,
                          qexists_tac `av` >> first_assum ACCEPT_TAC,
                          rename1 `abi_decoder_coherent ce env sf (EL k ts) child_tv` >>
                          asm "member_reject" (qspecl_then [`EL k ts`,`child_tv`] mp_tac) >>
                          (impl_tac >- (simp[] >> qexists_tac `av` >> first_assum ACCEPT_TAC)) >>
                          disch_then ACCEPT_TAC]) >>
  conj_tac >- (irule LESS_EQ_TRANS >> qexists_tac `type_memory_bytes ce par` >> simp[]) >>
  asm_simp_tac bool_ss []
QED

(* Apply the checked scan and execution cuts to the same member layout. *)
Theorem malformed_table_scanned_abort[local]:
  (^head_cut) /\ (^scalar_abort) /\ (^valid_child) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (^entry) st en pos output b d outsz s /\ (^pc) st s /\ (^ghosts) pos output outsz s G tn /\
  en.cs_next_var <= ceiling.cs_next_var /\ fn_has_code st en func /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex dyn (abi_decoder_member_infos sf ce ts)) st = ((),en) /\
  LIST_REL (abi_decoder_coherent ce env sf) ts tvs /\ (^head_sum) ts < dimword (:256) /\
  (^source_table) ce env sf par b ts /\ L = LENGTH xs /\
  type_memory_bytes ce par <= outsz /\ outsz < dimword (:256) /\
  EVERY (assignable_type env) ts /\ has_types (vyper_to_abi_types env ts) avs /\
  (^member_reject) ts ==> (^abort) s G tn
Proof
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (cj 1 abi_decoder_member_infos_layout) >> strip_tac >>
  `L < b + (^head_sum) ts \/ ?i. i < LENGTH ts /\ (^prefix_members) ts i` suffices_by
    (simp_tac bool_ss [] >> disch_tac >>
     MATCH_MP_TAC (SIMP_RULE bool_ss [] malformed_table_head_then_prefix) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac malformed_table_scan_for_prefix >>
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  asm_simp_tac bool_ss []
QED

(* Common physical and semantic inputs of the three table constructors. *)
val parent_inputs = ``\par tv.
  abi_decoder_coherent ce env sf par tv /\ abi_decode_bytes_widths env par /\
  compile_abi_decode_to_buf (Var output) b_op MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce par) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (?av. has_type (vyper_to_abi_type env par) av) /\ assignable_type env par /\
  type_memory_size tv < dimword (:256) /\ abi_size_bound sf par < dimword (:256) /\
  (^entry) st en b_op output b d (type_memory_bytes ce par) s /\
  (^pc) st s /\ en.cs_next_var <= ceiling.cs_next_var /\
  (^malformed_view) par ((^source_view) par b) /\ ~ctx_has_dalloca ctx /\
  (^ghosts) b_op output (type_memory_bytes ce par) s G tn``;

Theorem malformed_tuple_table_joint[local]:
  (^head_cut) /\ (^scalar_abort) /\ (^valid_child) /\ (^member_reject) ts /\
  (^parent_inputs) (TupleT ts) tv ==> (^abort) s G tn
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `L = LENGTH xs /\ b < dimword (:256) /\ LENGTH xs < dimword (:256) /\
   type_memory_bytes ce (TupleT ts) < dimword (:256)` by
    (qhdtm_assum `abi_malformed_entry`
      (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def, abi_malformed_allocated_window_def]) >>
     `L = LENGTH xs` by
       (qpat_assum `mem_bytes_at _ _ _ = xs` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
        simp[LENGTH_mem_bytes_at]) >>
     rpt conj_tac >> (simp[])) >>
  `(^source_table) ce env sf (TupleT ts) b ts` by
    (qspecl_then [`ce`,`env`,`sf`,`TupleT ts`,`tv`,`xs`,`b`] mp_tac
       malformed_aggregate_first_bad_child >>
     simp_tac bool_ss [LET_THM, vyperASTTheory.type_case_def, ADD_CLAUSES] >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_coherent _ _ _ (TupleT _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_tuple_iff]) >>
  drule_all abi_malformed_tuple_capacity >> strip_tac >>
  `EVERY (assignable_type env) ts` by fs[assignable_type_def, SF ETA_ss] >>
  `?avs. has_types (vyper_to_abi_types env ts) avs` by
    (qpat_assum `?av. has_type (vyper_to_abi_type env (TupleT ts)) av`
       (qx_choose_then `av` assume_tac) >>
     Cases_on `av` >> fs[Once vyper_to_abi_type_def, has_type_def] >>
     goal_assum (drule_at Any)) >>
  rule_assum_tac (SIMP_RULE bool_ss [LET_THM, TAKE_LENGTH_ID_rwt]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`pos` |-> `b_op`, `outsz` |-> `type_memory_bytes ce (TupleT ts)`,
                   `par` |-> `TupleT ts`,
                   `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) ts`]
                 malformed_table_scanned_abort) >>
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt, LESS_EQ_REFL] >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss []])) >>
  disch_then ACCEPT_TAC
QED

Theorem malformed_fixed_table_joint[local]:
  (^head_cut) /\ (^scalar_abort) /\ (^valid_child) /\ (^member_reject) (REPLICATE n t) /\
  (^parent_inputs) (ArrayT t (Fixed n)) tv ==> (^abort) s G tn
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `L = LENGTH xs /\ b < dimword (:256) /\ LENGTH xs < dimword (:256) /\
   type_memory_bytes ce (ArrayT t (Fixed n)) < dimword (:256)` by
    (qhdtm_assum `abi_malformed_entry`
      (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def, abi_malformed_allocated_window_def]) >>
     `L = LENGTH xs` by
       (qpat_assum `mem_bytes_at _ _ _ = xs` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
        simp[LENGTH_mem_bytes_at]) >>
     simp[]) >>
  `(^source_table) ce env sf (ArrayT t (Fixed n)) b (REPLICATE n t)` by
    (qspecl_then [`ce`,`env`,`sf`,`ArrayT t (Fixed n)`,`tv`,`xs`,`b`] mp_tac
       malformed_aggregate_first_bad_child >>
     simp_tac bool_ss [LET_THM, vyperASTTheory.type_case_def, vyperASTTheory.bound_case_def, ADD_CLAUSES] >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_array_iff]) >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) abi_malformed_array_capacity >>
  `(^head_sum) (REPLICATE n t) < dimword (:256)` by
    simp[map_replicate, SUM_REPLICATE] >>
  `?tvs. LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n t) tvs` by
    (rename1 `abi_decoder_coherent ce env sf t etv` >>
     qexists_tac `REPLICATE n etv` >> simp[LIST_REL_REPLICATE_same]) >>
  `EVERY (assignable_type env) (REPLICATE n t)` by
    fs[assignable_type_def, EVERY_REPLICATE] >>
  `?avs. has_types (vyper_to_abi_types env (REPLICATE n t)) avs` by
    (qpat_assum `?av. has_type (vyper_to_abi_type env (ArrayT t (Fixed n))) av`
       (qx_choose_then `av` assume_tac) >>
     qpat_x_assum `has_type _ av` mp_tac >> Cases_on `av` >>
     simp_tac (srw_ss()) [has_type_def, valid_length_def, LET_THM, vyper_to_abi_types_MAP,
                         map_replicate] >>
     strip_tac >> qpat_assum `LENGTH _ = n` (SUBST1_TAC o SYM) >>
     goal_assum (drule_at Any)) >>
  rule_assum_tac (SIMP_RULE bool_ss [LET_THM, TAKE_LENGTH_ID_rwt]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (Q.INST [`pos` |-> `b_op`, `outsz` |-> `type_memory_bytes ce (ArrayT t (Fixed n))`,
                   `par` |-> `ArrayT t (Fixed n)`, `ts` |-> `REPLICATE n t`,
                   `dyn` |-> `is_abi_dynamic ce.ce_struct_fields t`]
                 malformed_table_scanned_abort) >>
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt, LESS_EQ_REFL] >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss []])) >>
  disch_then ACCEPT_TAC
QED

Theorem malformed_struct_table_joint[local]:
  (^head_cut) /\ (^scalar_abort) /\
  ((\env sf. (^valid_child)) (env \\ nsid) (sf \\ nsid_to_string nsid)) /\
  (!args. FLOOKUP env nsid = SOME (StructArgs args) ==>
    (\env sf. (^member_reject) (MAP SND args)) (env \\ nsid) (sf \\ nsid_to_string nsid)) /\
  (^parent_inputs) (StructT nsid) tv ==> (^abort) s G tn
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `L = LENGTH xs /\ b < dimword (:256) /\ LENGTH xs < dimword (:256) /\
   type_memory_bytes ce (StructT nsid) < dimword (:256)` by
    (qhdtm_assum `abi_malformed_entry`
      (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def, abi_malformed_allocated_window_def]) >>
     `L = LENGTH xs` by
       (qpat_assum `mem_bytes_at _ _ _ = xs` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
        simp[LENGTH_mem_bytes_at]) >>
     simp[]) >>
  qpat_assum `abi_decoder_coherent _ _ _ (StructT _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_struct_iff]) >>
  `(^source_table) ce (env \\ nsid) (sf \\ nsid_to_string nsid) (StructT nsid) b (MAP SND args)` by
    (qspecl_then [`ce`,`env`,`sf`,`StructT nsid`,`tv`,`xs`,`b`] mp_tac
       malformed_aggregate_first_bad_child >>
     simp_tac bool_ss [LET_THM, vyperASTTheory.type_case_def, ADD_CLAUSES] >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac bool_ss [optionTheory.SOME_11, type_args_11]) >>
  drule_all abi_malformed_struct_capacity >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args)` by
    fs[assignable_type_def, EVERY_MAP, combinTheory.o_DEF] >>
  `?avs. has_types (vyper_to_abi_types (env \\ nsid) (MAP SND args)) avs` by
    (qpat_assum `?av. has_type (vyper_to_abi_type env (StructT nsid)) av`
       (qx_choose_then `av` assume_tac) >>
     qpat_x_assum `has_type _ av` mp_tac >> Cases_on `av` >>
     asm_simp_tac (srw_ss()) [has_type_def, Once vyper_to_abi_type_def] >>
     strip_tac >> goal_assum (drule_at Any)) >>
  drule abi_caller_struct_map_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >>
  disch_then (fn th =>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `MAP (FST o SND) fields = MAP SND args` (fn th =>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `!args. FLOOKUP _ _ = SOME (StructArgs args) ==> _`
    (qspec_then `args` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  qpat_x_assum `L = LENGTH xs` SUBST_ALL_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss [LET_THM, TAKE_LENGTH_ID_rwt]) >>
  mp_tac (Q.INST [`pos` |-> `b_op`, `outsz` |-> `type_memory_bytes ce (StructT nsid)`,
                   `L` |-> `LENGTH (xs:word8 list)`,
                   `par` |-> `StructT nsid`, `ts` |-> `MAP SND (args:(string # type) list)`,
                   `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
                   `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND (args:(string # type) list))`]
                 malformed_table_scanned_abort) >>
  simp_tac bool_ss [LET_THM, TAKE_LENGTH_ID_rwt, LESS_EQ_REFL] >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss []])) >>
  disch_then ACCEPT_TAC
QED

(* Closed ordinary success and the coherent induction hypothesis for a child. *)
val success_ih = ``!H0 ce env sf ty tv v ctx func cenv cx es st en source hi pos
  output B L xs p d dstid live ceiling s G tn lo PG.
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\ (^ghosts) pos output (type_memory_bytes ce ty) s G tn ==>
  ?u H z. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s u /\ (^worlds) s u /\ (^path) s G tn (OK u) H z /\
    ptr_covers H z output u (type_memory_bytes ce ty) /\
    abi_decode_ptr_window H z u source (n2w B) L /\
    (!mem. mem_agree_outside z.t_mem u.vs_memory mem ==> val_in_memory tv v d mem) /\
    (^old_live) st G tn H z /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN z.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
val reject_ih = ``\ce env sf ty tv. !H0 output b_op source hi st en func ctx cenv cx es
  dstid live B L xs b d s ceiling bytes G tn lo PG.
  abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
  compile_abi_decode_to_buf (Var output) b_op MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce ty) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  assignable_type env ty /\ type_memory_size tv < dimword(:256) /\
  abi_size_bound sf ty < dimword(:256) /\
  (^entry) st en b_op output b d (type_memory_bytes ce ty) s /\
  (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => b+32 <= L | _ => T) /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  bytes = (^source_view) ty b /\ (^malformed_view) ty bytes /\
  ~ctx_has_dalloca ctx /\ (^ghosts) b_op output (type_memory_bytes ce ty) s G tn ==>
  (^abort) s G tn``;

Theorem malformed_table_success_specialize[local]:
  (^success_ih) /\ ~ctx_has_dalloca ctx ==> (^valid_child)
Proof
  simp_tac bool_ss [] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "valid") assume_tac) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm "valid" drule_all >> simp[]
QED

Theorem malformed_table_members_specialize[local]:
  LIST_REL (abi_decoder_coherent ce env sf) ts tvs /\
  EVERY (\(t,tv). (^reject_ih) ce env sf t tv) (ZIP (ts,tvs)) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx ==> (^member_reject) ts
Proof
  simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule LIST_REL_LENGTH >> strip_tac >>
  rename1 `MEM ty ts` >> rename1 `abi_decoder_coherent ce env sf ty tv` >>
  `?j. j < LENGTH ts /\ EL j ts = ty` by metis_tac[MEM_EL] >>
  `abi_decoder_coherent ce env sf ty (EL j tvs)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `EL j tvs = tv` by metis_tac[abi_decoder_coherent_header, abi_decoder_header_def, optionTheory.SOME_11] >>
  `MEM (ty,tv) (ZIP (ts,tvs))` by
    (`j < LENGTH (ZIP (ts,tvs))` by simp[LENGTH_ZIP] >>
     drule_then mp_tac EL_MEM >> simp[EL_ZIP]) >>
  qpat_x_assum `EVERY _ (ZIP (ts,tvs))`
    (qspec_then `(ty,tv)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  asm_simp_tac (srw_ss()) [] >> disch_then (mk_asm "reject") >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm "reject" drule_all >> simp[]
QED

(* H6 supplies the immediate coherent children in constructor order. *)
Theorem malformed_table_first_failure_joint:
  (^success_ih) /\ (^head_cut) /\ (^scalar_abort) /\ (^parent_inputs) par tv /\
  ((?ts tvs. par = TupleT ts /\ tv = TupleTV tvs /\
      LIST_REL (abi_decoder_coherent ce env sf) ts tvs /\
      EVERY (\(t,v). (^reject_ih) ce env sf t v) (ZIP (ts,tvs))) \/
   (?nsid args tvs. par = StructT nsid /\ tv = StructTV (ZIP (MAP FST args,tvs)) /\
      FLOOKUP env nsid = SOME (StructArgs args) /\
      LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
        (MAP SND args) tvs /\
      EVERY (\(t,v). (^reject_ih) ce (env \\ nsid) (sf \\ nsid_to_string nsid) t v)
        (ZIP (MAP SND args,tvs))) \/
   (?t n etv. par = ArrayT t (Fixed n) /\ tv = ArrayTV etv (Fixed n) /\
      (^reject_ih) ce env sf t etv)) ==>
  (^abort) s G tn
Proof
  simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?ts tvs. par = TupleT ts /\ _) \/ _` strip_assume_tac
  >- (qpat_x_assum `par = TupleT _` SUBST_ALL_TAC >>
      `(^valid_child)` by (BETA_TAC >> mp_tac malformed_table_success_specialize >> simp_tac bool_ss [] >>
       (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
      `(^member_reject) ts` by
        (mp_tac malformed_table_members_specialize >> simp_tac bool_ss [] >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
      rule_assum_tac (SIMP_RULE bool_ss []) >>
      mp_tac malformed_tuple_table_joint >> simp_tac bool_ss [] >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (qpat_x_assum `par = StructT _` SUBST_ALL_TAC >>
      `((\env sf. (^valid_child)) (env \\ nsid) (sf \\ nsid_to_string nsid))` by
        (BETA_TAC >> mp_tac (Q.INST [`env` |-> `env \\ nsid`,
                         `sf` |-> `sf \\ nsid_to_string nsid`]
                         malformed_table_success_specialize) >> simp_tac bool_ss [] >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
      `!args'. FLOOKUP env nsid = SOME (StructArgs args') ==>
        (\env sf. (^member_reject) (MAP SND args')) (env \\ nsid) (sf \\ nsid_to_string nsid)` by
        (rpt strip_tac >> `args' = args` by gvs[optionTheory.SOME_11, type_args_11] >>
         qpat_x_assum `args' = args` SUBST_ALL_TAC >>
         mp_tac (Q.INST [`env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
                          `ts` |-> `MAP SND (args:(string # type) list)`]
                         malformed_table_members_specialize) >>
         simp_tac bool_ss [] >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
      rule_assum_tac (SIMP_RULE bool_ss []) >>
      mp_tac malformed_struct_table_joint >> simp_tac bool_ss [] >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `par = ArrayT _ (Fixed _)` SUBST_ALL_TAC >>
  `(^valid_child)` by (BETA_TAC >> mp_tac malformed_table_success_specialize >> simp_tac bool_ss [] >>
       (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_decoder_coherent ce env sf t etv` by
    fs[abi_decoder_coherent_array_iff] >>
  `(^member_reject) (REPLICATE n t)` by
    (mp_tac (Q.INST [`ts` |-> `REPLICATE n t`, `tvs` |-> `REPLICATE n etv`]
                     malformed_table_members_specialize) >>
     simp_tac bool_ss [] >>
     (impl_tac >-
       (conj_tac >- simp[LIST_REL_REPLICATE_same] >>
        conj_tac >-
          (simp_tac bool_ss [vyperMiscTheory.ZIP_REPLICATE, EVERY_REPLICATE] >>
           disj2_tac >> CONV_TAC pairLib.GEN_BETA_CONV >> first_assum ACCEPT_TAC) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  rule_assum_tac (SIMP_RULE bool_ss []) >>
  mp_tac malformed_fixed_table_joint >> simp_tac bool_ss [] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED
