Theory calldataExactLinkedMembers
Ancestors
  calldataExactMembers calldataSourceCorrespondence calldataExactAggregateSource calldataReconstruction typedCopyTuplePtr exprSimAggregateEncoding exprSimAggregateLoops calldataMembers calldataExactMemberFrame abiEncoderInput exprLoweringProps abiDecoderAppend emitHelperProps abiEncoder compileEnv fragExec fragExecMem list rich_list arithmetic

(* The raw-word interface keeps the traversal independent of source types. *)
Theorem calldata_members_owned_bad_intervals_linked_tail:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao0 vo0 st = ((),final) /\
  fn_has_code st final fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d+vo0 /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+vo0+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  (!i. i < LENGTH xs ==> type_memory_size (ty_at i) <= (\(ei,az,mz). mz) (EL i xs)) /\
  (!i ei az mz. i < LENGTH xs /\ EL i xs = (ei,az,mz) ==>
    member_ptrs i = w2n
      (if dec_info_needs_offset ei then
         srcword + abi_decode_load CALLDATALOAD
           (srcword + n2w (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))) initial
       else srcword + n2w (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + (ao0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
      (mz + (vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      u.vs_call_ctx.cc_calldata = initial.vs_call_ctx.cc_calldata /\ w2n w = member_ptrs i /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (ty_at i) <= base_addr+cap /\
      e+type_memory_size (ty_at i) < dimword (:256) ==>
      (Bad /\ ?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ Pred i x /\ val_wf (ty_at i) x /\
        val_in_memory (ty_at i) x e v.vs_memory /\
        (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
          ?fuel'. run_from fuel' ctx fn u = r /\
            (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
        v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
        alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        u.vs_alloca_next <= v.vs_alloca_next /\
        (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          FLOOKUP v.vs_allocas id = SOME (q,k)) /\
        (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
          FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
        (!op. abi_decoder_operand_live mid.cs_next_var op ==>
          eval_operand op v = eval_operand op u) /\
        abi_decode_footprint_frame ((e,type_memory_size (ty_at i))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (Bad /\ ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ LENGTH vs = LENGTH xs /\
    (!i. i < LENGTH xs ==> Pred i (EL i vs) /\ val_wf (ty_at i) (EL i vs) /\
      val_in_memory (ty_at i) (EL i vs)
        (d+(vo0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) t.vs_memory) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame
      ((d+vo0,SUM (MAP (\(ei,az,mz). mz) xs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `A = \i. ao0 + SUM (MAP (\(ei,az,mz). az) (TAKE i xs))` >>
  qabbrev_tac `V = \i. vo0 + SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))` >>
  qabbrev_tac `Inv = \rest ao vo a s. ?n vs scratch.
    n <= LENGTH xs /\ LENGTH vs = n /\ rest = DROP n xs /\ ao = A n /\ vo = V n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) rest ao vo a = ((),final) /\
    fn_has_code a final fn /\
    cs_extends st a /\ cs_extends a final /\ ci_mono st a /\ ci_mono a final /\
    eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live a.cs_next_var src /\ abi_decoder_operand_live a.cs_next_var dst /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    exact_member_owned_frame ctx fn site st.cs_next_id final.cs_next_id st.cs_next_var
      (d+vo0) (SUM (MAP (\(ei,az,mz). mz) xs)) initial s scratch /\
    (!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
      val_in_memory (ty_at j) (EL j vs) (d+V j) s.vs_memory)` >>
  qspecl_then [`ctx`,`fn`,`dst`,`src`,`Inv`,`Bad`] mp_tac
    calldata_members_fixed_fn_bad_invariant_rule >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> suspend "member_step")) >>
  disch_then (qspecl_then [`xs`,`ao0`,`vo0`,`st`,`final`,`initial`] mp_tac) >>
  (impl_tac >- (simp[] >> suspend "initial_invariant")) >>
  strip_tac >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `Inv [] _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  `LENGTH vs = LENGTH xs` by
    (qpat_x_assum `[] = DROP _ _` (mp_tac o SYM) >>
     pure_rewrite_tac [DROP_EQ_NIL] >> decide_tac) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >>
  qpat_x_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [exact_member_owned_frame_def] >> strip_tac >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _` kall_tac >>
  qpat_x_assum `!j. j < n ==> _` mp_tac >>
  simp_tac bool_ss [Abbr `V`] >> strip_tac >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume calldata_members_owned_bad_intervals_linked_tail[initial_invariant]:
  qpat_x_assum `!i a mid b ep dp ei az mz. _` kall_tac >>
  `cs_extends st final` by metis_tac[] >>
  qpat_x_assum `!ys ao vo a b. _` kall_tac >>
  qpat_x_assum `!ei ao vo a b. _` kall_tac >>
  `ci_mono st final` by
    (mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`xs`,`ao0`,`vo0`,`st`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `A 0 = ao0 /\ V 0 = vo0` by
    simp_tac bool_ss [Abbr `A`, Abbr `V`, TAKE_0, MAP, SUM, ADD_0] >>
  simp_tac bool_ss [Abbr `Inv`] >>
  qexistsl_tac [`[]`,`[]`] >>
  asm_rewrite_tac [LENGTH, DROP_0, LE_0, prim_recTheory.NOT_LESS_0, cs_extends_refl, ci_mono_refl] >>
  irule exact_member_owned_frame_init >> asm_rewrite_tac[]
QED

Resume calldata_members_owned_bad_intervals_linked_tail[member_step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  rename1 `LENGTH vs <= LENGTH xs` >>
  qabbrev_tac `n = LENGTH vs` >>
  qpat_assum `_::rest = DROP _ _` (mp_tac o SYM) >>
  disch_then (strip_assume_tac o MATCH_MP DROP_EQ_CONS) >>
  suspend "address_split"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[address_split]:
  qpat_x_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) a = ((),b)` mp_tac >>
  simp_tac (srw_ss() ++ boolSimps.LET_ss) [comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> SUBST1_TAC th) >> simp_tac (srw_ss()) [] >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> SUBST1_TAC th) >> simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w) a = (ep,c1)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] c1 = (dp,addr)` >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
     rest (ao+az) (vo+mz) b = ((),final)` by
    (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ (_::rest) _ _ _ = _` mp_tac >>
     qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_assum `compile_abi_decode_to_buf dp ep _ _ _ ei addr = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
          compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def]) >>
  suspend "address_execute"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[address_execute]:
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),addr)` by
    (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     simp[comp_bind_def, comp_return_def]) >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a addr` by
    (irule cs_extends_same_block >>
     qpat_assum `inst_extends a addr` mp_tac >>
     qpat_assum `addr.cs_current_bb = a.cs_current_bb` mp_tac >>
     qpat_assum `addr.cs_blocks = a.cs_blocks` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[inst_extends_def]) >>
  `cs_extends addr b` by (drule cs_extends_abi_decode >> simp[]) >>
  `fn_has_code a addr fn /\ fn_has_code addr b fn` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all calldata_member_address_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [combinTheory.K_THM] >> strip_tac >>
  suspend "address_frame"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[address_frame]:
  `alloca_inv s /\ alloca_frontier_inv ctx fn site s` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [exact_member_owned_frame_def] >> metis_tac[]) >>
  `alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    (drule_all calldataDynOwnedTheory.calldata_alloca_invariants_fields >>
     disch_then (fn th => pure_rewrite_tac [th]) >> asm_rewrite_tac[]) >>
  `st.cs_next_var <= a.cs_next_var` by
    (qpat_assum `ci_mono st a` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
       eval_operand op t = eval_operand op s` by
    (qpat_assum `st.cs_next_var <= a.cs_next_var` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live a.cs_next_var op ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `abi_decoder_operand_live a.cs_next_var op` by
       metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
     first_x_assum irule >> asm_rewrite_tac[]) >>
  `exact_member_owned_frame ctx fn site st.cs_next_id final.cs_next_id
     st.cs_next_var (d+vo0) (SUM (MAP (\(ei,az,mz). mz) xs)) initial t scratch` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `t.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `t.vs_call_ctx = s.vs_call_ctx` mp_tac >>
     qpat_assum `t.vs_data_section = s.vs_data_section` mp_tac >>
     qpat_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `t.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` mp_tac >>
     qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     metis_tac[exact_member_owned_frame_transport]) >>
  suspend "child_prepare"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[child_prepare]:
  `ci_mono addr b /\ ci_mono b final` by
    (conj_tac
     >- (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
         disch_then (qspecl_then [`dp`,`ep`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`ei`,`addr`] mp_tac) >> simp[]) >>
     mp_tac (cj 2 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`rest`,`ao+az`,`vo+mz`,`b`] mp_tac) >> simp[]) >>
  `cs_extends b final` by
    (qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ rest _ _ b = _` mp_tac >>
     qpat_assum `!ys ao vo a b. compile_abi_decode_complex_elems _ _ _ _ _ ys ao vo a = _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `fn_has_code b final fn` by
    (`cs_extends a b` by metis_tac[cs_extends_trans] >>
     qpat_assum `cs_extends a b` mp_tac >>
     qpat_assum `cs_extends b final` mp_tac >>
     qpat_assum `fn_has_code a final fn` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fn_has_code_split]) >>
  `type_memory_size (ty_at n) <= mz` by
    (qpat_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _` (qspec_then `n` mp_tac) >>
     qpat_assum `n < LENGTH xs` mp_tac >>
     qpat_assum `EL n xs = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `vo + mz <= vo0 + SUM (MAP (\(ei,az,mz). mz) xs) /\ vo0 <= vo` by
    (`xs = TAKE n xs ++ (ei,az,mz)::rest` by metis_tac[TAKE_DROP] >>
     qpat_assum `xs = TAKE n xs ++ _` mp_tac >>
     qpat_assum `vo = V n` mp_tac >>
     qpat_assum `Abbrev (V = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
     BETA_TAC >> rpt strip_tac >>
     qpat_x_assum `xs = _` (fn th => once_rewrite_tac [th]) >>
     simp[MAP_APPEND, SUM_APPEND]) >>
  suspend "child_bounds"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[child_bounds]:
  `a.cs_next_id <= addr.cs_next_id /\ a.cs_next_var <= addr.cs_next_var` by
    (qpat_assum `(do ep <- compile_getelemptr_abi _ _ _ _ (Lit 0w) _; _ od) a = ((ep,dp),addr)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `dec_info_needs_offset ei` >>
     simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def, emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `st.cs_next_id <= addr.cs_next_id /\ b.cs_next_id <= final.cs_next_id` by
    (qpat_assum `ci_mono st a` mp_tac >>
     qpat_assum `ci_mono b final` mp_tac >>
     qpat_assum `a.cs_next_id <= addr.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >> decide_tac) >>
  `base_addr <= d+vo /\ d+vo+type_memory_size (ty_at n) <= base_addr+cap /\
   d+vo+type_memory_size (ty_at n) < dimword (:256)` by decide_tac >>
  `eval_operand dp t = SOME (n2w (d+vo))` by
    (qpat_assum `eval_operand dp t = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wordsTheory.word_add_n2w]) >>
  `FLOOKUP t.vs_allocas oid = SOME (base_addr,cap)` by
    (qpat_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas oid = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  suspend "child_call"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[child_call]:
  `!id q k. addr.cs_next_id <= id /\ id < b.cs_next_id /\
     FLOOKUP t.vs_allocas id = SOME (q,k) ==>
     k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
     ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
       ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ _ t _` mp_tac >>
     qpat_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [exact_member_owned_frame_def] >> rpt strip_tac >>
     `st.cs_next_id <= id /\ id < final.cs_next_id` by decide_tac >>
     qpat_x_assum `!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\ _ ==> _`
       (qspecl_then [`id`,`q`,`k`] mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `ao = ao0 + SUM (MAP (\(ei,az,mz). az) (TAKE n xs)) /\
   vo = vo0 + SUM (MAP (\(ei,az,mz). mz) (TAKE n xs))` by
    (qpat_assum `ao = A n` mp_tac >> qpat_assum `vo = V n` mp_tac >>
     simp_tac bool_ss [Abbr `A`, Abbr `V`]) >>
  suspend "callback_links"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[callback_links]:
  `s.vs_call_ctx = initial.vs_call_ctx /\ t.vs_call_ctx = initial.vs_call_ctx` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ initial s _` mp_tac >>
     qpat_assum `t.vs_call_ctx = s.vs_call_ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [exact_member_owned_frame_def] >> metis_tac[]) >>
  `w2n (if dec_info_needs_offset ei then
      srcword + abi_decode_load CALLDATALOAD (srcword + n2w ao) s
      else srcword + n2w ao) = member_ptrs n` by
    (qpat_assum `!i ei az mz. _ ==> member_ptrs i = _`
       (qspecl_then [`n`,`ei`,`az`,`mz`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     qpat_assum `ao = ao0 + _` (fn th => pure_rewrite_tac [GSYM th]) >>
     qpat_assum `s.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def]) >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _` (qspec_then `n` mp_tac) >>
  qpat_assum `ao = ao0 + _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `vo = vo0 + _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `DROP (SUC n) xs = rest` (fn th => pure_rewrite_tac [th]) >>
  disch_then (qspecl_then [`a`,`addr`,`b`,`ep`,`dp`,`ei`,`az`,`mz`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ rest (ao+az) (vo+mz) b = _` mp_tac >>
    qpat_assum `ao = ao0 + _` mp_tac >> qpat_assum `vo = vo0 + _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[AC ADD_ASSOC ADD_COMM])) >>
  disch_then (qspecl_then [`t`,
    `if dec_info_needs_offset ei then srcword + abi_decode_load CALLDATALOAD (srcword + n2w ao) s else srcword + n2w ao`,
    `d+vo`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  suspend "child_result"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[child_result]:
  strip_tac
  >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!fuel. (!e. run_from fuel ctx fn t <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >>
      qpat_assum `run_from _ ctx fn t = Abort Revert_abort _` mp_tac >>
      qpat_assum `mem_safe_run _ ctx fn t` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >> metis_tac[]) >>
  `exact_member_owned_frame ctx fn site addr.cs_next_id b.cs_next_id
     addr.cs_next_var (d+vo) (type_memory_size (ty_at n)) t v sc` by
    (pure_rewrite_tac [exact_member_owned_frame_def] >> asm_rewrite_tac[]) >>
  suspend "child_success"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[child_success]:
  `addr.cs_next_id <= b.cs_next_id /\ st.cs_next_var <= addr.cs_next_var` by
    (qpat_assum `ci_mono addr b` mp_tac >>
     qpat_assum `st.cs_next_var <= a.cs_next_var` mp_tac >>
     qpat_assum `a.cs_next_var <= addr.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >> decide_tac) >>
  `d+vo0 <= d+vo /\ d+vo+type_memory_size (ty_at n) <=
     d+vo0+SUM (MAP (\(ei,az,mz). mz) xs)` by decide_tac >>
  `exact_member_owned_frame ctx fn site st.cs_next_id final.cs_next_id
     st.cs_next_var (d+vo0) (SUM (MAP (\(ei,az,mz). mz) xs)) initial v (scratch ++ sc)` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ initial t scratch` mp_tac >>
     qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ t v sc` mp_tac >>
     qpat_assum `st.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_assum `addr.cs_next_id <= b.cs_next_id` mp_tac >>
     qpat_assum `b.cs_next_id <= final.cs_next_id` mp_tac >>
     qpat_assum `st.cs_next_var <= addr.cs_next_var` mp_tac >>
     qpat_assum `d+vo0 <= d+vo` mp_tac >>
     qpat_assum `d+vo+type_memory_size (ty_at n) <= d+vo0+_` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     metis_tac[exact_member_owned_frame_compose]) >>
  suspend "prefix_success"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[prefix_success]:
  `!j. j < n ==> Pred j (EL j vs) /\ val_wf (ty_at j) (EL j vs) /\
     val_in_memory (ty_at j) (EL j vs) (d+V j) v.vs_memory` by
    (qx_gen_tac `j` >> strip_tac >>
     `j < LENGTH xs` by decide_tac >>
     `type_memory_size (ty_at j) <= (\(ei,az,mz). mz) (EL j xs)` by
       (qpat_assum `!i. i < LENGTH xs ==> type_memory_size _ <= _` (qspec_then `j` mp_tac) >>
        qpat_assum `j < LENGTH xs` mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     `V j + type_memory_size (ty_at j) <= vo /\ vo0 <= V j` by
       (qspecl_then [`\(ei,az,mz). mz`,`TAKE n xs`,`j`] mp_tac abi_encoder_prefix_sum_bound >>
        qpat_assum `Abbrev (V = _)` mp_tac >> qpat_assum `vo = V n` mp_tac >>
        qpat_assum `j < n` mp_tac >> qpat_assum `n <= LENGTH xs` mp_tac >>
        qpat_assum `type_memory_size (ty_at j) <= _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        pure_rewrite_tac [markerTheory.Abbrev_def] >> rpt strip_tac >>
        gvs[TAKE_TAKE, MIN_DEF, EL_TAKE]) >>
     qpat_assum `!j. j < n ==> Pred j _ /\ _` (qspec_then `j` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     `val_in_memory (ty_at j) (EL j vs) (d+V j) t.vs_memory` by asm_rewrite_tac[] >>
     suspend "preserve_prefix_value") >>
  suspend "success_finish"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[preserve_prefix_value]:
  `val_in_memory (ty_at j) (EL j vs) (d+V j) v.vs_memory` by
    (irule calldata_member_value_preserved >>
     qpat_assum `abi_decode_footprint_frame _ t v` (irule_at Any) >>
     qpat_assum `FLOOKUP t.vs_allocas oid = SOME _` (irule_at Any) >>
     qexistsl_tac [`addr.cs_next_id`,`b.cs_next_id`] >> asm_rewrite_tac[] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Resume calldata_members_owned_bad_intervals_linked_tail[success_finish]:
  `cs_extends st b /\ ci_mono st b` by
    (qpat_assum `cs_extends st a` mp_tac >> qpat_assum `cs_extends a addr` mp_tac >>
     qpat_assum `cs_extends addr b` mp_tac >> qpat_assum `ci_mono st a` mp_tac >>
     qpat_assum `a.cs_next_id <= addr.cs_next_id` mp_tac >>
     qpat_assum `a.cs_next_var <= addr.cs_next_var` mp_tac >>
     qpat_assum `ci_mono addr b` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     simp[ci_mono_def] >> metis_tac[cs_extends_trans,ci_mono_def,LESS_EQ_TRANS]) >>
  `A (SUC n) = az + A n /\ V (SUC n) = mz + V n` by
    (qpat_assum `Abbrev (A = _)` mp_tac >> qpat_assum `Abbrev (V = _)` mp_tac >>
     qpat_assum `n < LENGTH xs` mp_tac >> qpat_assum `EL n xs = (ei,az,mz)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[markerTheory.Abbrev_def] >> rpt strip_tac >>
     simp[TAKE_SUC,SUM_APPEND,AC ADD_ASSOC ADD_COMM]) >>
  suspend "success_entry"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[success_entry]:
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   abi_decoder_operand_live b.cs_next_var src /\ abi_decoder_operand_live b.cs_next_var dst /\
   FLOOKUP v.vs_allocas oid = SOME (base_addr,cap)` by
    (qpat_assum `exact_member_owned_frame _ _ _ _ _ _ _ _ initial v (scratch++sc)` mp_tac >>
     qpat_assum `eval_operand src initial = SOME _` mp_tac >>
     qpat_assum `eval_operand dst initial = SOME _` mp_tac >>
     qpat_assum `abi_decoder_operand_live st.cs_next_var src` mp_tac >>
     qpat_assum `abi_decoder_operand_live st.cs_next_var dst` mp_tac >>
     qpat_assum `FLOOKUP initial.vs_allocas oid = SOME _` mp_tac >>
     qpat_assum `ci_mono st b` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[exact_member_owned_frame_def,ci_mono_def] >> rpt strip_tac >>
     metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]) >>
  disj2_tac >> qexists_tac `v` >> asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`vs++[x]`,`scratch++sc`] >>
      `LENGTH (vs++[x]) = SUC n` by
        (qpat_assum `Abbrev (n = LENGTH vs)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
      pure_asm_rewrite_tac[] >> suspend "success_prefix_extend") >>
  suspend "success_back"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[success_back]:
  qpat_assum `!fuel r. run_from fuel ctx fn v = r /\ _ ==> _` mp_tac >>
  qpat_assum `!fuel. (!e. run_from fuel ctx fn t <> Error e) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  first_x_assum (qspec_then `fuel` mp_tac) >> suspend "back_chain"
QED

Resume calldata_members_owned_bad_intervals_linked_tail[success_prefix_extend]:
  conj_tac >- decide_tac >> conj_tac >- REFL_TAC >> conj_tac
  >- (qpat_assum `Abbrev (A = _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,ADD_COMM]) >>
  conj_tac
  >- (qpat_assum `Abbrev (V = _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,ADD_COMM]) >>
  rewrite_tac[] >> qx_gen_tac `j` >> strip_tac >> Cases_on `j < n`
  >- (qpat_assum `!j. j < n ==> Pred j _ /\ _ /\ val_in_memory _ _ _ v.vs_memory`
        (qspec_then `j` mp_tac) >>
      qpat_assum `Abbrev (n = LENGTH vs)` mp_tac >>
      qpat_assum `j < n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
      simp[markerTheory.Abbrev_def,EL_APPEND1]) >>
  `j = n` by decide_tac >> qpat_assum `Pred n x` mp_tac >>
  qpat_assum `val_wf (ty_at n) x` mp_tac >>
  qpat_assum `val_in_memory (ty_at n) x (d+vo) v.vs_memory` mp_tac >>
  qpat_assum `vo = V n` mp_tac >> qpat_assum `Abbrev (n = LENGTH vs)` mp_tac >>
  qpat_assum `j = n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp[markerTheory.Abbrev_def,EL_APPEND2]
QED

Resume calldata_members_owned_bad_intervals_linked_tail[back_chain]:
  disch_then (qspec_then `run_from fuel ctx fn v` mp_tac) >>
  simp[] >> strip_tac >> first_x_assum (qspec_then `fuel'` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> qexists_tac `fuel''` >> metis_tac[]
QED

Finalise calldata_members_owned_bad_intervals_linked_tail

Theorem calldata_exact_aggregate_owned_run_linked_tail:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs 0 0 st = ((),final) /\
  fn_has_code st final fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\ base_addr <= d /\
  d+type_memory_size TV <= base_addr+cap /\ d+type_memory_size TV < dimword (:256) /\
  LENGTH ts = LENGTH xs /\
  (!i. i < LENGTH xs ==> type_memory_size (EL i ts) = (\(ei,az,mz). mz) (EL i xs)) /\
  (!i ei az mz. i < LENGTH xs /\ EL i xs = (ei,az,mz) ==>
    dec_info_needs_offset ei = tv_abi_dynamic (EL i ts) /\
    member_ptrs i = cd_member_ptr F initial.vs_call_ctx.cc_calldata (EL i ts)
      (w2n srcword) (SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))) /\
  exact_aggregate_pack TV ts member_ptrs initial.vs_call_ctx.cc_calldata (w2n srcword) build /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))
      (mz + SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      u.vs_call_ctx.cc_calldata = initial.vs_call_ctx.cc_calldata /\ w2n w = member_ptrs i /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (EL i ts) <= base_addr+cap /\
      e+type_memory_size (EL i ts) < dimword (:256) ==>
      (cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = NONE /\
        ?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\
        (cd_decode F initial.vs_call_ctx.cc_calldata (EL i ts) (member_ptrs i) = SOME x /\
          value_has_type (EL i ts) x) /\ val_wf (EL i ts) x /\
        val_in_memory (EL i ts) x e v.vs_memory /\
        (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
          ?fuel'. run_from fuel' ctx fn u = r /\
            (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
        v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
        alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        u.vs_alloca_next <= v.vs_alloca_next /\
        (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          FLOOKUP v.vs_allocas id = SOME (q,k)) /\
        (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
          FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
        (!op. abi_decoder_operand_live mid.cs_next_var op ==>
          eval_operand op v = eval_operand op u) /\
        abi_decode_footprint_frame ((e,type_memory_size (EL i ts))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = NONE /\
    ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\ mem_safe_run fuel ctx fn initial) \/
  ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = SOME (build vs) /\
    value_has_type TV (build vs) /\ val_wf TV (build vs) /\
    val_in_memory TV (build vs) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size TV)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n. n <= LENGTH xs ==>
    SUM (MAP (\(ei,az,mz). mz) (TAKE n xs)) =
    SUM (MAP type_memory_size (TAKE n ts))` by
    (rpt strip_tac >> irule sum_map_take_pointwise >> simp[] >> metis_tac[]) >>
  `SUM (MAP (\(ei,az,mz). mz) xs) = type_memory_size TV` by
    (qpat_assum `exact_aggregate_pack _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [exact_aggregate_pack_def]) >>
     qpat_assum `!n. n <= LENGTH xs ==> _` (qspec_then `LENGTH xs` mp_tac) >>
     qpat_assum `LENGTH ts = LENGTH xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_x_assum `LENGTH ts = LENGTH xs` (fn th => fs[GSYM th])) >>
  `!i ei az mz. i < LENGTH xs /\ EL i xs = (ei,az,mz) ==>
    member_ptrs i = w2n
      (if dec_info_needs_offset ei then
        srcword + abi_decode_load CALLDATALOAD
          (srcword + n2w (SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))) initial
       else srcword + n2w (SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ei az mz. _ ==> _ /\ _`
       (qspecl_then [`i`,`ei`,`az`,`mz`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tv_abi_dynamic (EL i ts)` >>
     simp[vyperCalldataTheory.cd_member_ptr_def, vyperCalldataTheory.cd_at_def,
       calldata_decode_load_word, wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  mp_tac (REWRITE_RULE [ADD_CLAUSES] (BETA_RULE
    (Q.INST [`ty_at` |-> `\i. EL i ts`,
      `Pred` |-> `\i x. cd_decode F initial.vs_call_ctx.cc_calldata (EL i ts) (member_ptrs i) = SOME x /\ value_has_type (EL i ts) x`,
      `Bad` |-> `cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = NONE`,
      `ao0` |-> `0`, `vo0` |-> `0`]
      (SPEC_ALL calldata_members_owned_bad_intervals_linked_tail)))) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> simp[])) >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (disj1_tac >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl [`t`, `vs`, `scratch`] >>
  `cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = SOME (build vs) /\
    value_has_type TV (build vs) /\ val_wf TV (build vs) /\
    val_in_memory TV (build vs) d t.vs_memory` by
    (qpat_x_assum `LENGTH ts = LENGTH xs` mp_tac >>
     qpat_x_assum `LENGTH vs = LENGTH xs` mp_tac >>
     qpat_x_assum `!n. n <= LENGTH xs ==> _` mp_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> (_ /\ _) /\ _` mp_tac >>
     qpat_x_assum `exact_aggregate_pack _ _ _ _ _ _`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [exact_aggregate_pack_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     ntac 5 disch_tac >> qpat_x_assum `!vs d mem. _` irule >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_footprint_frame _ initial t` mp_tac >> asm_rewrite_tac[]
QED
