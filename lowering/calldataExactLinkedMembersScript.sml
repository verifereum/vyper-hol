Theory calldataExactLinkedMembers
Ancestors
  calldataExactMembers calldataSourceCorrespondence calldataExactAggregateSource calldataReconstruction typedCopyTuplePtr exprSimAggregateEncoding exprSimAggregateLoops calldataMembers calldataExactMemberFrame abiEncoderInput exprLoweringProps abiDecoderAppend emitHelperProps abiEncoder compileEnv fragExec fragExecMem list rich_list arithmetic

(* The raw-word interface keeps the traversal independent of source types. *)
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
