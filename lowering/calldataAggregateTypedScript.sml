(* Typed aggregate packaging for the reentrant owned decoder. *)
Theory calldataAggregateTyped
Ancestors
  valueEncodingDefs abiDecoderMemberInfos abiDecoderCoherence calldataDynOwned calldataMembers calldataReconstruction exprLowering valueEncoding vyperTyping vyperValue list rich_list arithmetic abiEncoder

Theorem calldata_tuple_indexed_pack[local]:
  !tvs vs d mem.
  LENGTH vs = LENGTH tvs /\
  (!i. i < LENGTH tvs ==>
    value_has_type (EL i tvs) (EL i vs) /\
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
  LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem
Proof
  Induct_on `tvs` >- (Cases_on `vs` >> simp[val_in_memory_def]) >>
  Cases_on `vs` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` assume_tac) >>
  gvs[val_in_memory_def] >>
  `LIST_REL value_has_type tvs t /\ tuple_in_memory t tvs (d + type_memory_size h') mem` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
     simp_tac (srw_ss()) [EL, TAKE_def, MAP, SUM, ADD_ASSOC, LESS_MONO_EQ] >>
     simp[]) >> simp[] >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [EL, TAKE_def, MAP, SUM, ADD_CLAUSES, prim_recTheory.LESS_0]
QED

Theorem calldata_tuple_layout[local]:
  !xs tvs.
  LENGTH tvs = LENGTH xs /\
  (!i. i < LENGTH xs ==>
    (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i tvs)) ==>
  MAP (\(ei,az,mz). mz) xs = MAP type_memory_size tvs
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[EL_MAP] >> first_x_assum irule >> simp[]
QED

Theorem calldata_tuple_prefix_layout[local]:
  LENGTH tvs = LENGTH xs /\
  (!i. i < LENGTH xs ==>
    (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i tvs)) ==>
  !i. MAP (\(ei,az,mz). mz) (TAKE i xs) =
      MAP type_memory_size (TAKE i tvs)
Proof
  strip_tac >> drule_all calldata_tuple_layout >> strip_tac >>
  asm_rewrite_tac[MAP_TAKE]
QED

Theorem calldata_tuple_size[local]:
  !tvs. type_memory_size (TupleTV tvs) = SUM (MAP type_memory_size tvs)
Proof
  simp_tac std_ss [type_memory_size_def] >> Induct >> simp[type_memory_size_def]
QED

Theorem calldata_complex_tuple_owned_run:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecComplex dyn xs) st = ((),final) /\
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
  base_addr <= d /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  LENGTH tvs = LENGTH xs /\
  (!i. i < LENGTH xs ==> (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i tvs)) /\
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
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (EL i tvs) <= base_addr+cap /\
      e+type_memory_size (EL i tvs) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type (EL i tvs) x /\ val_wf (EL i tvs) x /\
        val_in_memory (EL i tvs) x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size (EL i tvs))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (TupleTV tvs) x /\ val_wf (TupleTV tvs) x /\
    val_in_memory (TupleTV tvs) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (TupleTV tvs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_tuple_layout >> disch_then (assume_tac o GSYM) >>
  drule_all calldata_tuple_prefix_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def, LET_THM] >>
  strip_tac >>
  `!i. i < LENGTH xs ==> type_memory_size (EL i tvs) <= (\(ei,az,mz). mz) (EL i xs)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> _ = type_memory_size _` drule >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac std_ss []) >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _`
    (assume_tac o REWRITE_RULE [ADD_CLAUSES]) >>
  mp_tac (REWRITE_RULE [ADD_CLAUSES] (BETA_RULE (Q.INST
    [`ao0` |-> `0`, `vo0` |-> `0`, `ty_at` |-> `\i. EL i tvs`,
     `Pred` |-> `\i x. value_has_type (EL i tvs) x`]
    calldata_members_owned_repeat_intervals))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_x_assum `LENGTH tvs = LENGTH xs` mp_tac >>
  qpat_x_assum `MAP type_memory_size tvs = _` mp_tac >>
  qpat_x_assum `!i. MAP _ (TAKE i xs) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  ntac 3 strip_tac >> strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`,`z`] >> asm_rewrite_tac[]) >>
  disj2_tac >>
  `LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d t.vs_memory` by
    (irule calldata_tuple_indexed_pack >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all calldata_tuple_values_typed_memory >> strip_tac >>
  qexistsl_tac [`t`, `ArrayV (TupleV vs)`, `scratch`] >>
  asm_rewrite_tac[calldata_tuple_size] >>
  rpt strip_tac >> qpat_x_assum `!fuel r. _` irule >>
  asm_rewrite_tac[]
QED

Theorem calldata_struct_tuple_size[local]:
  !ftypes. type_memory_size (StructTV ftypes) =
    type_memory_size (TupleTV (MAP SND ftypes))
Proof
  simp_tac std_ss [type_memory_size_def] >>
  Induct >> simp[type_memory_size_def] >>
  gen_tac >> PairCases_on `h` >> simp[type_memory_size_def]
QED

Theorem calldata_struct_tuple_pack[local]:
  !ftypes vs d mem.
  values_have_types (MAP SND ftypes) vs /\
  tuple_in_memory vs (MAP SND ftypes) d mem ==>
  ?fields.
    LIST_REL (\nt nv. FST nt = FST nv /\ value_has_type (SND nt) (SND nv)) ftypes fields /\
    fields_in_memory fields ftypes d mem
Proof
  Induct >> Cases_on `vs` >> simp[val_in_memory_def, value_has_type_def] >>
  gen_tac >> PairCases_on `h'` >> simp[val_in_memory_def, value_has_type_def] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qspecl_then [`d+type_memory_size h'1`, `mem`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `(h'0,h)::fields` >>
  simp[val_in_memory_def]
QED

Theorem calldata_struct_tuple_repack[local]:
  value_has_type (TupleTV (MAP SND ftypes)) x /\
  val_in_memory (TupleTV (MAP SND ftypes)) x d mem ==>
  ?y. value_has_type (StructTV ftypes) y /\
    val_wf (StructTV ftypes) y /\
    val_in_memory (StructTV ftypes) y d mem
Proof
  Cases_on `x` >> simp[value_has_type_def] >>
  Cases_on `a` >> simp[value_has_type_def] >>
  simp[val_in_memory_def] >> strip_tac >>
  drule_all calldata_struct_tuple_pack >> strip_tac >>
  qexists_tac `StructV fields` >>
  irule calldata_struct_values_typed_memory >> simp[]
QED

Theorem calldata_complex_struct_owned_run:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecComplex dyn xs) st = ((),final) /\
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
  base_addr <= d /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  LENGTH (MAP SND ftypes) = LENGTH xs /\
  (!i. i < LENGTH xs ==> (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i (MAP SND ftypes))) /\
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
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (EL i (MAP SND ftypes)) <= base_addr+cap /\
      e+type_memory_size (EL i (MAP SND ftypes)) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type (EL i (MAP SND ftypes)) x /\ val_wf (EL i (MAP SND ftypes)) x /\
        val_in_memory (EL i (MAP SND ftypes)) x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size (EL i (MAP SND ftypes)))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (StructTV ftypes) x /\ val_wf (StructTV ftypes) x /\
    val_in_memory (StructTV ftypes) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (StructTV ftypes))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`tvs` |-> `MAP SND (ftypes : (identifier # type_value) list)`] calldata_complex_tuple_owned_run) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`, `z`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all calldata_struct_tuple_repack >> strip_tac >>
  qexistsl_tac [`t`, `y`, `scratch`] >>
  asm_rewrite_tac[calldata_struct_tuple_size]
QED

Theorem calldata_fixed_tuple_size[local]:
  !n. type_memory_size (TupleTV (REPLICATE n tv)) =
    type_memory_size (ArrayTV tv (Fixed n))
Proof
  simp[calldata_tuple_size, type_memory_size_def] >>
  Induct >> simp[REPLICATE, type_memory_size_def, MULT_CLAUSES]
QED

Theorem calldata_fixed_tuple_pack[local]:
  !n vs d mem.
  values_have_types (REPLICATE n tv) vs /\
  tuple_in_memory vs (REPLICATE n tv) d mem ==>
  LENGTH vs = n /\ EVERY (value_has_type tv) vs /\ elems_in_memory vs d tv mem
Proof
  Induct >> Cases_on `vs` >>
  simp[REPLICATE, value_has_type_def, val_in_memory_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem calldata_fixed_tuple_repack[local]:
  value_has_type (TupleTV (REPLICATE n tv)) x /\
  val_in_memory (TupleTV (REPLICATE n tv)) x d mem ==>
  ?y. value_has_type (ArrayTV tv (Fixed n)) y /\
    val_wf (ArrayTV tv (Fixed n)) y /\
    val_in_memory (ArrayTV tv (Fixed n)) y d mem
Proof
  Cases_on `x` >> simp[value_has_type_def] >>
  Cases_on `a` >> simp[value_has_type_def] >>
  simp[val_in_memory_def] >> strip_tac >>
  drule_all calldata_fixed_tuple_pack >> strip_tac >>
  qexists_tac `ArrayV (make_array_value tv (Fixed n) l)` >>
  irule calldata_fixed_values_typed_memory >> simp[]
QED

Theorem calldata_fixed_infos_layout[local]:
  abi_decoder_header ce env ty tv /\
  xs = abi_decoder_member_infos sf ce (REPLICATE n ty) ==>
  LENGTH xs = n /\
  MAP (\(ei,az,mz). mz) xs = MAP type_memory_size (REPLICATE n tv) /\
  (!i. i < LENGTH xs ==>
    (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i (REPLICATE n tv)))
Proof
  simp[abi_decoder_header_def, abi_decoder_member_infos_def, MAP_MAP_o,
    combinTheory.o_DEF, map_replicate, EL_REPLICATE]
QED

Theorem calldata_coherent_fixed_array_owned_run:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  xs = abi_decoder_member_infos sf ce (REPLICATE n ty) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Fixed n))) st = ((),final) /\
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
  base_addr <= d /\
  d+type_memory_size (ArrayTV tv (Fixed n)) <= base_addr+cap /\
  d+type_memory_size (ArrayTV tv (Fixed n)) < dimword (:256) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    abi_decoder_coherent ce env sf ty tv /\
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
      e+type_memory_size tv < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type tv x /\ val_wf tv x /\
        val_in_memory tv x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size tv)::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (ArrayTV tv (Fixed n)) x /\ val_wf (ArrayTV tv (Fixed n)) x /\
    val_in_memory (ArrayTV tv (Fixed n)) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (ArrayTV tv (Fixed n)))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp[abi_decoder_coherent_array_iff]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule_all calldata_fixed_infos_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  `d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
   d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256)` by
    asm_rewrite_tac[GSYM calldata_tuple_size, calldata_fixed_tuple_size] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  qpat_x_assum `xs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  disch_tac >>
  mp_tac (Q.INST [`tvs` |-> `REPLICATE n tv`,
    `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`] calldata_complex_tuple_owned_run) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      (rename1 `LENGTH (REPLICATE _ _) = LENGTH _` >> simp[LENGTH_REPLICATE]),
      (rpt gen_tac >> strip_tac >>
       `EL i (REPLICATE n tv) = tv` by simp[EL_REPLICATE] >>
       asm_rewrite_tac[] >>
       qpat_x_assum `!i a mid b ep dp ei az mz. _`
         (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
       disch_then (qspecl_then [`i`, `a`, `az`, `mz`] mp_tac) >>
       asm_rewrite_tac[])])) >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`, `z`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all calldata_fixed_tuple_repack >> strip_tac >>
  qexistsl_tac [`t`, `y`, `scratch`] >>
  asm_rewrite_tac[GSYM calldata_fixed_tuple_size]
QED

Theorem calldata_coherent_dynamic_layout[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) ==>
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_size tv)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) = 32+maxn*type_memory_size tv
Proof
  simp[abi_decoder_coherent_array_iff] >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, type_to_abi_dec_info_def, type_memory_size_def]
QED

Theorem calldata_coherent_nonbulk_array_owned_run:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  di = type_to_abi_dec_info sf ce ty /\
  abi_sz = abi_embedded_static_size ce.ce_struct_fields ty /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (Lit 0w) di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),end_st) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
  fn_has_code st1 end_st fn /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t x scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    value_has_type (ArrayTV tv (Dynamic maxn)) x /\
    val_wf (ArrayTV tv (Dynamic maxn)) x /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) x d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size (ArrayTV tv (Dynamic maxn)))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_coherent_dynamic_layout >> strip_tac >>
  qpat_x_assum `di = _` kall_tac >> qpat_x_assum `abi_sz = _` kall_tac >>
  qpat_x_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _` kall_tac >>
  qpat_x_assum `type_memory_size (ArrayTV _ _) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`P` |-> `value_has_type tv`] calldata_nonbulk_owned_repeat_observed) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`, `z`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`, `ArrayV (DynArrayV vs)`, `scratch`] >>
  asm_rewrite_tac[type_memory_size_def, value_has_type_def, all_have_type_EVERY]
QED

(* Tail-aware companions retain the installed suffix needed by recursive calls. *)
Theorem calldata_complex_tuple_owned_run_tail:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecComplex dyn xs) st = ((),final) /\
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
  base_addr <= d /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  LENGTH tvs = LENGTH xs /\
  (!i. i < LENGTH xs ==> (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i tvs)) /\
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
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
      (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (EL i tvs) <= base_addr+cap /\
      e+type_memory_size (EL i tvs) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type (EL i tvs) x /\ val_wf (EL i tvs) x /\
        val_in_memory (EL i tvs) x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size (EL i tvs))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (TupleTV tvs) x /\ val_wf (TupleTV tvs) x /\
    val_in_memory (TupleTV tvs) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (TupleTV tvs))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_tuple_layout >> disch_then (assume_tac o GSYM) >>
  drule_all calldata_tuple_prefix_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def, LET_THM] >>
  strip_tac >>
  `!i. i < LENGTH xs ==> type_memory_size (EL i tvs) <= (\(ei,az,mz). mz) (EL i xs)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> _ = type_memory_size _` drule >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac std_ss []) >>
  qpat_x_assum `!i a mid b ep dp ei az mz. _`
    (assume_tac o REWRITE_RULE [ADD_CLAUSES]) >>
  mp_tac (REWRITE_RULE [ADD_CLAUSES] (BETA_RULE (Q.INST
    [`ao0` |-> `0`, `vo0` |-> `0`, `ty_at` |-> `\i. EL i tvs`,
     `Pred` |-> `\i x. value_has_type (EL i tvs) x`]
    calldata_members_owned_repeat_intervals_tail))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_x_assum `LENGTH tvs = LENGTH xs` mp_tac >>
  qpat_x_assum `MAP type_memory_size tvs = _` mp_tac >>
  qpat_x_assum `!i. MAP _ (TAKE i xs) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  ntac 3 strip_tac >> strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`,`z`] >> asm_rewrite_tac[]) >>
  disj2_tac >>
  `LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d t.vs_memory` by
    (irule calldata_tuple_indexed_pack >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all calldata_tuple_values_typed_memory >> strip_tac >>
  qexistsl_tac [`t`, `ArrayV (TupleV vs)`, `scratch`] >>
  asm_rewrite_tac[calldata_tuple_size] >>
  rpt strip_tac >> qpat_x_assum `!fuel r. _` irule >>
  asm_rewrite_tac[]
QED

Theorem calldata_complex_struct_owned_run_tail:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecComplex dyn xs) st = ((),final) /\
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
  base_addr <= d /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
  d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256) /\
  LENGTH (MAP SND ftypes) = LENGTH xs /\
  (!i. i < LENGTH xs ==> (\(ei,az,mz). mz) (EL i xs) = type_memory_size (EL i (MAP SND ftypes))) /\
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
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
      (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size (EL i (MAP SND ftypes)) <= base_addr+cap /\
      e+type_memory_size (EL i (MAP SND ftypes)) < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type (EL i (MAP SND ftypes)) x /\ val_wf (EL i (MAP SND ftypes)) x /\
        val_in_memory (EL i (MAP SND ftypes)) x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size (EL i (MAP SND ftypes)))::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (StructTV ftypes) x /\ val_wf (StructTV ftypes) x /\
    val_in_memory (StructTV ftypes) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (StructTV ftypes))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`tvs` |-> `MAP SND (ftypes : (identifier # type_value) list)`] calldata_complex_tuple_owned_run_tail) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`, `z`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all calldata_struct_tuple_repack >> strip_tac >>
  qexistsl_tac [`t`, `y`, `scratch`] >>
  asm_rewrite_tac[calldata_struct_tuple_size]
QED

Theorem calldata_coherent_fixed_array_owned_run_tail:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  xs = abi_decoder_member_infos sf ce (REPLICATE n ty) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Fixed n))) st = ((),final) /\
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
  base_addr <= d /\
  d+type_memory_size (ArrayTV tv (Fixed n)) <= base_addr+cap /\
  d+type_memory_size (ArrayTV tv (Fixed n)) < dimword (:256) /\
  (!ys ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!i a mid b ep dp ei az mz.
    abi_decoder_coherent ce env sf ty tv /\
    i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
          (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
        return (ep,dp) od) a = ((ep,dp),mid) /\
    compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
    cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
    ci_mono st a /\ ci_mono b final /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP (SUC i) xs)
      (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
      (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
    fn_has_code b final fn ==>
    !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
      e+type_memory_size tv < dimword (:256) ==>
      (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
      ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
        v.vs_inst_idx = LENGTH b.cs_current_insts /\ value_has_type tv x /\ val_wf tv x /\
        val_in_memory tv x e v.vs_memory /\
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
        abi_decode_footprint_frame ((e,type_memory_size tv)::sc) u v /\
        (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?t x scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (ArrayTV tv (Fixed n)) x /\ val_wf (ArrayTV tv (Fixed n)) x /\
    val_in_memory (ArrayTV tv (Fixed n)) x d t.vs_memory /\
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
    abi_decode_footprint_frame ((d,type_memory_size (ArrayTV tv (Fixed n)))::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp[abi_decoder_coherent_array_iff]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule_all calldata_fixed_infos_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  `d+SUM (MAP (\(ei,az,mz). mz) xs) <= base_addr+cap /\
   d+SUM (MAP (\(ei,az,mz). mz) xs) < dimword (:256)` by
    asm_rewrite_tac[GSYM calldata_tuple_size, calldata_fixed_tuple_size] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  qpat_x_assum `xs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  disch_tac >>
  mp_tac (Q.INST [`tvs` |-> `REPLICATE n tv`,
    `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`] calldata_complex_tuple_owned_run_tail) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      (rename1 `LENGTH (REPLICATE _ _) = LENGTH _` >> simp[LENGTH_REPLICATE]),
      (rpt gen_tac >> strip_tac >>
       `EL i (REPLICATE n tv) = tv` by simp[EL_REPLICATE] >>
       asm_rewrite_tac[] >>
       qpat_x_assum `!i a mid b ep dp ei az mz. _`
         (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
       disch_then (qspecl_then [`i`, `a`, `az`, `mz`] mp_tac) >>
       asm_rewrite_tac[])])) >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >- (disj1_tac >> qexistsl_tac [`fuel`, `z`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all calldata_fixed_tuple_repack >> strip_tac >>
  qexistsl_tac [`t`, `y`, `scratch`] >>
  asm_rewrite_tac[GSYM calldata_fixed_tuple_size]
QED
