Theory exprSimAbiDecodeSiteCoverage
Ancestors
  exprSimAbiGasBridge exprSimAbiDecodeSuffixWrites emitHelper compileEnv
  venomInst list rich_list fragExec arithmetic ASCIInumbers exprLoweringProps

(* Primitive probes: emitted operations account for their entire ID interval.
   fresh_id alone deliberately does not: certificates must combine it with emit. *)
Theorem abi_decode_emit_op_interval:
  emit_op opc ops a = (out,b) ==>
  !id. a.cs_next_id <= id /\ id < b.cs_next_id ==>
    ?i. MEM i (frag_code a b) /\ i.inst_id = id /\
      !q. MEM q i.inst_outputs ==>
        ?n. a.cs_next_var <= n /\ q = STRING #"%" (toString n)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `id = a.cs_next_id` by decide_tac >> gvs[] >>
  qexists_tac `mk_inst a.cs_next_id opc ops [STRING #"%" (toString a.cs_next_var)]` >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND,
       mk_inst_def]
QED

Theorem abi_decode_emit_void_interval:
  emit_void opc ops a = (out,b) ==>
  !id. a.cs_next_id <= id /\ id < b.cs_next_id ==>
    ?i. MEM i (frag_code a b) /\ i.inst_id = id /\ i.inst_outputs = []
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  `id = a.cs_next_id` by decide_tac >> gvs[] >>
  qexists_tac `mk_inst a.cs_next_id opc ops []` >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND,
       mk_inst_def]
QED

Theorem abi_decode_new_block_counters:
  new_block label a = (old,b) ==>
  b.cs_next_id = a.cs_next_id /\ b.cs_next_var = a.cs_next_var
Proof
  simp[new_block_def] >> strip_tac >> gvs[]
QED

Theorem abi_decode_entry_reservation_transport:
  local_ptrs_reserved ce a /\ ci_mono a b /\ ci_mono b c ==>
  local_ptrs_reserved ce c
Proof
  strip_tac >> irule local_ptrs_reserved_next_var >>
  qexists_tac `a` >> fs[ci_mono_def] >> decide_tac
QED

Theorem abi_decode_coverage_front_append[local]:
  ys <> [] ==> FRONT (xs ++ ys) = xs ++ FRONT ys
Proof
  Cases_on `ys` >- simp[] >>
  strip_tac >> MATCH_ACCEPT_TAC FRONT_APPEND
QED

Theorem abi_decode_coverage_sub_add[local]:
  !a b:num. a - (b + a) = 0
Proof
  decide_tac
QED

Theorem abi_decode_coverage_drop_long[local]:
  !xs k. DROP (k + LENGTH xs) xs = []
Proof
  simp[DROP_EQ_NIL]
QED

Theorem abi_decode_frag_code_compose:
  cs_extends a b /\ cs_extends b c ==>
  !i. (MEM i (frag_code a c) <=>
       MEM i (frag_code a b) \/ MEM i (frag_code b c))
Proof
  strip_tac >> gen_tac >> eq_tac
  >- metis_tac[abi_decode_frag_code_split] >>
  fs[cs_extends_def] >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  `emitted_blocks b c = new'` by metis_tac[emitted_blocks_append] >>
  `emitted_blocks a c = new' ++ new` by
    (irule emitted_blocks_append >> simp[APPEND_ASSOC]) >>
  Cases_on `new = []` >> Cases_on `new' = []` >>
  gvs[frag_code_def, NULL_EQ, emitted_insts_def, LAST_APPEND_NOT_NIL,
      abi_decode_coverage_front_append, MEM_APPEND, MEM_FLAT, MEM_MAP, IS_PREFIX_APPEND,
      DROP_APPEND, APPEND_ASSOC, SUB_EQ_0] >>
  simp[abi_decode_coverage_front_append, abi_decode_coverage_sub_add,
       abi_decode_coverage_drop_long, MEM_APPEND, MEM_FLAT, MEM_MAP]
  >- metis_tac[] >>
  `MEM (LAST (emitted_blocks b c)) (emitted_blocks b c)` by
    simp[MEM_LAST_NOT_NIL] >>
  `!bb. MEM bb (FRONT (emitted_blocks b c)) ==>
        MEM bb (emitted_blocks b c)` by metis_tac[MEM_FRONT_NOT_NIL] >>
  metis_tac[MEM_APPEND]
QED

Theorem abi_decode_frag_code_left_inclusion:
  cs_extends a b /\ cs_extends b c /\ MEM i (frag_code a b) ==>
  MEM i (frag_code a c)
Proof
  metis_tac[abi_decode_frag_code_compose]
QED

Theorem abi_decode_frag_code_right_inclusion:
  cs_extends a b /\ cs_extends b c /\ MEM i (frag_code b c) ==>
  MEM i (frag_code a c)
Proof
  metis_tac[abi_decode_frag_code_compose]
QED
