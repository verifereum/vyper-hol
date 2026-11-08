Theory exprSimAbiEncodeStopObserver
Ancestors
  abiArgsObservation abiEncoderObserver fragExec venomWf venomInst unitShapeDefs
  exprSimAbiEncodeRegionTransfer list rich_list sorting
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  abiBuiltinEncodeCode emitHelper compileEnv exprSimAbiEncodeOblivious
  exprSimAbiEncodeSourceRoom

(* Replace, rather than duplicate, the endpoint block.  In particular the
   old endpoint prefix must not occur twice in the instruction-ID list. *)
Definition abi_encode_stop_observer_def:
  abi_encode_stop_observer fn sb id =
    fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> ::
      FILTER (\bb. bb.bb_label <> sb.cs_current_bb) fn.fn_blocks
End

Theorem abi_encode_stop_lookup_filter[local]:
  !blocks lbl endlabel.
    lbl <> endlabel ==>
    lookup_block lbl (FILTER (\bb. bb.bb_label <> endlabel) blocks) =
    lookup_block lbl blocks
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt strip_tac >>
  Cases_on `h.bb_label = endlabel` >> simp[] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def, FIND_thm]
QED

Theorem abi_encode_stop_contains:
  fn_has_code sa sb fn /\
  (!bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb) ==>
  fn_has_code sa sb (abi_encode_stop_observer fn sb id)
Proof
  rewrite_tac[fn_has_code_def] >> strip_tac >> conj_tac
  >- (qx_gen_tac `ebb` >> strip_tac >>
      `ebb.bb_label <> sb.cs_current_bb` by metis_tac[] >>
      `lookup_block ebb.bb_label fn.fn_blocks = SOME ebb` by metis_tac[] >>
      simp_tac bool_ss [abi_encode_stop_observer_def, ir_function_accfupds] >>
      once_rewrite_tac[lookup_block_def] >> simp[FIND_thm] >>
      rewrite_tac[GSYM lookup_block_def] >>
      simp[abi_encode_stop_lookup_filter]) >>
  simp[abi_encode_stop_observer_def, lookup_block_def, FIND_thm,
       IS_PREFIX_APPEND]
QED

Theorem abi_encode_stop_endpoint:
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  lookup_block t.vs_current_bb (abi_encode_stop_observer fn sb id).fn_blocks =
    SOME <|bb_label := sb.cs_current_bb;
           bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> /\
  get_instruction
    <|bb_label := sb.cs_current_bb;
      bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>
    t.vs_inst_idx = SOME (mk_inst id STOP [] [])
Proof
  simp[abi_encode_stop_observer_def, lookup_block_def, FIND_thm,
       get_instruction_def, EL_APPEND2]
QED

Theorem abi_encode_stop_sim_run:
  abi_decode_sim ctx (abi_encode_stop_observer fn sb id) s t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?fuel. run_from fuel ctx (abi_encode_stop_observer fn sb id) s =
    Halt (stop_view t)
Proof
  strip_tac >> drule_all abi_encode_stop_endpoint >> strip_tac >>
  irule abi_decode_sim_stop_run >> metis_tac[]
QED

Theorem abi_encode_stop_opcode_inclusion:
  fn_has_code sa sb fn /\
  MEM i (fn_insts (abi_encode_stop_observer fn sb id)) /\
  i.inst_opcode <> STOP ==> MEM i (fn_insts fn)
Proof
  simp[fn_insts_def, fn_insts_blocks_def, abi_encode_stop_observer_def,
       MEM_FLAT, MEM_MAP, MEM_FILTER] >> strip_tac
  >- (gvs[mk_inst_def] >>
      qpat_x_assum `fn_has_code _ _ _` mp_tac >>
      simp[fn_has_code_def] >> strip_tac >>
      gvs[IS_PREFIX_APPEND] >>
      metis_tac[fn_insts_def, lookup_block_fn_insts, MEM_APPEND])
  >- gvs[mk_inst_def] >>
  gvs[MEM_fn_insts_blocks_iff, MEM_FILTER] >> metis_tac[]
QED

Theorem abi_encode_stop_no_invoke:
  fn_has_code sa sb fn /\
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> INVOKE) ==>
  !i. MEM i (fn_insts (abi_encode_stop_observer fn sb id)) ==>
    i.inst_opcode <> INVOKE
Proof
  rpt strip_tac >> Cases_on `i.inst_opcode = STOP` >- gvs[] >>
  drule_all abi_encode_stop_opcode_inclusion >> metis_tac[]
QED

Theorem abi_encode_stop_partition_distinct[local]:
  ALL_DISTINCT (FLAT (MAP f xs)) ==>
  ALL_DISTINCT (FLAT (MAP f (FILTER P xs)) ++
                FLAT (MAP f (FILTER (\b. ~P b) xs)))
Proof
  strip_tac >>
  `PERM xs (FILTER P xs ++ FILTER (\b. ~P b) xs)` by
    (simp[GSYM combinTheory.o_DEF, PERM_SPLIT]) >>
  `PERM (FLAT (MAP f xs))
    (FLAT (MAP f (FILTER P xs ++ FILTER (\b. ~P b) xs)))` by
    (irule PERM_FLAT >> irule PERM_MAP >> first_assum ACCEPT_TAC) >>
  gvs[MAP_APPEND, FLAT_APPEND] >> metis_tac[ALL_DISTINCT_PERM]
QED

Theorem abi_encode_stop_find_prefix[local]:
  !xs. FIND P xs = SOME b ==>
    isPREFIX (f b) (FLAT (MAP f (FILTER P xs)))
Proof
  Induct >> simp[FIND_thm] >>
  Cases_on `P h` >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[IS_PREFIX_APPEND]
QED

Theorem abi_encode_stop_prefix_distinct[local]:
  ALL_DISTINCT (FLAT (MAP f xs)) /\ FIND P xs = SOME b /\
  isPREFIX pre (f b) ==>
  ALL_DISTINCT (pre ++ FLAT (MAP f (FILTER (\b. ~P b) xs)))
Proof
  strip_tac >> drule abi_encode_stop_partition_distinct >>
  disch_then (qspec_then `P` assume_tac) >>
  `isPREFIX (f b) (FLAT (MAP f (FILTER P xs)))` by
    (irule abi_encode_stop_find_prefix >> first_assum ACCEPT_TAC) >>
  `isPREFIX pre (FLAT (MAP f (FILTER P xs)))` by metis_tac[IS_PREFIX_TRANS] >>
  gvs[IS_PREFIX_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem abi_encode_stop_distinct:
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) ==> i.inst_id <> id) ==>
  fn_inst_ids_distinct (abi_encode_stop_observer fn sb id)
Proof
  strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  rewrite_tac[fn_has_code_def] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sb.cs_current_insts ++
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FILTER (\bb. bb.bb_label <> sb.cs_current_bb) fn.fn_blocks)))` by
    (ho_match_mp_tac (Q.GEN `b` abi_encode_stop_prefix_distinct) >>
     qexists `bb` >>
     gvs[fn_inst_ids_distinct_def, lookup_block_def] >>
     gvs[IS_PREFIX_APPEND, MAP_APPEND] >> simp[IS_PREFIX_APPEND]) >>
  simp[fn_inst_ids_distinct_def, abi_encode_stop_observer_def,
       MAP_APPEND, mk_inst_def, ALL_DISTINCT_APPEND] >>
  gvs[ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (gvs[MEM_MAP, IS_PREFIX_APPEND] >>
      metis_tac[lookup_block_fn_insts, MEM_APPEND]) >>
  rpt strip_tac >- metis_tac[] >>
  gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff]
QED

Theorem abi_encode_stop_noncollision:
  entry_shape sa sb /\ fn_has_code sa sb fn /\
  EVERY (\i. i.inst_opcode = NOP) sa.cs_current_insts /\
  EXISTS (\i. i.inst_opcode <> NOP) sb.cs_current_insts /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) ==>
  !bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb
Proof
  rewrite_tac[entry_shape_def] >> strip_tac
  >- gvs[emitted_blocks_def] >>
  `emitted_blocks sa sb = front ++
    [<|bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++ tail|>]` by
    simp[emitted_blocks_def, TAKE_APPEND] >>
  gvs[FRONT_APPEND, MEM_MAP] >> rpt strip_tac
  >- metis_tac[] >>
  gvs[fn_has_code_def] >>
  qpat_x_assum `!bb. _ ==> lookup_block _ _ = SOME bb` (qspec_then
    `<|bb_label := sb.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++ tail|>` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[frag_code_def, LAST_APPEND, FRONT_APPEND, MAP_APPEND,
      ALL_DISTINCT_APPEND, IS_PREFIX_APPEND, EXISTS_MEM, EVERY_MEM] >>
  `MEM i tail` by metis_tac[MEM_APPEND] >>
  `DROP (LENGTH sa.cs_current_insts) (sb.cs_current_insts ++ l) = tail` by
    metis_tac[DROP_LENGTH_APPEND] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem abi_encode_stop_endpoint_non_nop:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) ==>
  EXISTS (\i. i.inst_opcode <> NOP) sb.cs_current_insts
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
  simp[abi_builtin_encode_finish_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[mk_inst_def]
QED

Theorem abi_encode_stop_lower_noncollision:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  fn_has_code sa sb fn /\
  EVERY (\i. i.inst_opcode = NOP) sa.cs_current_insts ==>
  !bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb
Proof
  strip_tac >> drule lower_abi_encode_structural_facts >> strip_tac >>
  drule abi_encode_stop_endpoint_non_nop >> strip_tac >>
  `code_step enc_safe_opcode sa sb` by
    metis_tac[code_action_lower_abi_encode, code_action_def] >>
  gvs[code_step_def] >> metis_tac[abi_encode_stop_noncollision]
QED

Theorem abi_encode_stop_relabel_contains:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn ==>
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb)
    (abi_encode_stop_observer fn (start_swap sa L ids sb) id)
Proof
  strip_tac >>
  `lower_abi_encode ensure mid src info maxlen (start_relabel L ids sa) =
    (out,start_swap sa L ids sb)` by
    metis_tac[lower_abi_encode_start_oblivious, frag_start_oblivious_def] >>
  `EVERY (\i. i.inst_opcode = NOP) (start_relabel L ids sa).cs_current_insts` by
    (simp[start_relabel_def, EVERY_MEM, MEM_MAP, mk_inst_def] >>
     rpt strip_tac >> gvs[]) >>
  irule abi_encode_stop_contains >>
  metis_tac[abi_encode_stop_lower_noncollision]
QED

Theorem abi_encode_stop_room:
  fn_has_code sa sb obs /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) ==> i.inst_id <> id) /\
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
     MEM i (fn_insts func)) ==>
  alloca_room (ctx with ctx_functions := [abi_encode_stop_observer obs sb id])
    (abi_encode_stop_observer obs sb id) s
Proof
  strip_tac >>
  `fn_inst_ids_distinct (abi_encode_stop_observer obs sb id)` by
    (irule abi_encode_stop_distinct >> metis_tac[]) >>
  irule abi_encode_bridge_local_room >> simp[] >>
  qexists `func` >>
  reverse conj_tac >- simp[abi_encode_stop_observer_def] >>
  rpt strip_tac >> drule_all abi_encode_stop_opcode_inclusion >> metis_tac[]
QED
