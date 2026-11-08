Theory exprSimAbiEncodeStopObserver
Ancestors
  abiArgsObservation abiEncoderObserver fragExec venomWf venomInst unitShapeDefs
  exprSimAbiEncodeRegionTransfer list rich_list sorting

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
