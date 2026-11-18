Theory dftPacketFreshBodyObservation
Ancestors
  dftPacketObservationSuccess dftGasFromListReplayBoundary dftGasFromListTraceDefs
  dftRunRel dftIndexedExec dftStructural dftWf venomWf venomExecSemantics venomInst
  list rich_list arithmetic

Theorem fresh_gas_cells[local]:
  !xs q f. FLAT (TAKE q (GENLIST
    (\r. if (EL r xs).inst_opcode = GAS then [f (EL r xs)] else [])
    (LENGTH xs))) = MAP f (FILTER (\i. i.inst_opcode = GAS) (TAKE q xs))
Proof
  rpt gen_tac >>
  `GENLIST (\r. if (EL r xs).inst_opcode = GAS then [f (EL r xs)] else [])
    (LENGTH xs) = MAP (\i. if i.inst_opcode = GAS then [f i] else []) xs` by
    simp[LIST_EQ_REWRITE,EL_MAP,EL_GENLIST] >>
  simp[GSYM MAP_TAKE] >>
  qspec_tac (`TAKE q xs`,`ls`) >> Induct >> simp[] >>
  gen_tac >> Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Theorem fresh_gas_keys[local]:
  !xs a e. ALL_DISTINCT (MAP (\i:instruction. i.inst_id) xs) ==>
    ALL_DISTINCT (MAP (\i. (a,e,i.inst_id))
      (FILTER (\i. i.inst_opcode = GAS) xs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = GAS` >> gvs[MEM_MAP,MEM_FILTER] >> metis_tac[]
QED

Theorem dft_packet_fresh_body_observation:
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv sf bb xs be /\ be.vs_inst_idx = LENGTH ps /\
  ys <> [] /\ ci = HD ys /\ q < LENGTH xs /\ EL q xs = ci /\
  inv_memory_observation ci.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(a,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) gs /\
  FOLDR (dft_exec_cons fuel C7) OK (TAKE q xs)
    (be with vs_gas_readings := gs ++ tail) = OK u /\
  trace_gas (trace_block a e fuel C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions)
    (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT (TAKE q ks),gs) ==>
  (!op. MEM op ci.inst_operands ==> eval_operand op u = eval_operand op be) /\
  u.vs_initial_fmp = be.vs_initial_fmp
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    metis_tac[dft_fn_rel_def,wf_fn_block_inst_ids_distinct,MAP_APPEND,ALL_DISTINCT_APPEND] >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (gvs[fresh_gas_cells] >> irule fresh_gas_keys >>
     metis_tac[GSYM MAP_TAKE,ALL_DISTINCT_TAKE]) >>
  `LENGTH (FLAT (TAKE q ks)) = LENGTH gs` by
    (drule LIST_REL_LENGTH >> simp[fresh_gas_cells]) >>
  `trace_gas (trace_block a e fuel C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) be) = []` by
    simp[Once trace_defs,get_instruction_def,LENGTH_TAKE,trace_gas_def] >>
  qspecl_then [`[]`,`FLAT (TAKE q ks)`,`gs`,
    `trace_block a e fuel C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions)
      (be with vs_gas_readings := gs ++ tail)`,
    `trace_block a e fuel C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) be`]
    mp_tac trace_agrees_lookup_fill >>
  simp[EVERY_MEM,pairTheory.FORALL_PROD] >> strip_tac >>
  `xs = TAKE q xs ++ ci::DROP (SUC q) xs` by
    (qspecl_then [`xs`,`q`] mp_tac DROP_EL_CONS >> simp[ADD1] >>
     metis_tac[TAKE_DROP,APPEND,APPEND_ASSOC]) >>
  `ys = ci::TL ys` by (Cases_on `ys` >> gvs[]) >>
  irule dft_packet_native_observation_success >>
  (conj_tac >- gvs[]) >>
  goal_assum (drule_at (Pat `LIST_REL _ _ _`)) >>
  goal_assum (drule_at (Pat `dft_fn_rel _ _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME bb`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME bt`)) >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  qexistsl [`e`,`TL ys`,
    `\key. case ALOOKUP (ZIP (FLAT (TAKE q ks),gs)) key of NONE => 0w | SOME w => w`,
    `a`,`DROP (SUC q) xs`,`ps`,`[]`,`fuel`,`ci`] >>
  simp[GSYM MAP_TAKE] >>
  `TAKE q xs ++ HD ys::DROP (SUC q) xs = xs` by metis_tac[] >>
  reverse conj_tac >-
    (conj_tac >-
       (qpat_x_assum `TAKE q xs ++ HD ys::DROP (SUC q) xs = xs`
          (fn th => qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs`
            (mp_tac o PURE_ONCE_REWRITE_RULE [GSYM th])) >> simp[]) >>
     simp[]) >>
  metis_tac[APPEND,APPEND_ASSOC]
QED
