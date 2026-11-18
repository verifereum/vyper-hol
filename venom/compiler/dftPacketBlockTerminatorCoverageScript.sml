Theory dftPacketBlockTerminatorCoverage
Ancestors
  dftRunRel dftCorrectness dftStructural dftDefs venomExecProps
  venomWf venomInst list rich_list sorting arithmetic

(* A permutation ending in a non-call has already selected every call. *)
Theorem terminal_schedule_invoke_coverage[local]:
  !schedule k (xs:instruction list).
    PERM schedule (COUNT_LIST (LENGTH xs)) /\
    SUC k = LENGTH schedule /\
    (EL (EL k schedule) xs).inst_opcode <> INVOKE ==>
    !r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE k schedule)
Proof
  map_every qx_gen_tac [`schedule`,`k`,`xs`] >> strip_tac >>
  qx_gen_tac `r` >> strip_tac >>
  `MEM r schedule` by
    (drule PERM_MEM_EQ >>
     disch_then (qspec_then `r` mp_tac) >>
     simp[MEM_COUNT_LIST]) >>
  `schedule = TAKE k schedule ++ [EL k schedule]` by
    (qspecl_then [`schedule`,`k`] mp_tac TAKE_EL_SNOC >>
     simp[SNOC_APPEND, GSYM ADD1]) >>
  `MEM r (TAKE k schedule ++ [EL k schedule])` by metis_tac[] >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem dft_packet_block_terminator_invoke_coverage:
  !sf tf bb bt ps xs ys schedule k inst.
    tf = dft_fn sf /\ dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
    EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
    LENGTH xs = LENGTH ys /\
    PERM schedule (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
                    from_block [EL q xs] y) schedule ys /\
    k < LENGTH ys /\ inst = EL k ys /\ is_terminator inst.inst_opcode ==>
    SUC k = LENGTH ys /\
    !r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE k schedule)
Proof
  map_every qx_gen_tac [`sf`,`tf`,`bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,`k`,`inst`] >>
  strip_tac >>
  `bb_well_formed bt` by
    (irule dft_fn_blocks_well_formed >> qexists `sf` >>
     metis_tac[dft_fn_rel_def, venomExecPropsTheory.lookup_block_MEM]) >>
  `LENGTH ps + k = PRE (LENGTH ps + LENGTH ys)` by
    (qpat_x_assum `bb_well_formed bt` mp_tac >>
     simp[bb_well_formed_def] >> strip_tac >>
     qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + k` mp_tac) >>
     fs[EL_APPEND2] >> metis_tac[]) >>
  `SUC k = LENGTH ys` by decide_tac >>
  `LENGTH schedule = LENGTH ys /\ from_block [EL (EL k schedule) xs] inst` by
    (qpat_x_assum `LIST_REL _ schedule ys` mp_tac >>
     simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `(EL (EL k schedule) xs).inst_opcode <> INVOKE` by
    (qpat_x_assum `from_block _ inst` mp_tac >>
     simp[from_block_def] >>
     metis_tac[flip_operands_is_terminator, EVAL ``is_terminator INVOKE``]) >>
  conj_tac >- simp[] >>
  qspecl_then [`schedule`,`k`,`xs`] mp_tac terminal_schedule_invoke_coverage >>
  simp[]
QED
