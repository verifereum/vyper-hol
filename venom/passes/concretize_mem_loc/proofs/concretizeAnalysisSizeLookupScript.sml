Theory concretizeAnalysisSizeLookup
Ancestors
  concretizeMemLocDefs venomInst venomWf finite_map list

Theorem find_by_inst_id_alt:
  !Q l inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM inst l /\ Q inst ==>
    FIND (\i. Q i /\ i.inst_id = inst.inst_id) l = SOME inst
Proof
  gen_tac >> Induct >> simp[FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[ALL_DISTINCT_APPEND, MEM_MAP]
QED

Theorem get_alloca_size_from_inst:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest ==>
  get_alloca_size fn (Allocation inst.inst_id) = w2n n
Proof
  strip_tac >> simp[get_alloca_size_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)))` by
    gvs[fn_inst_ids_distinct_def, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `MEM inst (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))` by
    (`!bbs. fn_insts_blocks bbs =
            FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
       (Induct >> simp[fn_insts_blocks_def]) >>
     gvs[fn_insts_def]) >>
  `FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_id = inst.inst_id)
    (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) = SOME inst` by
    (match_mp_tac (find_by_inst_id_alt |> Q.SPEC `is_alloca_op o inst_opcode`
       |> SIMP_RULE (srw_ss()) []) >> simp[is_alloca_op_def]) >> simp[]
QED
