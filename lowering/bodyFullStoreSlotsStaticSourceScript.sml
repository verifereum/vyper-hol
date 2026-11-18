(* Concrete compiler certificate for the canonical slots observer. *)
Theory bodyFullStoreSlotsStaticSource
Ancestors
  bodyFullStoreSlotsStaticLayout bodyFullStoreSlotsStaticObserver
  bodyFullStoreSlotsStaticWrites bodyFullStoreSlotsStaticStores
  bodyFullStoreSlotsStaticCode exprSimAbiEncodeObliviousCode
  exprSimAbiGasBridge aggregateCountedRawRelabel
  context compileEnv fragExec exprLoweringProps emitHelper
  venomInst venomInstProps venomWf venomExecSemantics list rich_list pred_set

Theorem store_slots_fragment_source_certificate:
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func ==>
  ?L ids id obs.
    LENGTH ids = LENGTH sa.cs_current_insts /\ ALL_DISTINCT ids /\
    ~MEM id ids /\
    (!i. MEM i (frag_code sa sb) ==>
      ~MEM i.inst_id ids /\ i.inst_id <> id) /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    (?a. a = start_relabel L ids sa /\
     ?b. b = start_swap sa L ids sb /\
      compile_store_slots cenv src dst ty tr a = ((),b) /\
      cs_extends a b /\ frag_code a b = frag_code sa sb /\
      frag_gas_free a b /\ fn_has_code a b obs /\
      fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
      frag_observer a b obs id = obs /\
      (sa.cs_blocks <> sb.cs_blocks ==>
        obs = frag_relabel_observer sa sb L ids func id) /\
      (sa.cs_blocks = sb.cs_blocks ==>
        obs = frag_observer a b func id) /\
      (!i l. MEM i (frag_code a b) /\
        (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
        MEM (Label l) i.inst_operands ==>
        l <> a.cs_current_bb /\
        ?bb. lookup_block l obs.fn_blocks = SOME bb /\
             phi_prefix_length bb.bb_instructions = 0) /\
      EVERY (\i. MEM i.inst_opcode
        [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;
         SSTORE;TSTORE;INVALID]) (frag_code a b) /\
      (!i x. MEM i (frag_code a b) /\ MEM x i.inst_outputs ==>
        ~not_fresh_at a x) /\
      (!i. MEM i (frag_code a b) /\
        (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
        i.inst_opcode = (if tr then TSTORE else SSTORE) /\
        ?p v u w. i.inst_operands = [p;v] /\ i.inst_outputs = [] /\
          emit_void (if tr then TSTORE else SSTORE) [p;v] u = ((),w) /\
          i = mk_inst u.cs_next_id (if tr then TSTORE else SSTORE) [p;v] [] /\
          cs_extends a u /\ cs_extends u w /\ cs_extends w b /\
          fn_has_code u w obs) /\
      ~MEM b.cs_current_bb
        (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b))) /\
      (!bb. MEM bb (FRONT (emitted_blocks a b)) ==>
        phi_prefix_length bb.bb_instructions = 0) /\
      a.cs_current_bb = L /\
      LENGTH a.cs_current_insts = LENGTH sa.cs_current_insts /\
      a.cs_next_var = sa.cs_next_var /\
      a.cs_next_label = sa.cs_next_label /\ a.cs_next_id = sa.cs_next_id /\
      b.cs_next_var = sb.cs_next_var /\
      b.cs_next_label = sb.cs_next_label /\ b.cs_next_id = sb.cs_next_id /\
      LENGTH b.cs_current_insts = LENGTH sb.cs_current_insts /\
      (sa.cs_blocks <> sb.cs_blocks ==>
        b.cs_current_bb = sb.cs_current_bb /\
        b.cs_current_insts = sb.cs_current_insts) /\
      (sa.cs_blocks = sb.cs_blocks ==>
        b.cs_current_bb = L /\
        b.cs_current_insts = MAP (\k. mk_inst k NOP [] []) ids ++
          DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts))
Proof
  rewrite_tac[UNWIND_THM2] >> strip_tac >>
  `!L ids. LENGTH ids = LENGTH sa.cs_current_insts ==>
    compile_store_slots cenv src dst ty tr (start_relabel L ids sa) =
      ((),start_swap sa L ids sb)` by
    metis_tac[store_slots_start_oblivious, frag_start_oblivious_def] >>
  `!L ids i l. LENGTH ids = LENGTH sa.cs_current_insts /\
    MEM i (frag_code (start_relabel L ids sa) (start_swap sa L ids sb)) /\
    (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
    MEM (Label l) i.inst_operands ==>
    l = (start_swap sa L ids sb).cs_current_bb \/
    MEM l (MAP (\bb. bb.bb_label)
      (FRONT (emitted_blocks (start_relabel L ids sa)
        (start_swap sa L ids sb))))` by
    metis_tac[store_slots_fragment_label_operand_target] >>
  drule store_slots_fragment_syntax_shape >> strip_tac >>
  drule_all (REWRITE_RULE [UNWIND_THM2] store_slots_canonical_observer_exists) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`L`, `ids`, `id`, `obs`] >> simp[] >>
  `compile_store_slots cenv src dst ty tr (start_relabel L ids sa) =
    ((),start_swap sa L ids sb)` by metis_tac[] >>
  drule store_slots_fragment_syntax_shape >> strip_tac >>
  `code_action (\opc. MEM opc
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;
     SSTORE;TSTORE;INVALID]) (compile_store_slots cenv src dst ty tr)` by
    simp[store_slots_code_family] >>
  `EVERY (\i. MEM i.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;
     SSTORE;TSTORE;INVALID]) (frag_code (start_relabel L ids sa)
       (start_swap sa L ids sb))` by
    (fs[code_action_def, code_step_def] >> metis_tac[]) >>
  drule store_slots_fragment_outputs_fresh >> strip_tac >>
  drule store_slots_fragment_store_site_code >> disch_then assume_tac >>
  gvs[] >> rpt strip_tac >> metis_tac[]
QED
