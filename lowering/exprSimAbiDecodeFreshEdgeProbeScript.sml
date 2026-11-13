Theory exprSimAbiDecodeFreshEdgeProbe
Ancestors
  exprSimAbiGasBridge

Theorem abi_decode_fresh_observer_witness:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) ==>
  ?L ids fn'.
    LENGTH ids = LENGTH sa.cs_current_insts /\ L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb) /\
    fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
    fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
    (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
         i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
    (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
    (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule_all frag_relabel_observer_exists >> strip_tac >>
  qexistsl_tac [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] >>
  simp[frag_relabel_observer_def]
QED
