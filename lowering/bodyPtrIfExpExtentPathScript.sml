Theory bodyPtrIfExpExtentPath
Ancestors fragGasPathPtr bodyPtrIfExpWriterTransport

Theorem ifexp_path_ghost_invariant:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !P. (!H u t k H' u' result.
      P H /\ gas_path_ptr_edge D lo ctx fn PG H u t k H' u' result ==>
      P H') ==> P G ==> P G'
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt strip_tac >> metis_tac[]
QED

Theorem ifexp_path_extent:
  !D lo ctx fn PG G tn s n G' tn' r p sz.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r /\
    (?b. FLOOKUP G p = SOME (b,sz)) /\
    (!H u t k H' u' result.
      (?b. FLOOKUP H p = SOME (b,sz)) /\
      gas_path_ptr_edge D lo ctx fn PG H u t k H' u' result ==>
      ?b. FLOOKUP H' p = SOME (b,sz)) ==>
    ?b. FLOOKUP G' p = SOME (b,sz)
Proof
  rpt strip_tac >> drule ifexp_path_ghost_invariant >>
  disch_then (qspec_then `\H. ?b. FLOOKUP H p = SOME (b,sz)` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_edge_extent:
  !D lo ctx fn PG G tn s n G' tn' t p sz.
    gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
    (?b. FLOOKUP G p = SOME (b,sz)) /\
    (!u bb i. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
      ~MEM p i.inst_outputs) /\
    (!fuel bb inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst ==>
      ~MEM p inst.inst_outputs \/
      ?b. FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) p =
          SOME (b,sz)) ==>
    ?b. FLOOKUP G' p = SOME (b,sz)
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def, fragExecTheory.exit_result_def] >>
  metis_tac[ifexp_ghost_nonwriter, ifexp_entry_nonwriter, pairTheory.FST]
QED
