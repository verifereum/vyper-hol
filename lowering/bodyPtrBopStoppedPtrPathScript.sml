Theory bodyPtrBopStoppedPtrPath
Ancestors
  bodyPtrBopStoppedPath fragGasPathPtr

Theorem gas_path_ptr_stopped_transport:
  (!G tn s n H un r. stop s ==>
    ~gas_path_ptr_edge D lo ctx f PG G tn s n H un r) /\
  (!G tn s n H un r. ~stop s /\
    gas_path_ptr_edge D lo ctx f PG G tn s n H un r ==>
    gas_path_ptr_edge D lo ctx g PG G tn s n H un r) /\
  gas_path_ptr D lo ctx f PG G tn s k H un r ==>
  gas_path_ptr D lo ctx g PG G tn s k H un r
Proof
  strip_tac >>
  qpat_x_assum `!G tn s n H un r. ~stop s /\ _ ==> _` mp_tac >>
  qpat_x_assum `!G tn s n H un r. stop s ==> _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  map_every qid_spec_tac
    [`r`, `un`, `H`, `k`, `s`, `tn`, `G`, `PG`, `f`, `ctx`, `lo`, `D`] >>
  ho_match_mp_tac gas_path_ptr_ind >> metis_tac[gas_path_ptr_rules]
QED

(* An ordinary stopped endpoint also blocks every pointer edge, regardless
   of its ghost and taint, by the existing erasure interface. *)
Theorem gas_path_ptr_edge_no_instruction:
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
        get_instruction bb s.vs_inst_idx = NONE) ==>
  ~gas_path_ptr_edge D lo ctx fn PG G tn s n H un r
Proof
  metis_tac[gas_path_edge_no_instruction, gas_path_ptr_edge_erase]
QED
