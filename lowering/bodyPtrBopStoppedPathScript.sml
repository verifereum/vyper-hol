Theory bodyPtrBopStoppedPath
Ancestors
  fragGasPath

Theorem gas_path_edge_no_instruction:
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
        get_instruction bb s.vs_inst_idx = NONE) ==>
  ~gas_path_edge ctx fn s n r
Proof
  simp[gas_path_edge_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem gas_path_no_edges:
  (!n r. ~gas_path_edge ctx fn s n r) /\
  gas_path ctx fn s k r ==> k = 0 /\ r = OK s
Proof
  strip_tac >>
  qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
  once_rewrite_tac[gas_path_cases] >> metis_tac[]
QED

Theorem gas_path_stopped_transport:
  (!s n r. stop s ==> ~gas_path_edge ctx f s n r) /\
  (!s n r. ~stop s /\ gas_path_edge ctx f s n r ==>
            gas_path_edge ctx g s n r) /\
  gas_path ctx f s k r ==> gas_path ctx g s k r
Proof
  strip_tac >>
  qpat_x_assum `!s n r. ~stop s /\ _ ==> _` mp_tac >>
  qpat_x_assum `!s n r. stop s ==> _` mp_tac >>
  qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
  map_every qid_spec_tac [`r`, `k`, `s`, `f`, `ctx`] >>
  ho_match_mp_tac gas_path_ind >>
  metis_tac[gas_path_rules]
QED
