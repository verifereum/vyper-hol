(* An installed instruction outside the fragment identifies its exit PC. *)
Theory rawSlotFetchExit
Ancestors
  abiEncoderProps compileEnv venomExecSemantics venomInst venomState

Theorem slot_fetch_off_exit:
  lookup_block b.cs_current_bb f.fn_blocks = SOME bb_exit /\
  get_instruction bb_exit (LENGTH b.cs_current_insts) = SOME i_exit /\
  i_exit.inst_id NOTIN frag_ids a b ==>
  !p blk i.
    lookup_block p.vs_current_bb f.fn_blocks = SOME blk /\
    get_instruction blk p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids a b ==>
    (p.vs_current_bb <> b.cs_current_bb \/
     p.vs_inst_idx <> LENGTH b.cs_current_insts)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `p.vs_current_bb = b.cs_current_bb` >>
  Cases_on `p.vs_inst_idx = LENGTH b.cs_current_insts` >> gvs[] >>
  metis_tac[]
QED
