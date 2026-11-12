Theory bodyPtrBopInLoopLookups
Ancestors bodyPtrBopInLoopLayout fragExec abiDecoderLoopCode
  abiEncoderExitPhi typedCopyArrayPtr venomExecSemantics venomInst list

(* The layout theorem supplies this six-block spine. No label-freshness
   hypothesis is needed: containment already promises these exact lookups. *)
Theorem membership_loop_code:
  !sa sb fn old entry cond loop_bb found incr.
    sb.cs_blocks = [incr;found;loop_bb;cond;entry;old] ++ sa.cs_blocks /\
    fn_has_code sa sb fn ==>
    lookup_block old.bb_label fn.fn_blocks = SOME old /\
    lookup_block entry.bb_label fn.fn_blocks = SOME entry /\
    lookup_block cond.bb_label fn.fn_blocks = SOME cond /\
    lookup_block loop_bb.bb_label fn.fn_blocks = SOME loop_bb /\
    lookup_block found.bb_label fn.fn_blocks = SOME found /\
    lookup_block incr.bb_label fn.fn_blocks = SOME incr /\
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX sb.cs_current_insts bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_blocks sa sb = [incr;found;loop_bb;cond;entry;old]` by
    (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >> metis_tac[MEM]
QED

(* A nonempty generated head suffices even at an unfinished exit.
   In's empty prefix deliberately does not satisfy this interface. *)
Theorem membership_nonphi_prefix_entry:
  !fn s bb id opc args outs tail G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (mk_inst id opc args outs :: tail) bb.bb_instructions /\
    opc <> PHI ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  rpt gen_tac >> strip_tac >> irule entry_ghost_no_phi >>
  qexists_tac `bb` >> simp[] >>
  irule abi_encoder_nonempty_prefix_phi >>
  qexists_tac `mk_inst id opc args outs :: tail` >>
  simp[phi_prefix_length_def, mk_inst_def]
QED
