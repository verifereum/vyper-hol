Theory dftPacketReturnOrder
Ancestors
  dftPacketReturnActivation dftIndexedExec dftGasFromListTraceDefs
  venomExecProofs venomExecSemantics venomWf venomInst venomState
  finite_map list rich_list arithmetic sorting

Theorem return_order_indices:
  order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
  i < LENGTH order ==>
  EL i order = inc + SUC i /\
  (EL i order = LAST order <=> SUC i = LENGTH order) /\
  (SUC i < LENGTH order ==> EL (SUC i) order - 1 = EL i order)
Proof
  strip_tac >>
  `0 < LENGTH order` by (Cases_on `order` >> gvs[]) >>
  `EL i order = inc + SUC i /\
   (SUC i < LENGTH order ==> EL (SUC i) order = inc + SUC (SUC i))` by
    (conj_tac
     >- (qpat_assum `order = GENLIST _ _` (fn th => simp[Once th,EL_GENLIST])) >>
     strip_tac >>
     qpat_assum `order = GENLIST _ _` (fn th => simp[Once th,EL_GENLIST])) >>
  `LAST order = inc + LENGTH order` by
    (qpat_assum `order = GENLIST _ _` (fn th => rewrite_tac[Once th]) >>
     Cases_on `LENGTH order` >> gvs[GENLIST_LAST]) >>
  simp[] >> decide_tac
QED

Theorem return_order_row_shape:
  wf_function sf /\ wf_function tf /\
  lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis in_state bt.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons g D) OK
    (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be ==>
  lookup_block in_state.vs_current_bb tf.fn_blocks = SOME bt /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
  ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
  eval_phis in_state ps = OK sp /\
  FOLDR (dft_exec_cons g D) OK (DROP (phi_prefix_length ps) ps)
    (sp with vs_inst_idx := phi_prefix_length ps) = OK be
Proof
  strip_tac >>
  `bb.bb_label = in_state.vs_current_bb` by
    metis_tac[lookup_block_label] >>
  `MEM bb sf.fn_blocks /\ MEM bt tf.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb /\ bb_well_formed bt` by
    metis_tac[wf_function_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
     simp[] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def,is_terminator_def]) >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode /\
   bt.bb_instructions <> [] /\
   is_terminator (LAST bt.bb_instructions).inst_opcode` by
    metis_tac[bb_well_formed_def] >>
  `xs <> [] /\ ys <> []` by
    (conj_tac
     >- (strip_tac >>
         qpat_x_assum `EVERY (\i. ~is_terminator i.inst_opcode) ps`
           (qspec_then `LAST ps` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
         gvs[MEM_LAST_NOT_NIL]) >>
     strip_tac >>
     qpat_x_assum `EVERY (\i. ~is_terminator i.inst_opcode) ps`
       (qspec_then `LAST ps` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
     gvs[MEM_LAST_NOT_NIL]) >>
  `EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  gvs[LAST_APPEND_NOT_NIL,dft_eval_phis_append,dft_phi_prefix_append]
QED
