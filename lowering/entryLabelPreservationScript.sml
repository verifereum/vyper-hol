(* Label-only compilation interfaces, independent of opcode/environment shape. *)
Theory entryLabelPreservation
Ancestors
  loweringShapeDefs loweringShapeProps compileEnv fragExec abiDecoderAppend
  abiEncoder emitHelper list

Theorem added_labels_compose:
  cs_extends a b /\ cs_extends b c ==>
  added_labels a c = added_labels a b ++ added_labels b c
Proof
  strip_tac >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  imp_res_tac block_labels_cs_extends >> gvs[]
QED

Theorem label_extends_trans:
  cs_extends a b /\ EVERY LP (added_labels a b) /\
  cs_extends b c /\ EVERY LP (added_labels b c) ==>
  cs_extends a c /\ EVERY LP (added_labels a c)
Proof
  metis_tac[added_labels_compose, EVERY_APPEND, cs_extends_trans]
QED

Theorem added_labels_new_block:
  new_block lbl st = (old, st') ==> added_labels st st' = [lbl]
Proof
  strip_tac >> gvs[new_block_def] >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_APPEND,
       LENGTH_MAP]
QED

Theorem added_labels_emit_inst:
  emit_inst opc ops outs st = (r, st') ==> added_labels st st' = []
Proof
  strip_tac >>
  gvs[emit_inst_def, fresh_id_def, comp_bind_def, comp_return_def,
      emit_def] >>
  simp[added_labels_def, all_blocks_def, LENGTH_MAP]
QED

