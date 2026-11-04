(* Label-only compilation interfaces, independent of opcode/environment shape. *)
Theory entryLabelPreservation
Ancestors
  loweringShapeDefs loweringShapeProps compileEnv fragExec abiDecoderAppend
  abiEncoder list

Theorem added_labels_compose:
  cs_extends a b /\ cs_extends b c ==>
  added_labels a c = added_labels a b ++ added_labels b c
Proof
  strip_tac >>
  drule block_labels_cs_extends >> strip_tac >>
  drule_at (Pos last) block_labels_cs_extends >> strip_tac >>
  simp[added_labels_def] >>
  asm_rewrite_tac[] >>
  simp[DROP_APPEND, LENGTH_MAP, added_labels_def]
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
  simp[new_block_def, added_labels_def, all_blocks_def, MAP_APPEND,
       DROP_APPEND, LENGTH_MAP]
QED

Theorem added_labels_emit_inst:
  emit_inst opc ops outs st = (r, st') ==> added_labels st st' = []
Proof
  simp[emit_inst_def, fresh_id_def, comp_bind_def, comp_return_def,
       added_labels_def, all_blocks_def, emit_def, LENGTH_MAP]
QED
