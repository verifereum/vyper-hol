(* Joint offset-prefix application of a recursive member store. *)
Theory fullStoreSlotsMemberStep
Ancestors
  fullStoreSlotsMembers fullStoreSlotsMemberFrame
  typedCopyOriginPtrBase fragGasOriginPtr context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list arithmetic words stateFrame stmtLoweringMono
  typedMemoryCopy fragExec pair

Theorem store_slots_member_code:
  compile_lit_byte_offset (Var root) mo sa = (src,sb) /\
  compile_lit_byte_offset dst so sb = (slot,sc) /\
  compile_store_slots cenv src slot ty tr sc = ((),sd) /\
  fn_has_code sa sd func ==>
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p /\ not_fresh_at sc p)
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_lit_byte_offset,cj 1 ci_mono_compile_store_slots,SND] >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[ci_mono_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  simp[] >> rpt strip_tac >>
  metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS]
QED
