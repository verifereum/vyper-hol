Theory o1MakeSsaCallBlockBridge
Ancestors
  o1MakeSsaCallChecks o1MakeSsaTraversalFrames o1MakeSsaFormats
  o1MakeSsaCallOwnership o1MakeSsaCallPaths unitShapeDefs makeSsaCurrentDefs
  list pred_set o1ContractMakeSsaSrcOpcodes simplifyCfgCallChecks o1MakeSsaReaching

Theorem current_calls_flagged_phi_prefix:
  rename_current_block_insts s rs (pre ++ rest) = (rs',s',insts') /\
  current_rename_owner V H s rs /\
  EVERY (\i. set i.inst_outputs SUBSET V) (pre ++ rest) /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  EVERY (\i. i.inst_opcode <> PHI) rest /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  calls_flagged bbs (pre ++ rest) ==>
  calls_flagged bbs' insts'
Proof
  simp[rename_current_block_insts_append] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all current_rename_owner_block_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) pre` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) ns` by
    (qpat_assum `rename_current_block_insts s rs pre = _`
       (mp_tac o MATCH_MP rename_current_block_insts_opcodes) >>
     disch_then (mp_tac o Q.AP_TERM `EVERY (\op. op <> CALL /\ op <> STATICCALL)`) >>
     simp[EVERY_MAP, combinTheory.o_DEF]) >>
  gvs[calls_flagged_prefix_no_calls] >>
  irule current_calls_flagged_block_insts >> metis_tac[]
QED

Theorem mssa_patch_flag_path[local]:
  !xs ys vs.
  LIST_REL (\a b. b.inst_opcode = a.inst_opcode /\
    b.inst_outputs = a.inst_outputs /\
    (a.inst_opcode <> PHI ==> b = a)) xs ys ==>
  (flag_path env vs xs = flag_path env vs ys)
Proof
  Induct_on `xs` >- (simp[flag_path_def]) >>
  rpt gen_tac >> Cases_on `ys` >- simp[] >>
  rename1 `LIST_REL _ (a::xs) (b::ys')` >>
  simp[] >> strip_tac >> Cases_on `a.inst_opcode = PHI`
  >- (fs[] >> simp[flag_path_def, flag_fails_def] >> metis_tac[]) >>
  `b = a` by metis_tac[] >> simp[flag_path_def] >> metis_tac[]
QED

Theorem mssa_patch_calls_flagged[local]:
  !xs ys.
  LIST_REL (\a b. b.inst_opcode = a.inst_opcode /\
    b.inst_outputs = a.inst_outputs /\
    (a.inst_opcode <> PHI ==> b = a)) xs ys ==>
  (calls_flagged env xs = calls_flagged env ys)
Proof
  Induct_on `xs` >- simp[calls_flagged_def] >>
  rpt gen_tac >> Cases_on `ys` >- simp[] >>
  rename1 `LIST_REL _ (a::xs) (b::ys')` >>
  simp[] >> strip_tac >>
  `calls_flagged env xs = calls_flagged env ys'` by metis_tac[] >>
  `!vs. flag_path env vs xs = flag_path env vs ys'` by
    metis_tac[mssa_patch_flag_path] >>
  Cases_on `a.inst_opcode = PHI`
  >- (fs[] >> simp[calls_flagged_def]) >>
  `b = a` by metis_tac[] >> simp[calls_flagged_def]
QED

Theorem indexed_patch_frame_calls_flagged:
  indexed_patch_frame a b ==>
  (calls_flagged env a.bb_instructions = calls_flagged env b.bb_instructions)
Proof
  strip_tac >> irule mssa_patch_calls_flagged >>
  gvs[indexed_patch_frame_def, LIST_REL_EL_EQN]
QED
