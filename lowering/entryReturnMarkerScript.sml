(* A proof-only GAS marker at the return continuation. The suffix remains
   in its original block, so the allocation sites retain their order. *)
Theory entryReturnMarker
Ancestors
  fragGasOrigin frameGasEvents venomInst venomState list rich_list

Definition return_marker_inst_def:
  return_marker_inst id = mk_inst id GAS [] ["return_marker"]
End

Definition return_marker_blocks_def:
  return_marker_blocks label idx id [] = [] /\
  return_marker_blocks label idx id (bb::bbs) =
    if bb.bb_label = label then
      (bb with bb_instructions := TAKE idx bb.bb_instructions ++
        return_marker_inst id :: DROP idx bb.bb_instructions) :: bbs
    else bb :: return_marker_blocks label idx id bbs
End

Definition return_marker_fn_def:
  return_marker_fn func label idx id =
    func with fn_blocks := return_marker_blocks label idx id func.fn_blocks
End

Definition return_marker_ctx_def:
  return_marker_ctx ctx func label idx id =
    ctx with ctx_functions :=
      MAP (\f. if f = func then return_marker_fn f label idx id else f)
          ctx.ctx_functions
End

Theorem return_marker_lookup_blocks[local]:
  !bbs. lookup_block l (return_marker_blocks label idx id bbs) =
    OPTION_MAP (\bb. if l = label then
      bb with bb_instructions := TAKE idx bb.bb_instructions ++
        return_marker_inst id :: DROP idx bb.bb_instructions
      else bb) (lookup_block l bbs)
Proof
  Cases_on `l = label` >> simp[]
  >- (Induct >> simp[return_marker_blocks_def, lookup_block_def, FIND_thm] >>
      gen_tac >> IF_CASES_TAC >> fs[FIND_thm, lookup_block_def]) >>
  Induct >> simp[return_marker_blocks_def, lookup_block_def, FIND_thm] >>
  gen_tac >> IF_CASES_TAC >> fs[FIND_thm, lookup_block_def] >> metis_tac[]
QED

Theorem return_marker_lookup:
  lookup_block l (return_marker_fn func label idx id).fn_blocks =
    OPTION_MAP (\bb. if l = label then
      bb with bb_instructions := TAKE idx bb.bb_instructions ++
        return_marker_inst id :: DROP idx bb.bb_instructions
      else bb) (lookup_block l func.fn_blocks)
Proof
  simp[return_marker_fn_def, return_marker_lookup_blocks]
QED

Theorem return_marker_fetch:
  lookup_block l func.fn_blocks = SOME bb ==>
  ?b. lookup_block l (return_marker_fn func label idx id).fn_blocks = SOME b /\
      (l <> label ==> b = bb) /\
      (!j. j < idx /\ (l = label ==> idx <= LENGTH bb.bb_instructions) ==>
           get_instruction b j = get_instruction bb j) /\
      (l = label /\ idx <= LENGTH bb.bb_instructions ==>
       get_instruction b idx = SOME (return_marker_inst id))
Proof
  simp[return_marker_lookup] >> strip_tac >>
  Cases_on `l = label` >> gvs[get_instruction_def, EL_APPEND_EQN] >>
  rw[] >> fs[LENGTH_TAKE_EQ, EL_APPEND_EQN, EL_TAKE, LENGTH_DROP] >> decide_tac
QED

Theorem return_marker_no_empty_edge:
  lookup_block label func.fn_blocks = SOME bb /\
  idx <= LENGTH bb.bb_instructions /\
  s.vs_current_bb = label /\ s.vs_inst_idx = idx ==>
  ~gas_origin_edge memory E ctx (return_marker_fn func label idx id) s [] r
Proof
  strip_tac >> drule return_marker_fetch >>
  disch_then (qspecl_then [`label`,`idx`,`id`] strip_assume_tac) >>
  simp[gas_origin_edge_def, gas_events_step_plain, return_marker_inst_def,
       mk_inst_def]
QED
