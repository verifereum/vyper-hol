(* Endpoint insertion experiment.  The construction is named because layout,
   instruction inventories and context registration must all refer to the SAME
   modified function.  No source semantic judgment is changed. *)
Theory augAssignPtrEndpointInsertion
Ancestors
  augAssignPtrSealedBoundary exprLoweringProps fragExec venomInst compileEnv
  list rich_list

Definition aug_endpoint_insert_def:
  aug_endpoint_insert lbl k id fn =
    fn with fn_blocks := MAP (\bb.
      if bb.bb_label = lbl then
        bb with bb_instructions := TAKE k bb.bb_instructions ++
          [mk_inst id INVALID [] []] ++ DROP k bb.bb_instructions
      else bb) fn.fn_blocks
End

Theorem endpoint_insert_block_filter[local]:
  ~P (mk_inst id INVALID [] []) ==>
  FILTER P ((if bb.bb_label = lbl then
    bb with bb_instructions := TAKE k bb.bb_instructions ++
      [mk_inst id INVALID [] []] ++ DROP k bb.bb_instructions
    else bb).bb_instructions) = FILTER P bb.bb_instructions
Proof
  strip_tac >> Cases_on `bb.bb_label = lbl` >> simp[FILTER_APPEND] >>
  metis_tac[TAKE_DROP, FILTER_APPEND]
QED

Theorem endpoint_insert_blocks_filter[local]:
  ~P (mk_inst id INVALID [] []) ==>
  FILTER P (fn_insts_blocks (MAP (\bb.
      if bb.bb_label = lbl then
        bb with bb_instructions := TAKE k bb.bb_instructions ++
          [mk_inst id INVALID [] []] ++ DROP k bb.bb_instructions
      else bb) blocks)) = FILTER P (fn_insts_blocks blocks)
Proof
  strip_tac >> Induct_on `blocks` >>
  simp[fn_insts_blocks_def, FILTER_APPEND, endpoint_insert_block_filter]
QED

Theorem endpoint_insert_filter:
  ~P (mk_inst id INVALID [] []) ==>
  FILTER P (fn_insts (aug_endpoint_insert lbl k id fn)) = FILTER P (fn_insts fn)
Proof
  simp[aug_endpoint_insert_def, fn_insts_def, endpoint_insert_blocks_filter]
QED

Theorem endpoint_insert_inventories:
  FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts (aug_endpoint_insert lbl k id fn)) =
    FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn) /\
  FILTER (\i. i.inst_opcode = INVOKE) (fn_insts (aug_endpoint_insert lbl k id fn)) =
    FILTER (\i. i.inst_opcode = INVOKE) (fn_insts fn) /\
  FILTER (\i. i.inst_opcode = DALLOCA) (fn_insts (aug_endpoint_insert lbl k id fn)) =
    FILTER (\i. i.inst_opcode = DALLOCA) (fn_insts fn)
Proof
  rpt conj_tac >> irule endpoint_insert_filter >> simp[mk_inst_def]
QED

Theorem endpoint_insert_single_length:
  fn.fn_blocks = [bb] /\ bb.bb_label = lbl ==>
  LENGTH (fn_insts (aug_endpoint_insert lbl k id fn)) = SUC (LENGTH (fn_insts fn))
Proof
  strip_tac >> simp[aug_endpoint_insert_def, fn_insts_def, fn_insts_blocks_def] >>
  `LENGTH (TAKE k bb.bb_instructions) + LENGTH (DROP k bb.bb_instructions) =
    LENGTH bb.bb_instructions` by metis_tac[TAKE_DROP, LENGTH_APPEND] >>
  gvs[LENGTH_DROP]
QED

Theorem endpoint_insert_single_registration_obstruction:
  fn.fn_blocks = [bb] /\ bb.bb_label = lbl /\
  stmt_state_rel ctx fn ce cx es s ==>
  ~stmt_state_rel ctx (aug_endpoint_insert lbl k id fn) ce' cx' es' t
Proof
  strip_tac >> strip_tac >>
  `fn.fn_name = (aug_endpoint_insert lbl k id fn).fn_name` by
    simp[aug_endpoint_insert_def] >>
  `fn = aug_endpoint_insert lbl k id fn` by
    metis_tac[stmt_state_rel_function_unique] >>
  drule_all endpoint_insert_single_length >>
  disch_then (qspecl_then [`k`, `id`] mp_tac) >>
  qpat_x_assum `fn = aug_endpoint_insert _ _ _ _` (assume_tac o GSYM) >> simp[]
QED
