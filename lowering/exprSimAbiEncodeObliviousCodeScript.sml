Theory exprSimAbiEncodeObliviousCode
Ancestors
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge compileEnv fragExec
  exprLoweringProps list rich_list sorting

Theorem entry_shape_extends:
  !a b. entry_shape a b ==> cs_extends a b
Proof
  rw[entry_shape_def, cs_extends_def]
  >- (qexists_tac `[]` >> simp[])
  >> qexists_tac `front ++
       [<| bb_label := a.cs_current_bb;
           bb_instructions := a.cs_current_insts ++ tail |>]`
  >> simp[LAST_APPEND]
QED

Theorem frag_code_open:
  !a b tail. b.cs_blocks = a.cs_blocks /\
    b.cs_current_insts = a.cs_current_insts ++ tail ==>
    frag_code a b = tail
Proof
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_APPEND]
QED

Theorem frag_code_closed:
  !a b front tail.
    b.cs_blocks = front ++
      [<| bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ tail |>] ++ a.cs_blocks ==>
    frag_code a b = tail ++ FLAT (MAP (\bb. bb.bb_instructions) front) ++
      b.cs_current_insts
Proof
  rpt strip_tac
  >> simp[frag_code_def, emitted_blocks_def, TAKE_APPEND, DROP_APPEND,
          TAKE_LENGTH_TOO_LONG, FRONT_APPEND, LAST_APPEND]
QED
