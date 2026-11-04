Theory makeSsaCurrentDefaultOrigin
Ancestors makeSsaCurrentTokens venomInst list

Theorem current_output_token_default:
  !xs j t. current_output_token v l i j xs t = CurrentDefault w <=>
    t = CurrentDefault w /\ ~MEM v xs
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h = v` >> simp[] >> metis_tac[]
QED

Theorem current_original_scan_default:
  !insts i t. current_original_scan v l i insts t = CurrentDefault w <=>
    t = CurrentDefault w /\ EVERY (\inst. ~MEM v inst.inst_outputs) insts
Proof
  Induct >> simp[current_original_scan_def, current_output_token_default] >>
  metis_tac[]
QED

Theorem current_block_token_default:
  current_block_token fn ins v l t = CurrentDefault w <=>
  t = CurrentDefault w /\
  (!bb. lookup_block l fn.fn_blocks = SOME bb ==>
    ~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions)
Proof
  Cases_on `lookup_block l fn.fn_blocks` >>
  simp[current_block_token_def, current_original_scan_default] >>
  Cases_on `ins v l` >> simp[] >> metis_tac[]
QED

Theorem current_chain_token_default:
  !labels t. current_chain_token fn ins v labels t = CurrentDefault w <=>
    t = CurrentDefault w /\
    EVERY (\l. !bb. lookup_block l fn.fn_blocks = SOME bb ==>
      ~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) labels
Proof
  Induct >> simp[current_chain_token_def, current_block_token_default] >>
  metis_tac[]
QED

Theorem current_exit_default_sites:
  current_block_token fn ins v p (current_inherited_token fn ins v path) =
    CurrentDefault out <=>
  out = v /\
  EVERY (\l. !bb. lookup_block l fn.fn_blocks = SOME bb ==>
    ~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions)
    (path ++ [p])
Proof
  rewrite_tac[GSYM current_inherited_token_step] >>
  simp[current_inherited_token_def, current_chain_token_default] >> metis_tac[]
QED

Theorem current_exit_default_owner:
  current_block_token fn ins v p (current_inherited_token fn ins v path) =
    CurrentDefault out ==> out = v
Proof
  simp[current_exit_default_sites]
QED
