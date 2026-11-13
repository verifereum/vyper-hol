Theory makeSsaCurrentOutputHistory
Ancestors
  venomInst venomState list pred_set

Definition current_output_history_def:
  current_output_history f V P st <=>
    (!b i x. MEM b f.fn_blocks /\ b.bb_label IN V /\
      MEM i b.bb_instructions /\ MEM x i.inst_outputs ==>
      IS_SOME (lookup_var x st)) /\
    (!i x. MEM i P /\ MEM x i.inst_outputs ==>
      IS_SOME (lookup_var x st))
End

Theorem current_output_history_empty:
  current_output_history f {} [] st
Proof
  simp[current_output_history_def]
QED

Theorem current_output_history_transport:
  current_output_history f V P st /\
  (!x. IS_SOME (lookup_var x st) ==> IS_SOME (lookup_var x post)) ==>
  current_output_history f V P post
Proof
  simp[current_output_history_def] >> metis_tac[]
QED

Theorem current_output_history_extend:
  current_output_history f V P st /\
  (!i x. MEM i Q /\ MEM x i.inst_outputs ==> IS_SOME (lookup_var x st)) ==>
  current_output_history f V (P ++ Q) st
Proof
  simp[current_output_history_def, MEM_APPEND] >> metis_tac[]
QED

Theorem current_output_history_complete:
  current_output_history f V b.bb_instructions st /\
  MEM b f.fn_blocks /\ ALL_DISTINCT (MAP basic_block_bb_label f.fn_blocks) ==>
  current_output_history f (b.bb_label INSERT V) [] st
Proof
  strip_tac >>
  `!b1 b2. MEM b1 f.fn_blocks /\ MEM b2 f.fn_blocks /\
     b1.bb_label = b2.bb_label ==> b1 = b2` by
    (simp[MEM_EL] >> rpt strip_tac >> gvs[] >>
     `EL n (MAP basic_block_bb_label f.fn_blocks) =
      EL n' (MAP basic_block_bb_label f.fn_blocks)` by simp[EL_MAP] >>
     `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  gvs[current_output_history_def] >> metis_tac[]
QED

Theorem current_output_history_lookup:
  current_output_history f V P st /\ MEM b f.fn_blocks /\
  b.bb_label IN V /\ MEM i b.bb_instructions /\ MEM x i.inst_outputs ==>
  IS_SOME (lookup_var x st)
Proof
  simp[current_output_history_def] >> metis_tac[]
QED
