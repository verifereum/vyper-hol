Theory dftOriginalSegment
Ancestors
  dftOrdinarySwap dftOriginalOperands dftOriginalRuntime dftLocalOrdinaryClosure
  dftOccurrenceOrdinaryClosure dftProtectedRuntime dftOriginalScheduleRuntime
  dftOccurrenceAvailability venomWf venomInst list finite_map

Theorem dft_original_crossing_labels:
  dft_original_label_ready C L c /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n /\
  q.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) ==>
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels)
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ s.vs_labels = L` by
    (fs[dft_original_label_ready_def] >> metis_tac[dft_source_active_at]) >>
  `MEM q fn.fn_blocks` by
    (fs[dft_original_label_ready_def] >>
     drule_all dft_original_runtime_at_projection >> simp[]) >>
  `MEM x (fn_insts fn) /\ MEM y (fn_insts fn)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> conj_tac >>
     qexists `q` >> simp[]) >>
  fs[dft_ordinary_swap_pair_def] >> metis_tac[]
QED

Theorem dft_original_sync_pair_segment:
  dft_original_label_ready C L c /\
  dft_original_block f b q /\ dft_original_cut f b q s /\
  q.bb_instructions = (pp ++ done) ++ [x;y] ++ post /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  schedule_edges b.bb_instructions dft_must_order ((pp ++ done) ++ [y;x] ++ post) /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ y.inst_opcode <> ALLOCA /\
  ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) /\
  dft_ordinary_sync q (pp ++ done) x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) stack n ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    (dft_ordinary_sync q (pp ++ done) x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q (pp ++ done) x y post C)) j d) \/
     dft_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q (pp ++ done) x y post C)) j d)) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn q (pp ++ done) x y post) w C
      (dft_gas_edit_ctx q (pp ++ done) x y post C) c d k j
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   x.inst_opcode <> PHI` by
    (fs[dft_ordinary_swap_pair_def] >>
     metis_tac[is_pseudo_def]) >>
  drule_all dft_original_crossing_labels >> strip_tac >>
  `!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v` by
    (drule dft_original_first_operands >>
     disch_then (qspecl_then [`x`, `y::post`, `pp`, `done`] mp_tac) >>
     simp[APPEND_ASSOC]) >>
  `!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[dft_original_before_operands] >>
  `!sx. step_inst_base x s = OK sx ==> !op. MEM op y.inst_operands ==>
      ?v. eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = SOME v` by
    metis_tac[dft_original_after_operands] >>
  irule dft_ordinary_sync_pair_segment_local >> metis_tac[]
QED
