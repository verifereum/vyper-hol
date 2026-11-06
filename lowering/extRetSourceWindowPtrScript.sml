(* Actual live source bounds, independent of ghost-allocation end bounds. *)
Theory extRetSourceWindowPtr
Ancestors
  extRetSourceAllocationPtr extRetAbiReadBoundsPtr stmtSimReturn
  words finite_map arithmetic loweringPosts bodyPtrDefs

Theorem expr_val_at_aggregate_bound:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  (!bs. v <> BytesV bs) /\ (!str. v <> StringV str) ==>
  w2n w + type_memory_size tv < dimword(:256)
Proof
  strip_tac >> drule_all non_bytes_source_sizes >> strip_tac >>
  drule_all expr_val_at_bound >> simp[]
QED

Theorem expr_val_at_bytes_live_bound:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type ty /\ eval_operand op s = SOME w ==>
  w2n w + (32 + LENGTH bs) < dimword(:256)
Proof
  strip_tac >> drule_all expr_val_at_bound >> simp[val_footprint_def]
QED

Theorem expr_val_at_string_live_bound:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es (StringV str) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT cap)) /\
  ~is_word_type ty /\ eval_operand op s = SOME w ==>
  w2n w + (32 + LENGTH str) < dimword(:256)
Proof
  strip_tac >> drule_all expr_val_at_bound >> simp[val_footprint_def]
QED

Theorem positive_source_subwindow_arithmetic:
  w2n (w:256 word) + extent < dimword(:256) /\
  0 < n /\ off+n <= extent ==>
  w2n (w+n2w off) = w2n w+off /\
  w2n (w+n2w off)+n < dimword(:256)
Proof
  strip_tac >>
  `off < dimword(:256) /\ w2n w+off < dimword(:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac
QED

Theorem ptr_covers_positive_source_subwindow:
  ptr_covers G tn p s extent /\ lookup_var p s = SOME w /\
  w2n w+extent < dimword(:256) /\ 0 < n /\ off+n <= extent /\
  lookup_var q s' = SOME (w+n2w off) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' n
Proof
  strip_tac >> drule_all positive_source_subwindow_arithmetic >> strip_tac >>
  gvs[ptr_covers_def] >> decide_tac
QED

(* The input capacity here is the actual footprint, not necessarily the
   declared bytes/string capacity. Input shape remains a separate premise. *)
Theorem abi_encoder_actual_footprint_read_bound:
  abi_encoder_read_window ei av sb a n /\
  abi_encoder_input ei at av sb (val_footprint tv v) mem /\
  sb + val_footprint tv v < dimword(:256) ==>
  a+n < dimword(:256)
Proof
  strip_tac >> drule_all abi_encoder_read_window_bounds >> decide_tac
QED
