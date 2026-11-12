(* Counted slow dynamic-array copying, with live runtime length. *)
Theory typedCopyReturnDynArrayPtr
Ancestors typedCopyReturnDynArrayLayoutPtr typedCopyReturnDynArrayEntryPtr
  typedCopyReturnIndexBodyPtr typedCopyReturnControlPtr typedCopyReturnLoopPtr
  typedCopyRuntimeLengthHeaderPtr typedCopyReturnArrayBulkPtr
  typedCopyReturnArrayLayoutPtr typedCopyLayoutPtr typedMemoryCopy stateFrame
  assignBasePtrStorageLayout
  venomState venomInst ptrDiscipline words finite_map list arithmetic

(* Scalar loop control changes neither memory nor pre-existing variables. *)
Theorem typed_copy_control_state_frame[local]:
  execution_frame t = execution_frame s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  typed_copy_state_frame sa off len s t
Proof
  simp[execution_frame_def,typed_copy_state_frame_def,
    typed_copy_frame_def,venom_state_component_equality]
QED

Theorem typed_copy_dynarray_header_frame[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;Var len] [lt]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
  get_instruction bb (s.vs_inst_idx+2) =
    SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
  lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n) /\
  i <= n /\ n < dimword(:256) /\ op_taint tn (Var ctr) = {} /\
  op_taint tn (Var len) = {} /\ FLOOKUP G ctr = NONE /\ FLOOKUP G len = NONE /\
  ALL_DISTINCT [ctr;lt;done] /\ ~ctx_has_dalloca ctx /\
  (!x. not_fresh_at sa x ==> x <> lt /\ x <> done) /\
  P tn.t_mem s.vs_memory ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = (if i<n then bodylbl else exit) /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    typed_copy_state_frame sa off span s t /\ P tm.t_mem t.vs_memory /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var len) s = SOME (n2w n) /\ op_prov G (Var len) = NONE` by
    simp[eval_operand_def,op_prov_def] >>
  drule_all typed_copy_runtime_length_header_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  irule typed_copy_control_state_frame >>
  gvs[execution_frame_def,venom_state_component_equality]
QED

Theorem typed_copy_dynarray_backedge_frame[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var ctr;Lit 1w] [nv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) JMP [Label hdr] []) /\
  lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\
  op_taint tn (Var ctr) = {} /\ ctr <> nv /\ ~ctx_has_dalloca ctx /\
  (!x. not_fresh_at sa x ==> x <> ctr /\ x <> nv) /\
  P tn.t_mem s.vs_memory ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    lookup_var ctr t = SOME (n2w (SUC i)) /\ FLOOKUP H ctr = NONE /\
    op_taint tm (Var ctr) = {} /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    typed_copy_state_frame sa off span s t /\ P tm.t_mem t.vs_memory /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> ctr /\ x <> nv ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all typed_copy_backedge_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  irule typed_copy_control_state_frame >>
  gvs[execution_frame_def,venom_state_component_equality]
QED

Theorem typed_copy_dynarray_init_frame[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [ctr]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
  ~ctx_has_dalloca ctx /\ (!x. not_fresh_at sa x ==> x <> ctr) /\
  P tn.t_mem s.vs_memory ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    lookup_var ctr t = SOME 0w /\ FLOOKUP H ctr = NONE /\ op_taint tm (Var ctr) = {} /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    typed_copy_state_frame sa off span s t /\ P tm.t_mem t.vs_memory /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> ctr ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all assign_base_storage_init_counted >>
  disch_then (qspecl_then [`tn`,`G`,`D`,`PG`] assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_DRESTRICT,
    FLOOKUP_UPDATE,op_taint_def,typed_copy_state_frame_def] >>
  rpt strip_tac >> `x <> ctr` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED
