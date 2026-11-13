(* Finish an arbitrary-width element copy with the compiler's counter update. *)
Theory assignDynStorageRoundPtr
Ancestors assignStorageBlockFramePtr assignBasePtrStoragePath
  assignBasePtrStorageLoop fragGasPathPtr venomState stateFrame ptrDiscipline
  words finite_map list arithmetic

Theorem dyn_storage_multi_round_keep_counted:
  assign_base_store_frame loc b k s0 tn0 (i*ew) s tn /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
  assign_base_store_frame loc (b+n2w (i*ew)*32w) (k+n2w (i*ew))
    s tn ew u tt /\
  (!x. keep x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx =
    SOME (mk_inst id ADD [Var ctr;Lit 1w] [nv]) /\
  get_instruction bb (SUC u.vs_inst_idx) =
    SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
  get_instruction bb (u.vs_inst_idx+2) =
    SOME (mk_inst (id+2) JMP [Label hdr] []) /\
  lookup_var ctr u = SOME (n2w i) /\ FLOOKUP H ctr = NONE /\
  op_taint tt (Var ctr) = {} /\ ctr <> nv /\ ~ctx_has_dalloca ctx ==>
  ?H' tt' v.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H' tt' (OK v) /\
    assign_base_store_frame loc b k s0 tn0 ((SUC i)*ew) v tt' /\
    lookup_var ctr v = SOME (n2w (SUC i)) /\ FLOOKUP H' ctr = NONE /\
    op_taint tt' (Var ctr) = {} /\
    v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\ ~v.vs_halted /\
    v.vs_labels = u.vs_labels /\
    (!x. keep x /\ x <> ctr /\ x <> nv ==>
      lookup_var x v = lookup_var x s /\ FLOOKUP H' x = FLOOKUP G x /\
      op_taint tt' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `assign_base_store_frame loc b k s0 tn0 (i*ew+ew) u tt` by
    (irule assign_base_store_frame_block >>
     qexistsl_tac [`s`, `tn`] >> simp[]) >>
  drule_all assign_base_storage_increment_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choosel_then [`H1`, `tt1`, `u1`] strip_assume_tac) >>
  `(SUC i)*ew = i*ew+ew` by
    simp[ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  `assign_base_store_frame loc b k s0 tn0 ((SUC i)*ew) u1 tt1` by
    (asm_rewrite_tac [] >> irule assign_base_store_frame_preserve >>
     qexistsl_tac [`u`, `tt`] >> simp[]) >>
  `lookup_block u1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb u1.vs_inst_idx =
     SOME (mk_inst (id+2) JMP [Label hdr] [])` by simp[] >>
  drule_all assign_base_storage_jump_counted >>
  disch_then (qspecl_then [`tt1`, `H1`, `D`, `PG`] assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H1 tt1 (OK (jump_to hdr u1))` by
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  qexistsl_tac [`H1`, `tt1`, `jump_to hdr u1`] >>
  asm_rewrite_tac [] >>
  fs[jump_to_def, assign_base_store_frame_def, lookup_var_def, execution_frame_def] >>
  metis_tac[]
QED

Theorem dyn_storage_multi_round_counted:
  assign_base_store_frame loc b k s0 tn0 (i*ew) s tn /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
  assign_base_store_frame loc (b+n2w (i*ew)*32w) (k+n2w (i*ew))
    s tn ew u tt /\
  (!x. ~MEM x scratch ==> lookup_var x u = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx =
    SOME (mk_inst id ADD [Var ctr;Lit 1w] [nv]) /\
  get_instruction bb (SUC u.vs_inst_idx) =
    SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
  get_instruction bb (u.vs_inst_idx+2) =
    SOME (mk_inst (id+2) JMP [Label hdr] []) /\
  lookup_var ctr u = SOME (n2w i) /\ FLOOKUP H ctr = NONE /\
  op_taint tt (Var ctr) = {} /\ ctr <> nv /\ ~ctx_has_dalloca ctx ==>
  ?H' tt' v.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H' tt' (OK v) /\
    assign_base_store_frame loc b k s0 tn0 ((SUC i)*ew) v tt' /\
    lookup_var ctr v = SOME (n2w (SUC i)) /\ FLOOKUP H' ctr = NONE /\
    op_taint tt' (Var ctr) = {} /\
    v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\ ~v.vs_halted /\
    v.vs_labels = u.vs_labels /\
    (!x. ~MEM x (ctr::nv::scratch) ==>
      lookup_var x v = lookup_var x s /\ FLOOKUP H' x = FLOOKUP G x /\
      op_taint tt' (Var x) = op_taint tn (Var x))
Proof
  mp_tac (Q.INST [`keep` |-> `\x. ~MEM x scratch`]
    dyn_storage_multi_round_keep_counted) >> simp[] >> metis_tac[]
QED
