(* Normalized counted control for the outer dynamic storage traversal. *)
Theory placeStorageTraversalCounted
Ancestors
  placeStorageControlCounted typedArrayControlCounted typedArrayLoopControlMem typedCopyLoopCounted
  placeStorageLayoutCounted placeStorageElementPaths stmtSimStoreCopy venomState venomInst emitHelperProps words list rich_list

Theorem storage_traversal_header:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr; Var len] [cmp];
     mk_inst (id+1) ISZERO [Var cmp] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n) /\
  i <= n /\ n < dimword(:256) ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize sbase q = store_copy_normalize sbase s /\
      (!x. x <> cmp /\ x <> done ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = (if i < n then body_lbl else exit) /\
      q.vs_inst_idx = 0
Proof
  strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i) /\
   eval_operand (Var len) s = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all typed_memory_array_condition_path_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[venomStateTheory.jump_to_def, lookup_var_update_var, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_backedge:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  lookup_var ctr s = SOME (n2w i) /\ ctr <> nv ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize sbase q = store_copy_normalize sbase s /\
      lookup_var ctr q = SOME (n2w (SUC i)) /\
      (!x. x <> ctr /\ x <> nv ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0
Proof
  strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i)` by simp[eval_operand_def] >>
  drule_all typed_sa_backedge_path >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[typed_sa_backedge_state_def, venomStateTheory.jump_to_def,
       lookup_var_update_var, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) ASSIGN [Lit 0w] [ctr];
     mk_inst (id+2) JMP [Label hdr] []] /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = n2w n /\ ctr <> len ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize s q = s /\
      lookup_var ctr q = SOME 0w /\ lookup_var len q = SOME (n2w n) /\
      (!x. x <> ctr /\ x <> len ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0
Proof
  strip_tac >> drule_all dyn_storage_entry_path >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[venomStateTheory.jump_to_def, lookup_var_update_var, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_fold_fields:
  H = (\i. FOLDL (\a j. store_copy_prefix loc
           (p + n2w (32 + j*stride)) (d + n2w (1 + j*ew)) a ew)
         sbase (COUNT_LIST i)) /\
  store_copy_normalize sbase s = H j ==>
  s.vs_memory = sbase.vs_memory /\ s.vs_allocas = sbase.vs_allocas /\
  s.vs_alloca_next = sbase.vs_alloca_next /\ s.vs_call_ctx = sbase.vs_call_ctx
Proof
  strip_tac >> drule storage_element_fold_fields >>
  disch_then (qspec_then `j` mp_tac) >>
  qpat_x_assum `store_copy_normalize _ _ = _` (SUBST1_TAC o SYM) >>
  simp[store_copy_normalize_def]
QED
