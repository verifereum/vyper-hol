(* Counted writes through computed storage and transient places. *)
Theory bodyMemPlaceStorageStore
Ancestors
  augAssignPlaceWordStoreMemory placeStore stmtLowering loweringPosts
  bodyDeclMemoryCore exprSimProps exprLoweringProps fragGasMode venomState

Theorem place_store_empty_storage_run_mem:
  compile_store_at_loc imm dst_op (Lit 0w) (SOME loc) sa = ((),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  strip_tac >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w 0w s
                  | LocTransient => tstore w 0w s | _ => s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, Abbr `u`] >>
     drule_all place_store_empty_backend_state >> Cases_on `b` >> gvs[]) >>
  drule_all place_store_write_location >> strip_tac >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                        | _ => MSTORE) [dst_op; Lit 0w] sa = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_store_at_loc_def]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule place_store_emit_run_mem >> simp[] >>
     qexistsl_tac [`dst_op`, `loc`, `Lit 0w`, `sa`] >>
     Cases_on `loc` >> gvs[eval_operand_def, Abbr `u`]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
