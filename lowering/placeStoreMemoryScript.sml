(*
 * place_store_value_run (placeStore) at a place in memory: a word by one
 * MSTORE, an aggregate staged through a fresh buffer when the source is
 * in memory, then compile_store_memory (one MCOPY at one type or for a
 * bytestring, compile_store_memory_typed element by element otherwise).
 *
 * TOP-LEVEL: place_store_value_memory_run
 *)

Theory placeStoreMemory
Ancestors
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState placeMemoryTypeInterfaces placeMemoryPrimitiveForward
  placeMemoryCodeLayout placeMemoryCopyFrames placeMemoryTypedBase
  placeMemoryStateRebuild placeMemoryAssignForward exprSimProps vyperTypeArgFits

(* A widening-compatible representative that selects the typed array loop. *)
Theorem typed_copy_string_array_widens[local]:
  well_formed_type tenv (ArrayT (BaseT (StringT 33)) (Dynamic 2)) ==>
  type_widens_to tenv (ArrayT (BaseT (StringT 1)) (Dynamic 2))
                     (ArrayT (BaseT (StringT 33)) (Dynamic 2))
Proof
  simp[type_widens_to_def, arg_type_fits_def]
QED

Theorem typed_copy_string_array_dispatch[local]:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst
    (ArrayT (BaseT (StringT 33)) (Dynamic 2)) src
    (ArrayT (BaseT (StringT 1)) (Dynamic 2)) =
  compile_copy_dynarray_typed cenv dst (BaseT (StringT 33)) 2
                             src (BaseT (StringT 1))
Proof
  simp[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def]
QED

Theorem typed_copy_string_array_loop[local]:
  compile_copy_dynarray_typed cenv dst (BaseT (StringT 33)) 2
                             src (BaseT (StringT 1)) =
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w 2)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      cond_lbl <- fresh_label "typed_dyn_cond";
      body_lbl <- fresh_label "typed_dyn_body";
      exit_lbl <- fresh_label "typed_dyn_exit";
      counter <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [counter];
      emit_inst JMP [Label cond_lbl] [];
      new_block cond_lbl;
      lt_op <- emit_op LT [Var counter; length];
      done_op <- emit_op ISZERO [lt_op];
      emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
      new_block body_lbl;
      src_off <- emit_op MUL [Var counter;
        Lit (n2w (type_memory_bytes cenv (BaseT (StringT 1))))];
      dst_off <- emit_op MUL [Var counter;
        Lit (n2w (type_memory_bytes cenv (BaseT (StringT 33))))];
      src_elem <- emit_op ADD [src_data; src_off];
      dst_elem <- emit_op ADD [dst_data; dst_off];
      compile_store_memory_typed cenv dst_elem (BaseT (StringT 33))
                                     src_elem (BaseT (StringT 1));
      new_ctr <- emit_op ADD [Var counter; Lit 1w];
      emit_inst ASSIGN [new_ctr] [counter];
      emit_inst JMP [Label cond_lbl] [];
      _ <- new_block exit_lbl;
      return ()
   od)
Proof
  simp[Once contextTheory.compile_store_memory_typed_def]
QED

(* compile_assign_value into memory. *)
Theorem place_store_value_memory_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    loc = LocMemory /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_assign_memory_forward_local_frame >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
     qexistsl_tac [`dty`, `ee`, `env`, `p`, `r`, `s`, `sa`] >>
     gvs[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> simp[]
QED
