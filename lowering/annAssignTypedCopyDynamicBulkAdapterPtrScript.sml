(* Compiler-relative equal-layout dynamic payload execution. *)
Theory annAssignTypedCopyDynamicBulkAdapterPtr
Ancestors
  annAssignTypedCopyDynamicBulkPtr typedMemoryCopy bodyPtrDefs
  compileEnv emitHelper fragExec venomState venomInst venomExecSemantics
  loweringStateRelDefs freshWrites ASCIInumbers words arithmetic list

Theorem annassign_dynamic_compiler_bulk_payload:
  !ce dst src ty cap sa sb fn s len sr dr tmp a b n tv f G tn ctx D PG.
    compile_copy_dynarray_typed ce (Var dst) ty cap (Var src) ty sa = ((),sb) /\
    fn_has_code sa sb fn /\
    len = "%" ++ toString sa.cs_next_var /\
    sr = "%" ++ toString (sa.cs_next_var+3) /\
    dr = "%" ++ toString (sa.cs_next_var+4) /\
    tmp = "%" ++ toString (sa.cs_next_var+5) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    n * type_memory_bytes ce ty < dimword (:256) /\
    type_memory_bytes ce ty = type_memory_size tv /\
    ptr_covers G tn sr s (n * type_memory_bytes ce ty) /\
    ptr_covers G tn dr s (n * type_memory_bytes ce ty) /\
    (!i. i < n ==> val_wf tv (f i)) /\
    (!i. i < n ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv (f i) (w2n a + i * type_memory_bytes ce ty) m) ==>
    ?H tf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) (n * type_memory_bytes ce ty) s t /\
      (!i. i < n ==> !m. mem_agree_outside tf.t_mem t.vs_memory m ==>
        val_in_memory tv (f i) (w2n b + i * type_memory_bytes ce ty) m) /\
      (!j. ~(w2n b <= j /\ j < w2n b + n * type_memory_bytes ce ty) ==>
        mem_bytes_at j 1 t.vs_memory = mem_bytes_at j 1 s.vs_memory /\
        (j IN tf.t_mem <=> j IN tn.t_mem)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = len \/ x = sr \/ x = dr ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_fast_payload_locations >> strip_tac >>
  drule annassign_dynamic_fast_compiler_suffix >> strip_tac >>
  `sr <> tmp /\ dr <> tmp /\ ~not_fresh_at sa tmp /\
   (!x. not_fresh_at sa x \/ x = len \/ x = sr \/ x = dr ==> x <> tmp)` by
    (gvs[not_fresh_at_def, toString_inj] >> rpt strip_tac >>
     gvs[not_fresh_at_def, toString_inj] >> decide_tac) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst (sa.cs_next_id+7) MUL
       [Var len;Lit (n2w (type_memory_bytes ce ty))] [tmp]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst ((sa.cs_next_id+7)+1) MCOPY [Var dr;Var sr;Var tmp] [])` by
    simp[ADD1, ADD_ASSOC] >>
  drule_all (Q.INST [`sa` |-> `sa`] annassign_dynamic_bulk_resources) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tf`,`t`] >> gvs[] >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!x. x <> _ ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> metis_tac[]
QED
