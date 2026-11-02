(* Layout conversion between disjoint memory regions. Memory Assign stages
   its source before invoking this routine; that staging allocation belongs
   to the caller's frame, while this routine writes only the destination.
   Metadata premises are the field-layout clauses of expr_sim_inv. *)
Theory typedMemoryCopy
Ancestors
  context typedCopyDomain compileEnv valueEncoding valueEncodingProps
  valueEncodingProofs valueCopy fragExec exprLoweringProps
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping
  venomExecSemantics venomState venomInst words list finite_map arithmetic

Theorem compile_store_memory_typed_run:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((), sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED
