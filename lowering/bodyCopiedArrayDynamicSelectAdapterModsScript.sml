(* Canonical compiler cut for reading a copied dynamic array's length. *)
Theory bodyCopiedArrayDynamicSelectAdapterMods
Ancestors
  bodyCopiedArrayCutDefsMods compileEnv context exprLowering emitHelper
  vyperAST valueEncoding venomInst

Theorem copied_select_compile_dynamic_mload:
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0)
    (obj,mid,raw,ArrayV (DynArrayV vs),et,Dynamic cap,ArrayTV tv (Dynamic cap))
    (ann,idx,fin,IntV i,iop,dst,vv)
    (sm,sc,cvv) (si,z,Gi,ti) sb (q,w) /\
  type_memory_bytes ce et = type_memory_size tv ==>
  compile_array_subscript (Var q) iop T 0 32 (type_memory_size tv)
    (is_signed_type (expr_type idx))
    (\op. emit_op MLOAD [op]) si = (dst,sb)
Proof
  simp[copied_select_cut_mods_def,word_scale_def,elem_size_in_location_def,
       is_slot_addressed_def] >>
  strip_tac >>
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory =
    (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM,compile_ptr_load_def] >>
  fs[]
QED
