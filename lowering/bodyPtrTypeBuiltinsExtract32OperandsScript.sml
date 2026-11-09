Theory bodyPtrTypeBuiltinsExtract32Operands
Ancestors
  bodyPtrSignedConvertSourceCompile rawCallBufferPtr
  bodyPtrSignedConvertBytesRead bodyPtrDefs venomState

(* Read the header using the value's actual footprint, including Bytes[0].
   Buffer capacity at an expression annotation is not needed here. *)
Theorem extract32_source_prefix_counted:
  compile_bytestring_src (Var src) sb = ((len_op,data_op),sc) /\
  not_fresh_at sb src /\ sa.cs_next_var <= sb.cs_next_var /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!j. j < LENGTH (emitted_insts sb sc) ==>
    get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts sb sc))) /\
  ptr_mem_ok cx ty (BytesV bs) (Var src) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  op_taint tn (Var src) = {} /\ eval_operand (Var src) s = SOME a /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sb p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) ==>
  ?len data H th t.
    len_op = Var len /\ data_op = Var data /\ ALL_DISTINCT [src;len;data] /\
    ptr_mem_ok cx ty (BytesV bs) (Var src) H th t /\
    lookup_var src t = SOME a /\ op_taint th (Var src) = {} /\
    not_fresh_at sc src /\ not_fresh_at sc len /\ not_fresh_at sc data /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th (OK t) /\
    lookup_var len t = SOME (mload (w2n a) s) /\
    op_taint th (Var len) = {} /\ op_prov H (Var len) = NONE /\
    lookup_var data t = SOME (a+32w) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC (SUC s.vs_inst_idx) /\
    (!p. p <> len /\ p <> data ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    (!n. 32 < 32 + LENGTH bs /\ 32+n <= 32 + LENGTH bs /\
      w2n a+32 < dimword(:256) ==> ptr_covers H th data t n) /\
    ghost_inv d cenv cx es H th t /\
    ghost_kept cenv es0 sa G0 tn0 s0 H th
Proof
  strip_tac >>
  drule_all ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  `lookup_var src s = SOME a` by gvs[eval_operand_def] >>
  `ptr_covers G tn src s (32 + LENGTH bs)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `32 <= 32 + LENGTH bs` by simp[] >>
  drule_all compile_bytestring_src_counted_frame >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `src <> len /\ src <> data` by gvs[listTheory.ALL_DISTINCT] >>
  `lookup_var src t = SOME a /\ op_taint tn' (Var src) = {} /\
   FLOOKUP G' src = FLOOKUP G src` by metis_tac[] >>
  `ptr_mem_ok cx ty (BytesV bs) (Var src) G' tn' t` by
    (simp[ptr_mem_ok_def, eval_operand_def] >> rpt strip_tac >>
     gvs[ptr_mem_ok_def, eval_operand_def]) >>
  qexistsl_tac [`len`,`data`,`G'`,`tn'`,`t`] >> simp[]
QED
