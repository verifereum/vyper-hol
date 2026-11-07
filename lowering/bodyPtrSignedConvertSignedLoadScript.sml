(* Compiler boundary for the signed bytestring loader. *)
Theory bodyPtrSignedConvertSignedLoad
Ancestors
  bodyPtrSignedConvertScalarOps exprLowering exprLoweringProps compileEnv
  emitHelperProps rich_list venomInst

Theorem signed_loader_decompose:
  load_bytestring_as_word x SAR sa = ((out,bits),sb) ==>
  ?len dp data empty nonempty selected sub s1 s2 s3 s4 s5 s6 s7 s8.
    emit_op MLOAD [x] sa = (len,s1) /\
    emit_op ADD [x;Lit 32w] s1 = (dp,s2) /\
    emit_op MLOAD [dp] s2 = (data,s3) /\
    emit_op ISZERO [len] s3 = (empty,s4) /\
    emit_op ISZERO [empty] s4 = (nonempty,s5) /\
    emit_op MUL [data;nonempty] s5 = (selected,s6) /\
    emit_op SUB [Lit 32w;len] s6 = (sub,s7) /\
    emit_op MUL [sub;Lit 8w] s7 = (bits,s8) /\
    emit_op SAR [bits;selected] s8 = (out,sb)
Proof
  simp[load_bytestring_as_word_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem signed_loader_shape_fresh:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
  not_fresh_at sa src ==>
  ?len dp data empty nonempty selected sub b dst i j k l m r u v w.
    out = Var dst /\ bits = Var b /\
    ALL_DISTINCT [src;len;dp;data;empty;nonempty;selected;sub;b;dst] /\
    emitted_insts sa sb =
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp];
       mk_inst k MLOAD [Var dp] [data];
       mk_inst l ISZERO [Var len] [empty];
       mk_inst m ISZERO [Var empty] [nonempty];
       mk_inst r MUL [Var data;Var nonempty] [selected];
       mk_inst u SUB [Lit 32w;Var len] [sub];
       mk_inst v MUL [Var sub;Lit 8w] [b];
       mk_inst w SAR [Var b;Var selected] [dst]] /\
    (!p. not_fresh_at sa p ==>
      ~MEM p [len;dp;data;empty;nonempty;selected;sub;b;dst])
Proof
  strip_tac >> drule signed_loader_decompose >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  imp_res_tac emit_op_extends >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString (sa.cs_next_var+3))`,
    `STRING #"%" (toString (sa.cs_next_var+4))`,
    `STRING #"%" (toString (sa.cs_next_var+5))`,
    `STRING #"%" (toString (sa.cs_next_var+6))`] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       ASCIInumbersTheory.toString_inj, mk_inst_def] >>
  fs[same_blocks_def] >>
  qpat_x_assum `not_fresh_at sa src` mp_tac >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED
