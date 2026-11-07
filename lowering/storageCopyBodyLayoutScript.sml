(* Export the compiler body layout: the corresponding S1 helper is local. *)
Theory storageCopyBodyLayout
Ancestors
  list rich_list finite_map pred_set exprLowering emitHelper emitHelperProps
  exprLoweringProps context compileEnv localPtrsProps moduleLoweringProps

Theorem storage_copy_body_layout:
  !loc src dst cv so value scaled dest next stb s1 s2 s3 s4 s5 s6 ste.
    (loc = LocStorage \/ loc = LocTransient) /\
    emit_op ADD [src; Var cv] stb = (so,s1) /\
    compile_ptr_load F NONE loc so s1 = (value,s2) /\
    emit_op MUL [Var cv; Lit 32w] s2 = (scaled,s3) /\
    emit_op ADD [dst; scaled] s3 = (dest,s4) /\
    emit_void MSTORE [dest; value] s4 = ((),s5) /\
    emit_op ADD [Var cv; Lit 1w] s5 = (next,s6) /\
    emit_inst ASSIGN [next] [cv] s6 = ((),ste) ==>
    ?sv vv mv dv nv.
      so = Var sv /\ value = Var vv /\ scaled = Var mv /\
      dest = Var dv /\ next = Var nv /\
      ALL_DISTINCT [sv; vv; mv; dv; nv] /\
      (!x. not_fresh_at stb x ==> ~MEM x [sv; vv; mv; dv; nv]) /\
      same_blocks stb ste /\
      isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      ste.cs_next_var = stb.cs_next_var + 5 /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
        mk_inst (stb.cs_next_id+1)
          (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
        mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_ptr_load_def, emit_op_def, emit_void_def, emit_inst_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED
