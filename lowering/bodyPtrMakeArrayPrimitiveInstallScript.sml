(* Finite compiler expansions.  Fetches refer to the installed final function,
   not to a fixed-run execution witness. *)
Theory bodyPtrMakeArrayPrimitiveInstall
Ancestors
  bodyPtrMakeArrayEmission context fragExec emitHelperProps exprLoweringProps
  compileEnv emitHelper venomInst venomState list rich_list

Theorem typed_word_copy_install_shape:
  is_word_type dt /\
  compile_store_memory_typed ce dst dt src st sa = ((),sb) ==>
  ?tmp.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [src] [tmp];
       mk_inst (sa.cs_next_id + 1) MSTORE [dst; Var tmp] []] /\
    sb.cs_next_var = sa.cs_next_var + 1 /\
    sb.cs_next_id = sa.cs_next_id + 2 /\
    (!x. not_fresh_at sa x ==> x <> tmp)
Proof
  simp[Once compile_store_memory_typed_def] >>
  strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[APPEND_ASSOC, not_fresh_at_def]
QED

Theorem bytestring_copy_len_install_shape:
  compile_bytestring_copy_len src sa = (out,sb) ==>
  ?a b c d.
    out = Var d /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [src] [a];
       mk_inst (sa.cs_next_id + 1) ADD [Var a; Lit 31w] [b];
       mk_inst (sa.cs_next_id + 2) AND [Var b; Lit (i2w (- &32))] [c];
       mk_inst (sa.cs_next_id + 3) ADD [Var c; Lit 32w] [d]] /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 4 /\
    (!x. not_fresh_at sa x ==> x <> a /\ x <> b /\ x <> c /\ x <> d)
Proof
  strip_tac >>
  gvs[compile_bytestring_copy_len_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`] >>
  simp[APPEND_ASSOC, not_fresh_at_def]
QED

Theorem bytestring_store_install_shape:
  compile_store_bytestring src dst sa = ((),sb) ==>
  ?a b c d.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [src] [a];
       mk_inst (sa.cs_next_id + 1) ADD [Var a; Lit 31w] [b];
       mk_inst (sa.cs_next_id + 2) AND [Var b; Lit (i2w (- &32))] [c];
       mk_inst (sa.cs_next_id + 3) ADD [Var c; Lit 32w] [d];
       mk_inst (sa.cs_next_id + 4) MCOPY [dst; src; Var d] []] /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 5 /\
    (!x. not_fresh_at sa x ==> x <> a /\ x <> b /\ x <> c /\ x <> d)
Proof
  strip_tac >>
  Cases_on `compile_bytestring_copy_len src sa` >>
  gvs[compile_store_bytestring_def, comp_bind_def] >>
  drule bytestring_copy_len_install_shape >> strip_tac >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_return_def] >>
  qexistsl_tac [`a`, `b`, `c`, `d`] >> simp[APPEND_ASSOC]
QED

(* This single-instruction boundary does not inspect the copy count: it is
   also applicable when that operand evaluates to zero. *)
Theorem emit_void_fetch_boundary:
  emit_void opc args sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id opc args []) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
        comp_return_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all fn_has_code_same_block >> simp[] >> strip_tac >>
  qexists_tac `bb` >> simp[]
QED

Theorem typed_word_copy_fetch:
  is_word_type dt /\
  compile_store_memory_typed ce dst dt src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?tmp bb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id MLOAD [src] [tmp]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id + 1) MSTORE [dst; Var tmp] []) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2 /\
    (!x. not_fresh_at sa x ==> x <> tmp)
Proof
  strip_tac >> drule_all typed_word_copy_install_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`tmp`, `bb`] >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1] >>
  metis_tac[]
QED

Theorem bytestring_copy_len_fetch:
  compile_bytestring_copy_len src sa = (out,sb) /\
  fn_has_code sa sb fn ==>
  ?a b c d bb.
    out = Var d /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    (!i. i < 4 ==>
      get_instruction bb (LENGTH sa.cs_current_insts + i) = SOME (EL i
        [mk_inst sa.cs_next_id MLOAD [src] [a];
         mk_inst (sa.cs_next_id + 1) ADD [Var a; Lit 31w] [b];
         mk_inst (sa.cs_next_id + 2) AND [Var b; Lit (i2w (- &32))] [c];
         mk_inst (sa.cs_next_id + 3) ADD [Var c; Lit 32w] [d]])) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 4 /\
    (!x. not_fresh_at sa x ==> x <> a /\ x <> b /\ x <> c /\ x <> d)
Proof
  strip_tac >> drule bytestring_copy_len_install_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`a`, `b`, `c`, `d`, `bb`] >> simp[]
QED

Theorem bytestring_store_fetch:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?a b c d bb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    (!i. i < 5 ==>
      get_instruction bb (LENGTH sa.cs_current_insts + i) = SOME (EL i
        [mk_inst sa.cs_next_id MLOAD [src] [a];
         mk_inst (sa.cs_next_id + 1) ADD [Var a; Lit 31w] [b];
         mk_inst (sa.cs_next_id + 2) AND [Var b; Lit (i2w (- &32))] [c];
         mk_inst (sa.cs_next_id + 3) ADD [Var c; Lit 32w] [d];
         mk_inst (sa.cs_next_id + 4) MCOPY [dst; src; Var d] []])) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 5 /\
    (!x. not_fresh_at sa x ==> x <> a /\ x <> b /\ x <> c /\ x <> d)
Proof
  strip_tac >> drule bytestring_store_install_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`a`, `b`, `c`, `d`, `bb`] >> simp[]
QED
