(* Experimental entry class supplied by the image PLAN.  Unlike global
   reachability, these predicates inspect only finite instruction lists.
   They are NOT established invariants of the supported compiler. *)
Theory bodyPtrBytestringBuiltinsImageFrontier
Ancestors bodyPtrBytestringBuiltinsImageBoundary compileEnv emitHelper
          venomInst list rich_list arithmetic exprLowering context supportedExprs vyperAST

Definition image_bad_def:
  image_bad xs <=>
    ?p q i0 i1 i2 i3 w b data off.
      xs = p ++ [mk_inst i0 ALLOCA [Lit w] [b];
                 mk_inst i1 ADD [Var b; Lit 32w] [data];
                 mk_inst i2 ALLOCA [Lit 64w] [off];
                 mk_inst i3 MSTORE [Var off; Lit 0w] []] ++ q
End

Definition image_pending2_def:
  image_pending2 xs <=>
    ?i0 i1 w b data p.
      xs = p ++ [mk_inst i0 ALLOCA [Lit w] [b];
                 mk_inst i1 ADD [Var b; Lit 32w] [data]]
End

Definition image_pending3_def:
  image_pending3 xs <=>
    ?i0 i1 i2 w b data off p.
      xs = p ++ [mk_inst i0 ALLOCA [Lit w] [b];
                 mk_inst i1 ADD [Var b; Lit 32w] [data];
                 mk_inst i2 ALLOCA [Lit 64w] [off]]
End

Definition image_entry_def:
  image_entry st <=>
    EVERY (\bb. ~image_bad bb.bb_instructions) st.cs_blocks /\
    ~image_bad st.cs_current_insts /\
    ~image_pending2 st.cs_current_insts /\
    ~image_pending3 st.cs_current_insts
End

Theorem image_empty_lists[simp]:
  ~image_bad [] /\ ~image_pending2 [] /\ ~image_pending3 []
Proof
  simp[image_bad_def, image_pending2_def, image_pending3_def]
QED

Theorem image_entry_empty:
  st.cs_blocks = [] /\ st.cs_current_insts = [] ==> image_entry st
Proof
  simp[image_entry_def]
QED

Theorem image_entry_fresh_var:
  fresh_var st = (v,t) ==> (image_entry t <=> image_entry st)
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[image_entry_def]
QED

Theorem image_entry_new_block:
  image_entry st /\ new_block label st = (old,t) ==> image_entry t
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[image_entry_def]
QED

Theorem image_pending2_bounded:
  image_pending2 xs <=> image_pending2 (REVERSE (TAKE 3 (REVERSE xs)))
Proof
  simp[image_pending2_def, GSYM bounded_suffix_detect]
QED

Theorem image_pending3_bounded:
  image_pending3 xs <=> image_pending3 (REVERSE (TAKE 3 (REVERSE xs)))
Proof
  simp[image_pending3_def, GSYM bounded_suffix_detect]
QED

(* A no-emission callback satisfies the proposed child interface for ALL
   inputs, including supported ones.  No result-validity premise was supplied. *)
Theorem image_no_emission_child_contract:
  !vv st. image_entry st ==>
    image_entry (SND (comp_return vv st)) /\
    st.cs_next_var <= (SND (comp_return vv st)).cs_next_var
Proof
  simp[comp_return_def]
QED

(* Diagnostic only: an empty-layout child causes no store to separate the
   parent's allocation and destination ADD.  The contract does not restrict
   the tuple helper's offset, child's representation, or zero-sized layouts. *)
Theorem image_zero_tuple_continuation_trace:
  !cenv st buf sm out t.
    st.cs_current_insts = [] /\
    compile_alloc_buffer 64 st = (buf,sm) /\
    compile_make_tuple
      (\ce ty e. comp_return (StackValue (TupleT []) (Lit 0w))) cenv
      [Name (TupleT []) "empty"] buf.buf_operand 32 sm = (out,t) ==>
    t.cs_current_insts =
      [mk_inst st.cs_next_id ALLOCA [Lit 64w] ["%" ++ toString st.cs_next_var];
       mk_inst (st.cs_next_id + 1) ADD
         [Var ("%" ++ toString st.cs_next_var); Lit 32w]
         ["%" ++ toString (st.cs_next_var + 1)]]
Proof
  simp[compile_alloc_buffer_def, compile_make_tuple_def, unwrap_value_def,
       compile_store_memory_def, compile_copy_memory_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[expr_type_def, lowered_value_type_def,
    is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
    compile_copy_memory_def, comp_return_def]
QED

Theorem image_pending2_pair[simp]:
  !i0 i1 w b d.
    image_pending2 [mk_inst i0 ALLOCA [Lit w] [b];
                    mk_inst i1 ADD [Var b; Lit 32w] [d]]
Proof
  rpt gen_tac >> simp[image_pending2_def] >>
  metis_tac[]
QED

Theorem image_zero_tuple_child_supported:
  !tops. supported_pure_expr tops (Name (TupleT []) "empty")
Proof
  simp[supported_pure_expr_def]
QED

Theorem image_zero_tuple_continuation_not_entry:
  !cenv st buf sm out t.
    st.cs_current_insts = [] /\ st.cs_blocks = [] /\
    compile_alloc_buffer 64 st = (buf,sm) /\
    compile_make_tuple
      (\ce ty e. comp_return (StackValue (TupleT []) (Lit 0w))) cenv
      [Name (TupleT []) "empty"] buf.buf_operand 32 sm = (out,t) ==>
    image_entry st /\ ~image_entry t
Proof
  rpt gen_tac >> strip_tac >> conj_tac >- simp[image_entry_def] >>
  drule_all image_zero_tuple_continuation_trace >>
  strip_tac >> gvs[image_entry_def]
QED
