(* Exact finite compiler specialization; no runtime correctness is asserted. *)
Theory ctorDeployMemoryRunPtrPrefixBoolShape
Ancestors
  loweringStateRelDefs
  abiEncoder abiDecoderExecution context emitHelper compileEnv fragExec
  exprLoweringProps emitHelperProps words arithmetic list ASCIInumbers

Theorem prefix_bool_decode_compile:
  !st dst src data_size max_count.
    0 < data_size /\ data_size < dimword(:256) ==>
    let x = (\k. "%" ++ toString (st.cs_next_var+k));
        hd = fresh_label_output "dec_dyn_hdr" st.cs_next_label;
        body = fresh_label_output "dec_dyn_body" (st.cs_next_label+1);
        ex = fresh_label_output "dec_dyn_exit" (st.cs_next_label+2);
        id = st.cs_next_id;
        pre = [
          mk_inst id DLOAD [Var src] [x 0];
          mk_inst (id+1) GT [Var(x 0); Lit(n2w max_count)] [x 1];
          mk_inst (id+2) ISZERO [Var(x 1)] [x 2];
          mk_inst (id+3) ASSERT [Var(x 2)] [];
          mk_inst (id+4) MUL [Var(x 0); Lit 32w] [x 3];
          mk_inst (id+5) ADD [Var(x 3); Lit 32w] [x 4];
          mk_inst (id+6) ADD [Var src; Var(x 4)] [x 5];
          mk_inst (id+7) GT [Var(x 5); Lit(n2w data_size)] [x 6];
          mk_inst (id+8) ISZERO [Var(x 6)] [x 7];
          mk_inst (id+9) ASSERT [Var(x 7)] [];
          mk_inst (id+10) DLOAD [Var src] [x 8];
          mk_inst (id+11) MSTORE [Var dst; Var(x 8)] [];
          mk_inst (id+12) ALLOCA [Lit 32w] [x 9];
          mk_inst (id+13) MSTORE [Var(x 9); Lit 0w] [];
          mk_inst (id+14) JMP [Label hd] []];
        header = abi_decode_header_insts (id+15) (Var(x 9)) (Var src)
          DLOAD (x 10) (x 11) (x 12) (x 13) body ex;
        bod = [
          mk_inst (id+20) MLOAD [Var(x 9)] [x 14];
          mk_inst (id+21) ADD [Var src; Lit 32w] [x 15];
          mk_inst (id+22) MUL [Var(x 14); Lit 32w] [x 16];
          mk_inst (id+23) ADD [Var(x 15); Var(x 16)] [x 17];
          mk_inst (id+24) ADD [Var dst; Lit 32w] [x 18];
          mk_inst (id+25) MUL [Var(x 14); Lit 32w] [x 19];
          mk_inst (id+26) ADD [Var(x 18); Var(x 19)] [x 20];
          mk_inst (id+27) DLOAD [Var(x 17)] [x 21];
          mk_inst (id+28) SHR [Lit 1w; Var(x 21)] [x 22];
          mk_inst (id+29) ISZERO [Var(x 22)] [x 23];
          mk_inst (id+30) ASSERT [Var(x 23)] [];
          mk_inst (id+31) MSTORE [Var(x 20); Var(x 21)] [];
          mk_inst (id+32) ADD [Var(x 14); Lit 1w] [x 24];
          mk_inst (id+33) MSTORE [Var(x 9); Var(x 24)] [];
          mk_inst (id+34) JMP [Label hd] []]
    in
      compile_abi_decode_to_buf (Var dst) (Var src) DLOAD
        (Lit(n2w data_size))
        (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st =
      ((), st with <|
        cs_next_id := id+35; cs_next_var := st.cs_next_var+25;
        cs_next_label := st.cs_next_label+3;
        cs_current_bb := ex; cs_current_insts := [];
        cs_blocks := <|bb_label := body; bb_instructions := bod|> ::
                     <|bb_label := hd; bb_instructions := header|> ::
                     <|bb_label := st.cs_current_bb;
                       bb_instructions := st.cs_current_insts ++ pre|> ::
                     st.cs_blocks |> )
Proof
  rpt strip_tac >>
  `n2w data_size <> (0w:bytes32)` by simp[n2w_11] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, needs_clamp_def, dec_info_needs_clamp_def,
       dec_info_needs_offset_def, compile_alloc_buffer_def,
       abi_decode_header_insts_def] >>
  simp[emit_op_def, emit_void_def, emit_inst_def] >>
  simp[Ntimes comp_bind_def 20, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, fresh_label_def, new_block_def] >>
  simp[Ntimes comp_bind_def 20, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, fresh_label_def, new_block_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, fresh_label_def, new_block_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem prefix_bool_decode_counters:
  0 < data_size /\ data_size < dimword(:256) /\
  compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit(n2w data_size))
    (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) ==>
  sf.cs_next_id = st.cs_next_id + 35 /\
  sf.cs_next_var = st.cs_next_var + 25 /\
  sf.cs_next_label = st.cs_next_label + 3 /\
  sf.cs_current_bb = fresh_label_output "dec_dyn_exit" (st.cs_next_label+2) /\
  sf.cs_current_insts = [] /\
  LENGTH sf.cs_blocks = LENGTH st.cs_blocks + 3
Proof
  rpt strip_tac >> drule_all prefix_bool_decode_compile >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem prefix_bool_decode_checks:
  0 < data_size /\ data_size < dimword(:256) /\
  compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit(n2w data_size))
    (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      pre = (EL 2 sf.cs_blocks).bb_instructions;
      bod = (EL 0 sf.cs_blocks).bb_instructions;
      n = LENGTH st.cs_current_insts;
      id = st.cs_next_id
  in
    EL (n+3) pre = mk_inst (id+3) ASSERT [Var(x 2)] [] /\
    EL (n+9) pre = mk_inst (id+9) ASSERT [Var(x 7)] [] /\
    EL (n+12) pre = mk_inst (id+12) ALLOCA [Lit 32w] [x 9] /\
    EL 10 bod = mk_inst (id+30) ASSERT [Var(x 23)] []
Proof
  rpt strip_tac >> drule_all prefix_bool_decode_compile >>
  simp[] >> strip_tac >> gvs[] >> simp[EL_APPEND_EQN]
QED

(* Every generated variable is different, not merely adjacent temporaries. *)
Theorem prefix_bool_decode_var_inj:
  !st i j.
    ("%" ++ toString (st.cs_next_var+i) =
     "%" ++ toString (st.cs_next_var+j)) <=> i = j
Proof
  simp[toString_11]
QED

Theorem prefix_bool_decode_var_separation:
  not_fresh_at st v ==>
  !i. v <> "%" ++ toString (st.cs_next_var+i)
Proof
  simp[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st.cs_next_var+i` mp_tac) >> simp[]
QED

Theorem prefix_bool_decode_vars_absent:
  fresh_vars_wrt st s ==>
  !i. "%" ++ toString (st.cs_next_var+i) NOTIN FDOM s.vs_vars
Proof
  simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st.cs_next_var+i` mp_tac) >> simp[]
QED

Theorem prefix_bool_decode_labels_distinct:
  !st.
    ALL_DISTINCT
      [fresh_label_output "dec_dyn_hdr" st.cs_next_label;
       fresh_label_output "dec_dyn_body" (st.cs_next_label+1);
       fresh_label_output "dec_dyn_exit" (st.cs_next_label+2)]
Proof
  simp[ALL_DISTINCT] >> rpt strip_tac >>
  drule fresh_label_output_inj >> simp[]
QED

(* fn_has_code covers all three finished blocks exactly. Its final partial
   exit block need only exist: it is not necessarily an empty function block. *)
Theorem prefix_bool_decode_blocks_lookup:
  sf.cs_blocks = bod :: hdr :: pre :: st.cs_blocks /\
  sf.cs_current_insts = [] /\ fn_has_code st sf fn ==>
  lookup_block bod.bb_label fn.fn_blocks = SOME bod /\
  lookup_block hdr.bb_label fn.fn_blocks = SOME hdr /\
  lookup_block pre.bb_label fn.fn_blocks = SOME pre /\
  ?exit. lookup_block sf.cs_current_bb fn.fn_blocks = SOME exit
Proof
  simp[fn_has_code_def, emitted_blocks_def] >> metis_tac[]
QED

val _ = export_theory();
