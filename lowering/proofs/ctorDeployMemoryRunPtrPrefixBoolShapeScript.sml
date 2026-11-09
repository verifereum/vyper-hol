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
          mk_inst id ADD [Var src; Lit 32w] [x 0];
          mk_inst (id+1) LT [Var(x 0); Var src] [x 1];
          mk_inst (id+2) ISZERO [Var(x 1)] [x 2];
          mk_inst (id+3) GT [Var(x 0); Lit(n2w data_size)] [x 3];
          mk_inst (id+4) ISZERO [Var(x 3)] [x 4];
          mk_inst (id+5) AND [Var(x 2); Var(x 4)] [x 5];
          mk_inst (id+6) ASSERT [Var(x 5)] [];
          mk_inst (id+7) DLOAD [Var src] [x 6];
          mk_inst (id+8) GT [Var(x 6); Lit(n2w max_count)] [x 7];
          mk_inst (id+9) ISZERO [Var(x 7)] [x 8];
          mk_inst (id+10) ASSERT [Var(x 8)] [];
          mk_inst (id+11) MUL [Var(x 6); Lit 32w] [x 9];
          mk_inst (id+12) ADD [Var(x 0); Var(x 9)] [x 10];
          mk_inst (id+13) LT [Var(x 10); Var(x 0)] [x 11];
          mk_inst (id+14) ISZERO [Var(x 11)] [x 12];
          mk_inst (id+15) GT [Var(x 10); Lit(n2w data_size)] [x 13];
          mk_inst (id+16) ISZERO [Var(x 13)] [x 14];
          mk_inst (id+17) AND [Var(x 12); Var(x 14)] [x 15];
          mk_inst (id+18) ASSERT [Var(x 15)] [];
          mk_inst (id+19) DLOAD [Var src] [x 16];
          mk_inst (id+20) MSTORE [Var dst; Var(x 16)] [];
          mk_inst (id+21) ALLOCA [Lit 32w] [x 17];
          mk_inst (id+22) MSTORE [Var(x 17); Lit 0w] [];
          mk_inst (id+23) JMP [Label hd] []];
        header = abi_decode_header_insts (id+24) (Var(x 17)) (Var src)
          DLOAD (x 18) (x 19) (x 20) (x 21) body ex;
        bod = [
          mk_inst (id+29) MLOAD [Var(x 17)] [x 22];
          mk_inst (id+30) ADD [Var src; Lit 32w] [x 23];
          mk_inst (id+31) MUL [Var(x 22); Lit 32w] [x 24];
          mk_inst (id+32) ADD [Var(x 23); Var(x 24)] [x 25];
          mk_inst (id+33) ADD [Var dst; Lit 32w] [x 26];
          mk_inst (id+34) MUL [Var(x 22); Lit 32w] [x 27];
          mk_inst (id+35) ADD [Var(x 26); Var(x 27)] [x 28];
          mk_inst (id+36) DLOAD [Var(x 25)] [x 29];
          mk_inst (id+37) SHR [Lit 1w; Var(x 29)] [x 30];
          mk_inst (id+38) ISZERO [Var(x 30)] [x 31];
          mk_inst (id+39) ASSERT [Var(x 31)] [];
          mk_inst (id+40) MSTORE [Var(x 28); Var(x 29)] [];
          mk_inst (id+41) ADD [Var(x 22); Lit 1w] [x 32];
          mk_inst (id+42) MSTORE [Var(x 17); Var(x 32)] [];
          mk_inst (id+43) JMP [Label hd] []]
    in
      compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit 0w)
        (Lit(n2w data_size))
        (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st =
      ((), st with <|
        cs_next_id := id+44; cs_next_var := st.cs_next_var+33;
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
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def, compile_abi_decode_static_def,
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
  compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit 0w) (Lit(n2w data_size))
    (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) ==>
  sf.cs_next_id = st.cs_next_id + 44 /\
  sf.cs_next_var = st.cs_next_var + 33 /\
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
  compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit 0w) (Lit(n2w data_size))
    (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      pre = (EL 2 sf.cs_blocks).bb_instructions;
      bod = (EL 0 sf.cs_blocks).bb_instructions;
      n = LENGTH st.cs_current_insts;
      id = st.cs_next_id
  in
    EL (n+10) pre = mk_inst (id+10) ASSERT [Var(x 8)] [] /\
    EL (n+18) pre = mk_inst (id+18) ASSERT [Var(x 15)] [] /\
    EL (n+21) pre = mk_inst (id+21) ALLOCA [Lit 32w] [x 17] /\
    EL 10 bod = mk_inst (id+39) ASSERT [Var(x 31)] []
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
