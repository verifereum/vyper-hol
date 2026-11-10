(* These nonrecursive lists package compiler syntax only.  Naming the three
   chunks avoids copying the encoder's literal instruction lists into its
   pointer-path consumers; unwrap_value remains an opaque compiler call. *)
Theory revertReasonLayout
Ancestors
  stmtLowering exprLoweringProps emitHelper emitHelperProps context compileEnv loweringStateRelDefs fragExec
  arithmetic list rich_list words

Definition revert_reason_prefix_def:
  revert_reason_prefix id (v:num) ms =
    [mk_inst id ALLOCA [Lit (n2w (64+ms))]
       [STRING #"%" (toString v)];
     mk_inst (id+1) MSTORE
       [Var (STRING #"%" (toString v)); Lit 0x08c379a0w] [];
     mk_inst (id+2) ADD
       [Var (STRING #"%" (toString v)); Lit 32w]
       [STRING #"%" (toString (v+1))];
     mk_inst (id+3) ALLOCA [Lit (n2w ms)]
       [STRING #"%" (toString (v+2))]]
End

Definition revert_reason_copy_def:
  revert_reason_copy id (v:num) q op =
    [mk_inst id MLOAD [op] [STRING #"%" (toString v)];
     mk_inst (id+1) ADD [Var (STRING #"%" (toString v)); Lit 31w]
       [STRING #"%" (toString (v+1))];
     mk_inst (id+2) AND
       [Var (STRING #"%" (toString (v+1)));
        Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
       [STRING #"%" (toString (v+2))];
     mk_inst (id+3) ADD [Lit 32w; Var (STRING #"%" (toString (v+2)))]
       [STRING #"%" (toString (v+3))];
     mk_inst (id+4) MCOPY [q; op; Var (STRING #"%" (toString (v+3)))] []]
End

Definition revert_reason_suffix_def:
  revert_reason_suffix id (v:num) b p q =
    [mk_inst (id+5) ALLOCA [Lit 32w] [STRING #"%" (toString (v+4))];
     mk_inst (id+6) MSTORE [Var (STRING #"%" (toString (v+4))); Lit 32w] [];
     mk_inst (id+7) ADD [q; Lit 0w] [STRING #"%" (toString (v+5))];
     mk_inst (id+8) ADD [p; Lit 0w] [STRING #"%" (toString (v+6))];
     mk_inst (id+9) MLOAD [Var (STRING #"%" (toString (v+4)))]
       [STRING #"%" (toString (v+7))];
     mk_inst (id+10) ADD [p; Var (STRING #"%" (toString (v+7)))]
       [STRING #"%" (toString (v+8))];
     mk_inst (id+11) MLOAD [Var (STRING #"%" (toString (v+5)))]
       [STRING #"%" (toString (v+9))];
     mk_inst (id+12) ADD [Var (STRING #"%" (toString (v+9))); Lit 31w]
       [STRING #"%" (toString (v+10))];
     mk_inst (id+13) AND [Var (STRING #"%" (toString (v+10)));
       Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
       [STRING #"%" (toString (v+11))];
     mk_inst (id+14) ADD [Var (STRING #"%" (toString (v+8)));
       Var (STRING #"%" (toString (v+11)))] [STRING #"%" (toString (v+12))];
     mk_inst (id+15) MSTORE [Var (STRING #"%" (toString (v+12))); Lit 0w] [];
     mk_inst (id+16) ADD [Lit 32w; Var (STRING #"%" (toString (v+9)))]
       [STRING #"%" (toString (v+13))];
     mk_inst (id+17) MCOPY [Var (STRING #"%" (toString (v+8)));
       Var (STRING #"%" (toString (v+5))); Var (STRING #"%" (toString (v+13)))] [];
     mk_inst (id+18) ADD [Var (STRING #"%" (toString (v+9))); Lit 31w]
       [STRING #"%" (toString (v+14))];
     mk_inst (id+19) AND [Var (STRING #"%" (toString (v+14)));
       Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
       [STRING #"%" (toString (v+15))];
     mk_inst (id+20) ADD [Lit 32w; Var (STRING #"%" (toString (v+15)))]
       [STRING #"%" (toString (v+16))];
     mk_inst (id+21) MSTORE [Var (STRING #"%" (toString (v+6)));
       Var (STRING #"%" (toString (v+7)))] [];
     mk_inst (id+22) ADD [Var (STRING #"%" (toString (v+7)));
       Var (STRING #"%" (toString (v+16)))] [STRING #"%" (toString (v+17))];
     mk_inst (id+23) MSTORE [Var (STRING #"%" (toString (v+4)));
       Var (STRING #"%" (toString (v+17)))] [];
     mk_inst (id+24) MLOAD [Var (STRING #"%" (toString (v+4)))]
       [STRING #"%" (toString (v+18))];
     mk_inst (id+25) ADD [b; Lit 28w] [STRING #"%" (toString (v+19))];
     mk_inst (id+26) ADD [Lit 4w; Var (STRING #"%" (toString (v+18)))]
       [STRING #"%" (toString (v+20))];
     mk_inst (id+27) REVERT [Var (STRING #"%" (toString (v+19)));
       Var (STRING #"%" (toString (v+20)))] []]
End

Theorem revert_reason_chunk_lengths[simp]:
  LENGTH (revert_reason_prefix id v ms) = 4 /\
  LENGTH (revert_reason_copy id v q op) = 5 /\
  LENGTH (revert_reason_suffix id v b p q) = 23
Proof
  simp[revert_reason_prefix_def, revert_reason_copy_def, revert_reason_suffix_def]
QED

Theorem compile_revert_reason_layout:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==>
  ?sm sn op.
    sm = sa with <| cs_next_var := sa.cs_next_var + 3;
      cs_next_id := sa.cs_next_id + 4;
      cs_current_insts := sa.cs_current_insts ++
        revert_reason_prefix sa.cs_next_id sa.cs_next_var ms |> /\
    unwrap_value cenv vv sm = (op,sn) /\
    sb = sn with <| cs_next_var := sn.cs_next_var + 21;
      cs_next_id := sn.cs_next_id + 28;
      cs_current_insts := sn.cs_current_insts ++
        (revert_reason_copy sn.cs_next_id sn.cs_next_var
          (Var (STRING #"%" (toString (sa.cs_next_var+2)))) op ++
         revert_reason_suffix sn.cs_next_id sn.cs_next_var
          (Var (STRING #"%" (toString sa.cs_next_var)))
          (Var (STRING #"%" (toString (sa.cs_next_var+1))))
          (Var (STRING #"%" (toString (sa.cs_next_var+2))))) |>
Proof
  simp[compile_revert_with_reason_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  qmatch_goalsub_abbrev_tac `unwrap_value cenv vv sm` >>
  pairarg_tac >> rename1 `unwrap_value cenv vv sm = (op,sn)` >>
  simp[] >> strip_tac >> qexistsl_tac [`sn`, `op`] >>
  qpat_x_assum `_ = sb` (SUBST_ALL_TAC o SYM) >>
  pure_rewrite_tac[revert_reason_prefix_def, revert_reason_copy_def,
       revert_reason_suffix_def, GSYM APPEND_ASSOC, APPEND] >>
  simp[Abbr `sm`, ADD_COMM] >>
  pop_assum mp_tac >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

Theorem compile_revert_reason_chunks:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==>
  ?sm sn op.
    unwrap_value cenv vv sm = (op,sn) /\
    same_blocks sa sm /\ same_blocks sn sb /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    sm.cs_next_var <= sn.cs_next_var /\
    sm.cs_next_id <= sn.cs_next_id /\ 
    sm.cs_next_var = sa.cs_next_var + 3 /\
    sm.cs_next_id = sa.cs_next_id + 4 /\
    sb.cs_next_var = sn.cs_next_var + 21 /\
    sb.cs_next_id = sn.cs_next_id + 28 /\
    emitted_insts sa sm = revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    emitted_insts sn sb =
      revert_reason_copy sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))) op ++
      revert_reason_suffix sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString sa.cs_next_var)))
        (Var (STRING #"%" (toString (sa.cs_next_var+1))))
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))) /\
    sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb
Proof
  strip_tac >> drule compile_revert_reason_layout >> strip_tac >>
  `ci_mono sm sn` by
    (qspecl_then [`cenv`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  qexistsl_tac [`sm`, `sn`, `op`] >>
  gvs[same_blocks_def, emitted_insts_def, ci_mono_def, cs_extends_def, DROP_APPEND1] >>
  rewrite_tac[GSYM APPEND_ASSOC, IS_PREFIX_APPEND] >> simp[]
QED

Theorem revert_reason_chunk_outputs_fresh:
  s.cs_next_var <= v ==>
  EVERY (\i. EVERY (\x. ~not_fresh_at s x) i.inst_outputs)
    (revert_reason_prefix id v ms) /\
  EVERY (\i. EVERY (\x. ~not_fresh_at s x) i.inst_outputs)
    (revert_reason_copy id v q op) /\
  EVERY (\i. EVERY (\x. ~not_fresh_at s x) i.inst_outputs)
    (revert_reason_suffix id v b p q)
Proof
  strip_tac >>
  simp[revert_reason_prefix_def, revert_reason_copy_def,
       revert_reason_suffix_def, venomInstTheory.mk_inst_def, not_fresh_at_def] >>
  rpt conj_tac >> strip_tac >> first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

