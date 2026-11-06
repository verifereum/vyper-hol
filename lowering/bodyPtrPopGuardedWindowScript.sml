Theory bodyPtrPopGuardedWindow
Ancestors
  bodyPtrPopWindow bodyPtrPopSuffixSignature bodyPtrPopProducerAudit
  exprLowering emitHelper compileEnv venomInst context list rich_list

(* Factor the operand-sensitive signature shared by containment and compiler
   composition. Instruction identifiers are deliberately unconstrained. *)
Definition pop_guarded5_def:
  pop_guarded5 w <=>
    ?tr h a b c d i0 i1 i2 i3 i4.
      w = [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
           mk_inst i1 ISZERO [Var a] [b];
           mk_inst i2 ISZERO [Var b] [c];
           mk_inst i3 ASSERT [Var c] [];
           mk_inst i4 SUB [Var a; Lit 1w] [d]]
End

Theorem pop_guarded5_instance:
  pop_guarded5
    [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
     mk_inst i1 ISZERO [Var a] [b];
     mk_inst i2 ISZERO [Var b] [c];
     mk_inst i3 ASSERT [Var c] [];
     mk_inst i4 SUB [Var a; Lit 1w] [d]]
Proof
  simp[pop_guarded5_def] >> metis_tac[]
QED

Theorem pop_guarded5_snoc:
  pop_guarded5 (xs ++ [i]) <=>
    ?tr h a b c d i0 i1 i2 i3 i4.
      xs = [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
            mk_inst i1 ISZERO [Var a] [b];
            mk_inst i2 ISZERO [Var b] [c];
            mk_inst i3 ASSERT [Var c] []] /\
      i = mk_inst i4 SUB [Var a; Lit 1w] [d]
Proof
  simp[pop_guarded5_def]
QED

Theorem pop_guarded5_decrement_residual:
  occurs5 pop_guarded5 (xs ++ [mk_inst iid SUB [lhs; rhs] [dst]]) <=>
    occurs5 pop_guarded5 xs \/
    (?tr h a b c i0 i1 i2 i3.
      4 <= LENGTH xs /\
      tail4 xs =
        [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
         mk_inst i1 ISZERO [Var a] [b];
         mk_inst i2 ISZERO [Var b] [c];
         mk_inst i3 ASSERT [Var c] []] /\
      lhs = Var a /\ rhs = Lit 1w)
Proof
  simp[occurs5_snoc, pop_guarded5_snoc, mk_inst_def] >> metis_tac[]
QED

Theorem pop_guarded5_append_no_sub:
  EVERY (\i. i.inst_opcode <> SUB) ys ==>
  (occurs5 pop_guarded5 (xs ++ ys) <=> occurs5 pop_guarded5 xs)
Proof
  qid_spec_tac `xs` >> Induct_on `ys` using SNOC_INDUCT
  >- simp[] >>
  simp[SNOC_APPEND, EVERY_APPEND] >> rpt strip_tac >>
  `!zs. ~pop_guarded5 (zs ++ [x])` by
    (simp[pop_guarded5_snoc] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  simp[occurs5_snoc]
QED

Theorem pop_storage_guarded_fn_window:
  compile_dynarray_pop (Var h) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code si sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
       occurs5 pop_guarded5 bb.bb_instructions
Proof
  strip_tac >> drule_all pop_storage_suffix_fn_window >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  irule occurs5_append_left >> irule occurs5_append_right >>
  simp[occurs5_def] >>
  qexistsl_tac [`[]`,
    `[mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Var h] [x0];
      mk_inst (sa.cs_next_id+1) ISZERO [Var x0] [x1];
      mk_inst (sa.cs_next_id+2) ISZERO [Var x1] [x2];
      mk_inst (sa.cs_next_id+3) ASSERT [Var x2] [];
      mk_inst (sa.cs_next_id+4) SUB [Var x0; Lit 1w] [x3]]`,
    `[mk_inst (sa.cs_next_id+5) (if tr then TSTORE else SSTORE)
        [Var h; Var x3] [];
      mk_inst (sa.cs_next_id+6) ADD [Var h; Lit 1w] [x4];
      mk_inst (sa.cs_next_id+7) MUL [Var x3; Lit (n2w esz)] [x5];
      mk_inst (sa.cs_next_id+8) ADD [Var x4; Var x5] [x6]]`] >>
  simp[pop_guarded5_instance]
QED

Theorem pop_unsigned_div_guarded_window:
  ~is_signed_type ty /\ compile_safe_div x y ty sa = (out,sb) ==>
  (occurs5 pop_guarded5 sb.cs_current_insts <=>
   occurs5 pop_guarded5 sa.cs_current_insts)
Proof
  strip_tac >>
  gvs[compile_safe_div_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule pop_guarded5_append_no_sub >> simp[mk_inst_def]
QED

Theorem pop_mod_guarded_window:
  compile_safe_mod x y ty sa = (out,sb) ==>
  (occurs5 pop_guarded5 sb.cs_current_insts <=>
   occurs5 pop_guarded5 sa.cs_current_insts)
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule pop_guarded5_append_no_sub >> simp[mk_inst_def]
QED
