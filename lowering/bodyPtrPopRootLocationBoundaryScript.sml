Theory bodyPtrPopRootLocationBoundary
Ancestors bodyPtrPopAllocationBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopLiteralBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardBoundary bodyPtrPopGuardedWindow
  bodyPtrPopWindow exprLowering emitHelper compileEnv venomInst list rich_list context

(* A generic head excluded only from SLOAD/TLOAD is insufficient: it could
   itself be SUB completing an inherited guarded prefix. The full opcode
   barrier below covers the actual non-storage load templates. *)

Theorem pop_nonstorage_guard_separation:
  a.inst_opcode <> SLOAD /\ a.inst_opcode <> TLOAD /\
  a.inst_opcode <> ISZERO /\ a.inst_opcode <> ASSERT /\ a.inst_opcode <> SUB /\
  b.inst_opcode = ISZERO /\ c.inst_opcode = ISZERO /\
  d.inst_opcode = ASSERT /\ e.inst_opcode = SUB ==>
  (occurs5 pop_guarded5 (p ++ [a;b;c;d;e] ++ q) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 q)
Proof
  strip_tac >> Induct_on `p`
  >- simp[occurs5_cons_take, pop_guarded5_head_nonload] >>
  gen_tac >> simp[occurs5_cons_take] >>
  Cases_on `p`
  >- (simp[pop_guarded5_def] >> eq_tac >> strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `t` ["", "j rest"]
  >- (simp[pop_guarded5_def] >> eq_tac >> strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `rest` ["", "k rest2"]
  >- (simp[pop_guarded5_def] >> eq_tac >> strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `rest2` ["", "l rest3"]
  >- (simp[pop_guarded5_def] >> eq_tac >> strip_tac >> gvs[mk_inst_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem pop_nonstorage_template_boundary:
  a.inst_opcode <> SLOAD /\ a.inst_opcode <> TLOAD /\
  a.inst_opcode <> ISZERO /\ a.inst_opcode <> ASSERT /\ a.inst_opcode <> SUB /\
  b.inst_opcode = ISZERO /\ c.inst_opcode = ISZERO /\
  d.inst_opcode = ASSERT /\ e.inst_opcode = SUB /\
  EVERY (\i. i.inst_opcode <> ASSERT) q /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ [a;b;c;d;e] ++ q)
Proof
  strip_tac >>
  `occurs5 pop_guarded5 (p ++ [a;b;c;d;e] ++ []) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 []` by
    (irule pop_nonstorage_guard_separation >> simp[]) >>
  `pop_boundary_clean (p ++ [a;b;c;d;e])` by
    (simp[pop_boundary_clean_def] >> conj_tac
     >- (gvs[occurs5_short] >> metis_tac[pop_boundary_clean_windows]) >>
     `~pop_guard4 ((p ++ [a;b;c;d]) ++ [e])` by
       (irule pop_guard4_snoc_no_assert >> simp[]) >>
     pop_assum (mp_tac o SIMP_RULE std_ss [GSYM APPEND_ASSOC, APPEND]) >>
     simp[]) >>
  irule pop_boundary_clean_append_no_assert >> simp[]
QED

Theorem pop_nonstorage_guard_boundary:
  opc <> SLOAD /\ opc <> TLOAD /\ opc <> ISZERO /\
  opc <> ASSERT /\ opc <> SUB /\ pop_comp_boundary sa /\
  (do len <- emit_op opc [hdr];
      nz <- emit_op ISZERO [len];
      valid <- emit_op ISZERO [nz];
      emit_void ASSERT [valid];
      emit_op SUB [len; Lit 1w]
   od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule (Q.INST [`q` |-> `[]`] pop_nonstorage_template_boundary
         |> SIMP_RULE std_ss [APPEND_NIL, EVERY_DEF]) >>
  simp[mk_inst_def]
QED

Theorem pop_nonstorage_load_guard_boundary:
  loc <> LocStorage /\ loc <> LocTransient /\ pop_comp_boundary sa /\
  (do len <- compile_ptr_load ctor imm loc hdr;
      nz <- emit_op ISZERO [len];
      valid <- emit_op ISZERO [nz];
      emit_void ASSERT [valid];
      emit_op SUB [len; Lit 1w]
   od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def]
  >- (rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`) pop_nonstorage_guard_boundary >> simp[])
  >- (reverse (Cases_on `ctor`) >> simp[compile_imm_load_word_def]
      >- (rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`) pop_nonstorage_guard_boundary >> simp[]) >>
      Cases_on `imm` >> simp[]
      >- (rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`) pop_nonstorage_guard_boundary >> simp[]) >>
      simp[comp_bind_assoc] >> strip_tac >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
      rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`) pop_nonstorage_guard_boundary >> simp[]) >>
  rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`) pop_nonstorage_guard_boundary >> simp[]
QED

Theorem pop_ptr_store_boundary:
  pop_comp_boundary sa /\
  compile_ptr_store ctor imm loc dst v sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_clean_append_no_assert >> simp[mk_inst_def]
QED

Theorem pop_dynarray_guard_split[local]:
  compile_dynarray_pop hdr scale esz ctor imm loc =
  comp_bind
    (do len <- compile_ptr_load ctor imm loc hdr;
        nz <- emit_op ISZERO [len];
        valid <- emit_op ISZERO [nz];
        emit_void ASSERT [valid];
        emit_op SUB [len; Lit 1w] od)
    (\new_len. do
        compile_ptr_store ctor imm loc hdr new_len;
        data_ptr <- emit_op ADD [hdr; Lit (n2w scale)];
        offset <- emit_op MUL [new_len; Lit (n2w esz)];
        emit_op ADD [data_ptr; offset] od)
Proof
  simp[compile_dynarray_pop_def, comp_bind_assoc, comp_ignore_bind_def]
QED

Theorem pop_nonstorage_dynarray_boundary:
  loc <> LocStorage /\ loc <> LocTransient /\ pop_comp_boundary sa /\
  compile_dynarray_pop hdr scale esz ctor imm loc sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[pop_dynarray_guard_split, comp_ignore_bind_def] >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `comp_bind _ _ _ = _`)
        (SRULE [comp_ignore_bind_def] pop_nonstorage_load_guard_boundary) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_ptr_store_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_literal_all_locations_boundary:
  pop_comp_boundary sa /\
  compile_dynarray_pop (Lit h) 1 esz ctor imm loc sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `loc` >> rpt strip_tac
  >- (drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
        pop_nonstorage_dynarray_boundary >> simp[])
  >- (drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
        (Q.INST [`tr` |-> `F`] pop_literal_storage_boundary
         |> SIMP_RULE std_ss []) >> simp[])
  >- (drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
        (Q.INST [`tr` |-> `T`] pop_literal_storage_boundary
         |> SIMP_RULE std_ss []) >> simp[])
  >> drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
       pop_nonstorage_dynarray_boundary >> simp[]
QED
