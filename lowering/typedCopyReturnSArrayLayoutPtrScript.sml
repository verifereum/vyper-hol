(* Compiler slices for the counted fixed-array typed-copy loop. *)
Theory typedCopyReturnSArrayLayoutPtr
Ancestors typedCopyLoopLayoutPtr typedCopyArrayPtr typedMemoryCopy typedNormalizeLoop
  emitHelperProps freshWrites
  fragExec exprLoweringProps compileEnv emitHelper context words list

Theorem typed_copy_sarray_slow_emit_slices:
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce (Var dst) dty (Var src) sty N sa = ((),sz) ==>
  ?hdr body exit ctr lt done so doff sp dp inc
   l1 l2 l3 init st0 st1 sth h1 stj st2 stb c1 c2 c3 si se c6 ste st3 u1 u2 u3.
    fresh_label "typed_sa_cond" sa = (hdr,l1) /\
    fresh_label "typed_sa_body" l1 = (body,l2) /\
    fresh_label "typed_sa_exit" l2 = (exit,l3) /\
    fresh_var l3 = (ctr,init) /\
    emit_inst ASSIGN [Lit 0w] [ctr] init = ((),st0) /\
    emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
    new_block hdr st1 = (u1,sth) /\
    emit_op LT [Var ctr;Lit (n2w N)] sth = (Var lt,h1) /\
    emit_op ISZERO [Var lt] h1 = (Var done,stj) /\
    emit_inst JNZ [Var done;Label exit;Label body] [] stj = ((),st2) /\
    new_block body st2 = (u2,stb) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce sty))] stb = (Var so,c1) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dty))] c1 = (Var doff,c2) /\
    emit_op ADD [Var src;Var so] c2 = (Var sp,c3) /\
    emit_op ADD [Var dst;Var doff] c3 = (Var dp,si) /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
    emit_op ADD [Var ctr;Lit 1w] se = (Var inc,c6) /\
    emit_inst ASSIGN [Var inc] [ctr] c6 = ((),ste) /\
    emit_inst JMP [Label hdr] [] ste = ((),st3) /\
    new_block exit st3 = (u3,sz) /\
    (fn_has_code sa sz fn ==>
      fn_has_code stb c1 fn /\ fn_has_code c1 c2 fn /\
      fn_has_code c2 c3 fn /\ fn_has_code c3 si fn /\
      fn_has_code si se fn)
Proof
  strip_tac >>
  drule compile_copy_sarray_typed_slow >>
  disch_then (qspecl_then [`Var dst`,`Var src`,`N`,`sa`,`sz`] mp_tac) >>
  simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  `?lt. lt_op = Var lt` by metis_tac[emitted_insts_emit_op] >>
  `?done. done_op = Var done` by metis_tac[emitted_insts_emit_op] >>
  `?so. src_off = Var so` by metis_tac[emitted_insts_emit_op] >>
  `?doff. dst_off = Var doff` by metis_tac[emitted_insts_emit_op] >>
  `?sp. src_elem = Var sp` by metis_tac[emitted_insts_emit_op] >>
  `?dp. dst_elem = Var dp` by metis_tac[emitted_insts_emit_op] >>
  `?inc. new_ctr = Var inc` by metis_tac[emitted_insts_emit_op] >>
  gnvs[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  strip_tac >>
  rename1 `compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se)` >>
  rename1 `emit_op MUL [Var counter;Lit (n2w (type_memory_bytes ce sty))] sb = (Var so,c1)` >>
  rename1 `emit_op MUL [Var counter;Lit (n2w (type_memory_bytes ce dty))] c1 = (Var doff,c2)` >>
  rename1 `emit_op ADD [Var src;Var so] c2 = (Var sp,c3)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `new_block exit st3 = (u3,sz)` >>
  `cs_extends si se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`,`Var dp`,`dty`,`Var sp`,`sty`,`si`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sa sb /\ cs_extends se sz` by
    (gvs[fresh_label_def,fresh_var_def,emit_op_def,emit_inst_def,
         emit_def,fresh_id_def,new_block_def,comp_bind_def,comp_ignore_bind_def,
         comp_return_def,cs_extends_def]) >>
  imp_res_tac typed_copy_emit_op_mono >>
  `cs_extends sb c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 si` by
    fs[ci_mono_def] >>
  `cs_extends c2 si /\ cs_extends c1 si /\ cs_extends sb si` by
    metis_tac[cs_extends_trans] >>
  `cs_extends si sz` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_mid,cs_extends_trans]
QED

(* Closed entry, condition, and recursive-child exit blocks. *)
Theorem typed_copy_sarray_slow_closed_blocks:
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce (Var dst) dty (Var src) sty N sa = ((),sz) /\
  fn_has_code sa sz fn ==>
  ?hdr body exit ctr lt done sp dp si se entry test back.
    hdr = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    body = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    exit = fresh_label_output "typed_sa_exit" (sa.cs_next_label+2) /\
    ctr = "%" ++ toString sa.cs_next_var /\
    lt = "%" ++ toString (sa.cs_next_var+1) /\
    done = "%" ++ toString (sa.cs_next_var+2) /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
    fn_has_code si se fn /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry /\
    entry.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
       mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
    lookup_block hdr fn.fn_blocks = SOME test /\
    test.bb_instructions =
      [mk_inst (sa.cs_next_id+2) LT [Var ctr;Lit(n2w N)] [lt];
       mk_inst (sa.cs_next_id+3) ISZERO [Var lt] [done];
       mk_inst (sa.cs_next_id+4) JNZ [Var done;Label exit;Label body] []] /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = se.cs_current_insts ++
      [mk_inst se.cs_next_id ADD [Var ctr;Lit 1w] ["%" ++ toString se.cs_next_var];
       mk_inst (se.cs_next_id+1) ASSIGN [Var("%" ++ toString se.cs_next_var)] [ctr];
       mk_inst (se.cs_next_id+2) JMP [Label hdr] []] /\
    get_instruction entry (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
    get_instruction entry (LENGTH sa.cs_current_insts+1) =
      SOME (mk_inst (sa.cs_next_id+1) JMP [Label hdr] []) /\
    get_instruction test 0 =
      SOME (mk_inst (sa.cs_next_id+2) LT [Var ctr;Lit(n2w N)] [lt]) /\
    get_instruction test 1 =
      SOME (mk_inst (sa.cs_next_id+3) ISZERO [Var lt] [done]) /\
    get_instruction test 2 =
      SOME (mk_inst (sa.cs_next_id+4) JNZ [Var done;Label exit;Label body] []) /\
    get_instruction back (LENGTH se.cs_current_insts) =
      SOME (mk_inst se.cs_next_id ADD [Var ctr;Lit 1w] ["%" ++ toString se.cs_next_var]) /\
    get_instruction back (LENGTH se.cs_current_insts+1) =
      SOME (mk_inst (se.cs_next_id+1) ASSIGN [Var("%" ++ toString se.cs_next_var)] [ctr]) /\
    get_instruction back (LENGTH se.cs_current_insts+2) =
      SOME (mk_inst (se.cs_next_id+2) JMP [Label hdr] [])
Proof
  strip_tac >> drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  rename1 `compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se)` >>
  `?entry test back.
     si.cs_blocks = test::entry::sa.cs_blocks /\
     entry.bb_label = sa.cs_current_bb /\
     isPREFIX sa.cs_current_insts entry.bb_instructions /\
     sz.cs_blocks = back::se.cs_blocks /\
     back.bb_label = se.cs_current_bb /\
     isPREFIX se.cs_current_insts back.bb_instructions /\
     entry = EL 1 si.cs_blocks /\ test = HD si.cs_blocks /\ back = HD sz.cs_blocks` by
    (qexistsl_tac [`EL 1 si.cs_blocks`,`HD si.cs_blocks`,`HD sz.cs_blocks`] >>
     map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
       [`si = _`,`sb = _`,`sc = _`,`sz = _`,`tail = _`] >>
     simp[NoAsms]) >>
  drule_all typed_copy_loop_slice_locations >> strip_tac >>
  qpat_x_assum `si.cs_blocks = _` kall_tac >>
  qpat_x_assum `sz.cs_blocks = _` kall_tac >>
  qexistsl_tac [`cond`,`body'`,`exit`,`ctr`,`lt`,`done`,`sp`,`dp`,
                 `si`,`se`,`entry`,`test`,`back`] >>
  gvs[APPEND_ASSOC, venomInstTheory.get_instruction_def, EL_APPEND_EQN]
QED

(* Fresh generated child pointers and old loop roots at the recursive entry. *)
Theorem typed_copy_sarray_slow_child_freshness:
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce (Var dst) dty (Var src) sty N sa = ((),sz) /\
  not_fresh_at sa src /\ not_fresh_at sa dst ==>
  ?si se.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+6))) dty
      (Var ("%" ++ toString (sa.cs_next_var+5))) sty si = ((),se) /\
    si.cs_next_var = sa.cs_next_var+7 /\
    not_fresh_at si src /\ not_fresh_at si dst /\
    not_fresh_at si ("%" ++ toString sa.cs_next_var) /\
    (!x. MEM x ["%" ++ toString (sa.cs_next_var+3);
                "%" ++ toString (sa.cs_next_var+4);
                "%" ++ toString (sa.cs_next_var+5);
                "%" ++ toString (sa.cs_next_var+6)] ==> not_fresh_at si x) /\
    ALL_DISTINCT ["%" ++ toString (sa.cs_next_var+3);
                  "%" ++ toString (sa.cs_next_var+4);
                  "%" ++ toString (sa.cs_next_var+5);
                  "%" ++ toString (sa.cs_next_var+6)] /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var ==>
       ~MEM x ["%" ++ toString (sa.cs_next_var+3);
               "%" ++ toString (sa.cs_next_var+4);
               "%" ++ toString (sa.cs_next_var+5);
               "%" ++ toString (sa.cs_next_var+6)])
Proof
  strip_tac >> drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `si.cs_next_var = sa.cs_next_var+7` by simp[] >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`si = _`,`sb = _`,`sc = _`,`sz = _`,`tail = _`] >>
  drule typed_sarray_pointer_fresh >>
  disch_then (qspecl_then [`Var src`,`Var dst`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >> gvs[])) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`si`,`se`] >> simp[] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED
