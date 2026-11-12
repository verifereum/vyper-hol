(* Compiler-only boundaries for the counted dynamic-array slow copy. *)
Theory typedCopyReturnDynArrayLayoutPtr
Ancestors placeMemoryArrayForward placeMemoryCodeLayout typedNormalizeDynarrayLoop
  typedCopyLoopLayoutPtr typedMemoryCopy emitHelperProps freshWrites
  fragExec exprLoweringProps compileEnv emitHelper context words list

Theorem typed_copy_dynarray_slow_emit_slices:
  ~(type_memory_bytes ce de = type_memory_bytes ce se /\ de = se) /\
  compile_copy_dynarray_typed ce (Var dst) de N (Var src) se sa = ((),sz) /\
  fn_has_code sa sz fn ==>
  ?a1 a2 a3 a4 a5 a6 sm len sd dd flag ok
   hdr body exit ctr lt done so doff sp dp inc
   l1 l2 l3 init st0 st1 sth h1 stj st2 stb c1 c2 c3 si sj c6 ste st3 u1 u2 u3.
    emit_op MLOAD [Var src] sa = (Var len,a1) /\
    emit_op GT [Var len;Lit (n2w N)] a1 = (flag,a2) /\
    emit_op ISZERO [flag] a2 = (ok,a3) /\
    emit_void ASSERT [ok] a3 = ((),a4) /\
    emit_void MSTORE [Var dst;Var len] a4 = ((),a5) /\
    emit_op ADD [Var src;Lit 32w] a5 = (Var sd,a6) /\
    emit_op ADD [Var dst;Lit 32w] a6 = (Var dd,sm) /\
    fresh_label "typed_dyn_cond" sm = (hdr,l1) /\
    fresh_label "typed_dyn_body" l1 = (body,l2) /\
    fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
    fresh_var l3 = (ctr,init) /\
    emit_inst ASSIGN [Lit 0w] [ctr] init = ((),st0) /\
    emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
    new_block hdr st1 = (u1,sth) /\
    emit_op LT [Var ctr;Var len] sth = (Var lt,h1) /\
    emit_op ISZERO [Var lt] h1 = (Var done,stj) /\
    emit_inst JNZ [Var done;Label exit;Label body] [] stj = ((),st2) /\
    new_block body st2 = (u2,stb) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce se))] stb = (Var so,c1) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce de))] c1 = (Var doff,c2) /\
    emit_op ADD [Var sd;Var so] c2 = (Var sp,c3) /\
    emit_op ADD [Var dd;Var doff] c3 = (Var dp,si) /\
    compile_store_memory_typed ce (Var dp) de (Var sp) se si = ((),sj) /\
    emit_op ADD [Var ctr;Lit 1w] sj = (Var inc,c6) /\
    emit_inst ASSIGN [Var inc] [ctr] c6 = ((),ste) /\
    emit_inst JMP [Label hdr] [] ste = ((),st3) /\
    new_block exit st3 = (u3,sz) /\
    not_fresh_at sm len /\ not_fresh_at sm sd /\ not_fresh_at sm dd /\
    fn_has_code sa a1 fn /\ fn_has_code a1 a4 fn /\
    fn_has_code a4 a5 fn /\ fn_has_code a5 a6 fn /\ fn_has_code a6 sm fn /\
    fn_has_code sm sz fn /\ fn_has_code stb c1 fn /\ fn_has_code c1 c2 fn /\
    fn_has_code c2 c3 fn /\ fn_has_code c3 si fn /\ fn_has_code si sj fn
Proof
  strip_tac >> drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  qpat_x_assum `(do _ <- _; _ od) sa = _` mp_tac >>
  simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  `?len. length = Var len` by metis_tac[emitted_insts_emit_op] >>
  `?sd. src_data = Var sd` by metis_tac[emitted_insts_emit_op] >>
  `?dd. dst_data = Var dd` by metis_tac[emitted_insts_emit_op] >>
  `?ltv. lt = Var ltv` by metis_tac[emitted_insts_emit_op] >>
  `?donev. done = Var donev` by metis_tac[emitted_insts_emit_op] >>
  `?sov. so = Var sov` by metis_tac[emitted_insts_emit_op] >>
  `?dov. doff = Var dov` by metis_tac[emitted_insts_emit_op] >>
  `?spv. sp = Var spv` by metis_tac[emitted_insts_emit_op] >>
  `?dpv. dp = Var dpv` by metis_tac[emitted_insts_emit_op] >>
  `?incv. inc = Var incv` by metis_tac[emitted_insts_emit_op] >>
  gnvs[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  rename1 `fresh_label "typed_dyn_cond" sm = _` >>
  `fn_has_code sm sz fn` by
    (qpat_x_assum `fn_has_code sa sz fn` mp_tac >>
     gvs[fn_has_code_def,emitted_blocks_def,same_blocks_def]) >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  imp_res_tac typed_copy_emit_op_mono >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  rename1 `emit_void MSTORE [Var dst;Var len] a4 = ((),a5)` >>
  rename1 `emit_void ASSERT [ok] a3 = ((),a4)` >>
  `ci_mono a4 a5` by
    (mp_tac (Q.SPECL [`MSTORE`,`[Var dst;Var len]`,`a4`] ci_mono_emit_void) >> simp[]) >>
  `ci_mono sm l1 /\ ci_mono l1 l2 /\ ci_mono l2 l3 /\ ci_mono l3 init` by
    metis_tac[ci_mono_fresh_label,ci_mono_fresh_var,pairTheory.SND] >>
  `ci_mono init st0 /\ ci_mono st0 st1 /\ ci_mono stj st2 /\
   ci_mono b6 ste /\ ci_mono ste st3` by metis_tac[ci_mono_emit_inst,pairTheory.SND] >>
  `ci_mono st1 sth /\ ci_mono st2 stb /\ ci_mono st3 sz` by
    metis_tac[ci_mono_new_block,pairTheory.SND] >>
  fs[ci_mono_def] >>
  `cs_extends sm st1` by metis_tac[cs_extends_trans] >>
  `cs_extends sth st2` by metis_tac[cs_extends_trans] >>
  `cs_extends sm stb /\ cs_extends b5 sz` by metis_tac[cs_extends_trans] >>
  `cs_extends b4 b5` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`,`Var dpv`,`de`,`Var spv`,`se`,`b4`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sm sz` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm fn` by metis_tac[fn_has_code_split] >>
  rpt conj_tac >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

(* Child-entry preservation eligibility, including length and shifted roots. *)
Theorem typed_copy_dynarray_slow_child_freshness:
  ~(type_memory_bytes ce de = type_memory_bytes ce se /\ de = se) /\
  compile_copy_dynarray_typed ce (Var dst) de N (Var src) se sa = ((),sz) /\
  fn_has_code sa sz fn ==>
  ?si sj.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) de
      (Var ("%" ++ toString (sa.cs_next_var+10))) se si = ((),sj) /\
    (!x. not_fresh_at sa x ==> not_fresh_at si x) /\
    (!k. k < 12 ==> not_fresh_at si ("%" ++ toString (sa.cs_next_var+k))) /\
    ALL_DISTINCT ["%" ++ toString (sa.cs_next_var+8);
                  "%" ++ toString (sa.cs_next_var+9);
                  "%" ++ toString (sa.cs_next_var+10);
                  "%" ++ toString (sa.cs_next_var+11)] /\
    (!x k. not_fresh_at sa x /\ k < 12 ==>
       x <> "%" ++ toString (sa.cs_next_var+k))
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  qexistsl_tac [`sc`,`ec`] >> simp[] >>
  rpt strip_tac >> gvs[not_fresh_at_def,ASCIInumbersTheory.toString_inj] >>
  decide_tac
QED
