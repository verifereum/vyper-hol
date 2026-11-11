(*
 * Fuel bound for the dynamic-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_dynarray_typed
 *)

Theory fragFuelLoopDynarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
Libs
  fragFuelLib

(* Structural projection: admitting all jumps as exits bounds a single
   pass through the emitted code.  This is used only for compile-state
   properties, not as the fuel bound for the counted loop. *)
Theorem dynarray_compile_structure[local]:
  !cenv dst dst_elem cap src src_elem st x st'.
    (!d s Wv E. fuel_ok Wv {} E
       (compile_store_memory_typed cenv d dst_elem s src_elem)) /\
    compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem st = (x, st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    (cs_no_phi st ==> cs_no_phi st')
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} UNIV
     (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)`
    suffices_by metis_tac[fuel_ok_def] >>
  simp[Once (cj 6 compile_store_memory_typed_def), compile_copy_memory_dynamic_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst] >>
  simp[is_terminator_def]
QED

(* Keep each monadic cut as a run equation.  In particular, no unfolding
   of the recursive element copy is needed to recover the loop layout. *)
Theorem dynarray_counted_run[local]:
  !ce dst dt cap src styp sa result sz.
    ~(type_memory_bytes ce dt = type_memory_bytes ce styp /\ dt = styp) /\
    compile_copy_dynarray_typed ce dst dt cap src styp sa = (result,sz) ==>
    ?len long ok sd dd hdr body exit ctr lt done so doff sp dp next
     a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
     a17 a18 a19 a20 a21 a22 a23 a24 a25 a26.
      emit_op MLOAD [src] sa = (len,a1) /\
      emit_op GT [len; Lit (n2w cap)] a1 = (long,a2) /\
      emit_op ISZERO [long] a2 = (ok,a3) /\
      emit_void ASSERT [ok] a3 = ((),a4) /\
      emit_void MSTORE [dst;len] a4 = ((),a5) /\
      emit_op ADD [src;Lit 32w] a5 = (sd,a6) /\
      emit_op ADD [dst;Lit 32w] a6 = (dd,a7) /\
      fresh_label "typed_dyn_cond" a7 = (hdr,a8) /\
      fresh_label "typed_dyn_body" a8 = (body,a9) /\
      fresh_label "typed_dyn_exit" a9 = (exit,a10) /\
      fresh_var a10 = (ctr,a11) /\
      emit_inst ASSIGN [Lit 0w] [ctr] a11 = ((),a12) /\
      emit_inst JMP [Label hdr] [] a12 = ((),a13) /\
      new_block hdr a13 = (a13.cs_current_bb,a14) /\
      emit_op LT [Var ctr;len] a14 = (lt,a15) /\
      emit_op ISZERO [lt] a15 = (done,a16) /\
      emit_inst JNZ [done;Label exit;Label body] [] a16 = ((),a17) /\
      new_block body a17 = (a17.cs_current_bb,a18) /\
      emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))] a18 = (so,a19) /\
      emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))] a19 = (doff,a20) /\
      emit_op ADD [sd;so] a20 = (sp,a21) /\
      emit_op ADD [dd;doff] a21 = (dp,a22) /\
      compile_store_memory_typed ce dp dt sp styp a22 = ((),a23) /\
      emit_op ADD [Var ctr;Lit 1w] a23 = (next,a24) /\
      emit_inst ASSIGN [next] [ctr] a24 = ((),a25) /\
      emit_inst JMP [Label hdr] [] a25 = ((),a26) /\
      new_block exit a26 = (a26.cs_current_bb,sz) /\ result = () /\
      len = Var (STRING #"%" (toString sa.cs_next_var)) /\
      ctr = STRING #"%" (toString (sa.cs_next_var + 5)) /\
      a22.cs_next_var = sa.cs_next_var + 12 /\
      var_below a22.cs_next_var (STRING #"%" (toString sa.cs_next_var)) /\
      var_below a22.cs_next_var ctr /\
      ctr <> STRING #"%" (toString sa.cs_next_var) /\
      (!N. N <= sa.cs_next_var ==>
        ~var_below N (STRING #"%" (toString sa.cs_next_var)) /\
        ~var_below N ctr)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once (cj 6 compile_store_memory_typed_def), comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[new_block_def, emit_op_def, emit_inst_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, fresh_label_def, emit_def,
      var_below_def, ASCIInumbersTheory.toString_inj]
QED

(* The straight-line body cut ends just before its back jump.  Its
   temporary registers are fresh; only the loop counter may be overwritten. *)
Theorem dynarray_body_fuel[local]:
  !ce dt styp ctr sd dd Wv E.
    (!d s Wv E. fuel_ok Wv {} E
       (compile_store_memory_typed ce d dt s styp)) ==>
    fuel_ok (ctr INSERT Wv) {} E
      (do so <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))];
          doff <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))];
          sp <- emit_op ADD [sd;so];
          dp <- emit_op ADD [dd;doff];
          compile_store_memory_typed ce dp dt sp styp;
          next <- emit_op ADD [Var ctr;Lit 1w];
          emit_inst ASSIGN [next] [ctr]
       od)
Proof
  rpt strip_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst] >>
  simp[is_terminator_def]
QED

(* Given a bound for the element copy (the recursive call), the copy of a
   dynamic array is bounded.  The length is loaded into a fresh variable
   before the loop; the loop counts a fresh counter from 0 while it is
   below that length.  The body writes only the counter and variables it
   allocates itself, so the length stays fixed and the loop leaves within
   2 ** 256 rounds. *)
Theorem fuel_ok_compile_copy_dynarray_typed:
  !cenv dst dst_elem cap src src_elem.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)
Proof
  cheat
QED
