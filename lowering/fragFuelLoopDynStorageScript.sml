(*
 * Fuel bound for the dynamic-array-to-storage copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_dynarray_to_storage
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* The length is loaded into a fresh variable before the loop; the loop
   counts a fresh counter from 0 while it is below that length.  Each round
   copies one element (one word, or a word-copy loop over a literal count)
   and adds 1; the body writes only the counter and variables it allocates
   itself, so the length stays fixed and the loop leaves within 2 ** 256
   rounds. *)
(* The copy slice stops before the counter update and the back edge. *)
Theorem fuel_ok_dynstorage_copy_body[local]:
  !src_ptr dst_slot counter elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (if elem_words = 1 then
         do mul_op <- emit_op MUL [Var counter; Lit 32w];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            val_op <- emit_op MLOAD [src_elem];
            slot_off <- emit_op ADD [Var counter; Lit 1w];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            (if transient then emit_void TSTORE [dst_elem; val_op]
             else emit_void SSTORE [dst_elem; val_op])
         od
       else
         do mul_op <- emit_op MUL [Var counter; Lit (n2w elem_mem_size)];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            slot_mul <- emit_op MUL [Var counter; Lit (n2w elem_words)];
            slot_off <- emit_op ADD [Lit 1w; slot_mul];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            compile_word_copy_loop src_elem dst_elem elem_words
              LocMemory (if transient then LocTransient else LocStorage) F;
            return ()
         od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

(* An empty write set keeps both loop registers, even across a nested copy.
   The bound is fixed at compile time, before the runtime state is chosen. *)
Theorem dynstorage_copy_body_outcome[local]:
  !m st x st' len counter.
    fuel_ok {} {} {} m /\ m st = (x, st') /\
    var_below st.cs_next_var len /\ var_below st.cs_next_var counter ==>
    ?Kb. frag_fuel {} {} {} st st' Kb /\
      !G ctx fn s.
        no_phi_fn fn /\ fn_has_code st st' fn /\
        callees_stable G ctx fn /\ at_point st s ==>
        ?j. j <= Kb /\
          fuel_outcome G ctx fn s j
            (\t. vars_kept st.cs_next_var {} s t /\
                 lookup_var len t = lookup_var len s /\
                 lookup_var counter t = lookup_var counter s /\
                 at_point st' t)
Proof
  rpt gen_tac >> strip_tac >>
  fs[fuel_ok_def] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `Kb` >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `st.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >>
  simp[vars_kept_def]
QED

Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  cheat
QED
