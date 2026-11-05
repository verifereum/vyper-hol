(*
 * The stores of a tuple's elements into locals, word or memory-backed,
 * against the source's writes; a store into x_i keeps the tuple's unread
 * elements.
 *
 * TOP-LEVEL:
 *   tuple_store_mixed_locals_run — the stores against the writes
 *)
Theory tupleLocalStoreRun
Ancestors
  tupleLocalStoreProps stmtSimAssignStore stmtSimAssignMem tupleMemoryFrame
  tupleMemoryLayout  exprLoweringProps localPtrsProps compileEnv
  valueEncoding valueEncodingProps valueEncodingProofs vyperState vyperLookup
  list rich_list finite_map arithmetic venomState venomInst
  stmtSimDeclMem stmtLowering emitHelperProps emitHelper fragExec vyperInterpreter
  vyperTyping valueTypingMemoryProps freshWrites

(* Expose a destination's region and capacity without unfolding the state
   relation in every suffix-frame consumer. *)
Theorem tuple_store_destination_region:
  !func cenv cx es s id p dsz entry dw ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw ==>
    local_region cenv es.scopes s id (w2n dw) dsz /\
    type_memory_size entry.type <= dsz
Proof
  cheat
QED

(* This applies to either a 32-byte MSTORE or a runtime-sized memory
   copy. Only the unread suffix, not the already-consumed head, survives. *)
Theorem tuple_local_write_suffix:
  !func cenv cx es s id p dsz entry dw b sz addr elem vs tvs written mem' ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + elem + type_memory_size_list tvs <= b + sz /\
    written <= elem /\ written <= type_memory_size entry.type /\
    (!a len. a + len <= w2n dw \/ w2n dw + written <= a ==>
       mem_bytes_at a len mem' = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory vs tvs (addr + elem) s.vs_memory /\
    tuple_val_wf vs tvs ==>
    tuple_in_memory vs tvs (addr + elem) mem'
Proof
  cheat
QED

(* One execution interface for both representations; memory mode preserves
   old variables, while the word-only specialization preserves every variable. *)
Theorem tuple_local_store_head_run:
  !m ctx func cenv cx es s id p dsz pre env entry rest v tv ty vt op st st' w.
    (if is_word_type ty then emit_void MSTORE [Var p; op]
     else compile_store_memory cenv op (Var p) vt ty) st = ((), st') /\
    (~m ==> is_word_type ty) /\
    eval_operand op s = SOME w /\
    (if is_word_type ty then
       w = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v
     else
       ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
       value_has_type entry.type v /\ val_wf entry.type v /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
       (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
       type_memory_bytes cenv vt = type_memory_size entry.type /\
       type_memory_size entry.type + 64 < dimword (:256)) /\
    (m ==> (!x. op = Var x ==> not_fresh_at st x) /\ local_ptrs_reserved cenv st) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
      (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
                FLOOKUP t.vs_allocas aid = SOME bs) /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32
                   else MIN (type_memory_size tv) (type_memory_size entry.type)) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* The typing condition for later targets depends only on scope-entry types. *)
Theorem tuple_store_layout_write_local:
  !cx cenv ids tys tvs vs sc pre env entry rest id v.
    find_containing_scope id sc = SOME (pre, env, entry, rest) /\
    (!i e. i < LENGTH ids /\ lookup_scopes (EL i ids) sc = SOME e ==>
       if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) e.type (EL i vs)
       else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                 evaluate_type (get_tenv cx) vt = SOME e.type /\
                 value_has_type e.type (EL i vs)) ==>
    !i e. i < LENGTH ids /\
      lookup_scopes (EL i ids)
        (pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) = SOME e ==>
      if is_word_type (EL i tys) then
        store_lays_out (EL i tvs) e.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                evaluate_type (get_tenv cx) vt = SOME e.type /\
                value_has_type e.type (EL i vs)
Proof
  cheat
QED

Theorem tuple_store_operands_tail:
  !m st s t id ids ty tys tv tvs v vs op ops addr.
    LENGTH ops = LENGTH ids /\
    EVERY (\op. ?x. op = Var x) (op::ops) /\
    (m ==> EVERY (\op. !x. op = Var x ==> not_fresh_at st x) (op::ops)) /\
    (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
    (!i. i < LENGTH (id::ids) ==>
       ?w. eval_operand (EL i (op::ops)) s = SOME w /\
         (if is_word_type (EL i (ty::tys)) then
            w = typed_val_to_w256 (EL i (tv::tvs)) (EL i (v::vs))
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i (tv::tvs))))) ==>
    !i. i < LENGTH ids ==>
      ?w. eval_operand (EL i ops) t = SOME w /\
        (if is_word_type (EL i tys) then
           w = typed_val_to_w256 (EL i tvs) (EL i vs)
         else w2n w = addr + type_memory_size tv +
                       SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  cheat
QED

Theorem tuple_store_memory_tail:
  !func cenv cx es s t st scopes' id p dsz entry dw b sz addr tv tvs v vs written ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw /\
    local_ptrs_reserved cenv st /\
    MAP FDOM es.scopes = MAP FDOM scopes' /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + type_memory_size_list (tv::tvs) <= b + sz /\
    written <= type_memory_size tv /\ written <= type_memory_size entry.type /\
    (!a len. a + len <= w2n dw \/ w2n dw + written <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory (v::vs) (tv::tvs) addr s.vs_memory /\
    tuple_val_wf (v::vs) (tv::tvs) ==>
    b <= addr + type_memory_size tv /\
    addr + type_memory_size tv + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes' t name b sz)) /\
    tuple_in_memory vs tvs (addr + type_memory_size tv) t.vs_memory /\
    tuple_val_wf vs tvs
Proof
  cheat
QED

Theorem tuple_store_head_code_shape:
  !cenv ty vt p op st sm.
    (is_word_type vt = is_word_type ty) /\
    (~is_word_type ty ==> (vt = ty \/ is_bytestring_type vt) /\
                            0 < type_memory_bytes cenv vt) /\
    (if is_word_type ty then emit_void MSTORE [Var p; op]
     else compile_store_memory cenv op (Var p) vt ty) st = ((),sm) ==>
    cs_extends st sm /\ ~block_is_terminated sm
Proof
  cheat
QED

(* The single recursion used by both the all-word and memory-backed APIs. *)
Theorem tuple_store_mixed_locals_run:
  !ids m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops st = ((),st') /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es = (INL (),es') /\
    LENGTH ids = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    (m ==> EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops) /\
    (!i. i < LENGTH ids ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH ids ==>
       ?p dsz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) dsz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type (EL i tys) ==>
           (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
           type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
           ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
                 type_memory_bytes cenv vt = type_memory_size vtv /\
                 0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256))) /\
    (!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) es.scopes = SOME entry ==>
       if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
       else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                 evaluate_type (get_tenv cx) vt = SOME entry.type /\
                 value_has_type entry.type (EL i vs)) /\
    (m ==> local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
       (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (ids <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED








