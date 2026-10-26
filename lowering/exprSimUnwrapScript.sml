(*
 * unwrap_value's step of the expression simulation (#636)
 *
 * lower_value is compile_expr followed by unwrap_value, which turns the
 * value_vv compile_expr hands out into an operand: none for a StackValue
 * or an aggregate in memory, a load for a word behind a pointer, a copy
 * into a buffer for an aggregate elsewhere.  expr_sim_of_vv_sim sequences
 * compile_expr's fragment, which ends in vv_post (expr_vv_sim), with
 * unwrap_value's, which takes vv_post to expr_post (unwrap_value_sim).
 *
 * TOP-LEVEL:
 *   expr_sim_of_vv_sim — expr_vv_sim gives expr_sim
 *   unwrap_value_sim   — unwrap_value's code takes vv_post to expr_post,
 *                        one lemma per form of value_vv:
 *                        expr_post_of_vv_post_stack,
 *                        unwrap_memory_sim (expr_post_of_vv_post_memory,
 *                        and unwrap_memory_word_sim's MLOAD),
 *                        unwrap_runtime_immutable_word_sim (DLOAD),
 *                        vv_post_calldata (no calldata pointers)
 *
 * Helpers: compile_ensure_in_memory_extends, unwrap_value_extends,
 *   expr_post_of_vv_post_load, step_DLOAD, immutable_holds_dload
 *
 * Cheated, each with its reason at the lemma:
 *   compile_expr_extends — compile_expr appends to the compile state and
 *                        hands out names from its start counters on
 *   unwrap_storage_word_sim — a word load from storage (false as stated)
 *   unwrap_ctor_immutable_word_sim — a word immutable in the constructor
 *                        (the lowering differs from Python)
 *   unwrap_copy_sim    — the copy of an aggregate out of storage or code
 *)

Theory exprSimUnwrap
Ancestors
  list finite_map
  exprSim exprLowering compileEnv vyperAST vyperInterpreter vyperState
  loweringSlice fragExec freshWrites venomInst venomExecSemantics venomState
Libs
  pairLib

(* ===== The compile side ===== *)

(* compile_expr only appends to the compile state, and hands out variables
   and instruction ids from its start counters on.  Cheated: it needs an
   induction over compile_expr's cases of its own, as exprLoweringProps'
   ci_mono_lower_value_compile_expr has for the weaker ci_mono. *)
Theorem compile_expr_extends:
  !cenv ty e sa vv sm.
    compile_expr cenv ty e sa = (vv, sm) ==>
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id
Proof
  cheat
QED

Theorem compile_ensure_in_memory_appends[local]:
  !pop loc mem_bytes word_count is_ctor.
    cs_appends (compile_ensure_in_memory pop loc mem_bytes word_count is_ctor)
Proof
  rw[contextTheory.compile_ensure_in_memory_def,
     contextTheory.compile_alloc_buffer_def,
     contextTheory.compile_storage_to_memory_def,
     contextTheory.compile_transient_to_memory_def,
     contextTheory.compile_code_to_memory_def,
     contextTheory.compile_word_copy_loop_def,
     contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def,
     word_scale_def] >>
  Cases_on `loc` >> rw[] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind,
              IF_CASES_TAC] >>
       rw[cs_appends_prims, cs_appends_return, cs_appends_emit_helpers]) >>
  rw[cs_appends_prims, cs_appends_return, cs_appends_emit_helpers]
QED

(* compile_ensure_in_memory's copy only appends to the compile state. *)
Theorem compile_ensure_in_memory_extends:
  !pop loc mem_bytes word_count is_ctor sm op sb.
    compile_ensure_in_memory pop loc mem_bytes word_count is_ctor sm =
      (op, sb) ==>
    cs_extends sm sb
Proof
  rpt strip_tac >>
  `cs_appends (compile_ensure_in_memory pop loc mem_bytes word_count
                 is_ctor)` by simp[compile_ensure_in_memory_appends] >>
  fs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

Theorem emit_op_cs_extends[local]:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  rpt strip_tac >>
  `cs_appends (emit_op opc args)` by simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

Theorem unwrap_value_extends:
  !cenv vv sm op sb. unwrap_value cenv vv sm = (op, sb) ==> cs_extends sm sb
Proof
  Cases_on `vv` >>
  rw[unwrap_value_def, comp_return_def, cs_extends_refl]
  >- (rename1 `compile_ptr_load _ loc` >> Cases_on `loc` >>
      gvs[contextTheory.compile_ptr_load_def, AllCaseEqs()] >>
      metis_tac[emit_op_cs_extends]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[comp_return_def, cs_extends_refl] >>
  metis_tac[compile_ensure_in_memory_extends]
QED

(* ===== unwrap_value's code ===== *)

(* unwrap_value's code, run where compile_expr's code ends, takes vv_post to
   expr_post.  One lemma per form of value_vv. *)

(* A StackValue: no code. *)
Theorem expr_post_of_vv_post_stack:
  !func cenv cx e es sa sb s0 es' v t op s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (StackValue t op) s ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def]
QED

(* An aggregate in memory: the pointer is the operand, no code. *)
Theorem expr_post_of_vv_post_memory:
  !func cenv cx e es sa sb s0 es' v t p s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (LocatedValue t p) s /\
    p.ptr_location = LocMemory /\ ~is_word_type t ==>
    expr_post func cenv cx e es sa sb s0 es' v p.ptr_operand s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def] >>
  gvs[materialise_def, return_def, expr_val_rel_def, expr_val_at_def] >>
  metis_tac[]
QED

(* The end of a one-instruction load of a word: the loaded word in a fresh
   variable, nothing else changed. *)
Theorem expr_post_of_vv_post_load:
  !func cenv cx e es sa sm sb s0 es' v t p op s1 s w.
    vv_post func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 /\
    is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel func cenv cx es' s /\ eval_operand op s = SOME w /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           w = typed_val_to_w256 tvt v) /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s1 = SOME w' ==>
            lookup_var x s = SOME w') /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_def]
  >~ [`expr_val_rel`] >- gvs[expr_val_rel_def]
  >~ [`expr_val_at`] >- simp[expr_val_at_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- fs[vv_post_def] >>
  fs[vv_post_def] >> metis_tac[]
QED

(* A word in memory: an MLOAD. *)
Theorem unwrap_memory_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op MLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s1.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, materialise_def, return_def] >>
     metis_tac[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
                           `mload (w2n w) s1`, `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule emitHelperPropsTheory.step_MLOAD >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`, `mload (w2n w) s1`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >>
      fs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  simp[]) >>
  gvs[vv_post_def]
QED

Theorem step_DLOAD:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id DLOAD [op1] [out]) ss =
      OK (update_var out
            (word_of_bytes T (0w:bytes32)
               (TAKE 32 (DROP (w2n v1) ss.vs_data_section ++
                         REPLICATE 32 0w))) ss)
Proof
  rw[venomExecSemanticsTheory.step_inst_base_def,
     venomExecSemanticsTheory.exec_read1_def]
QED

(* At runtime an immutable's word is in the data section at its offset, as
   immutables_rel says. *)
Theorem immutable_holds_dload:
  !func cenv cx es s t v w.
    stmt_state_rel func cenv cx es s /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t (Value v) w es ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
          typed_val_to_w256 tvt v
Proof
  rw[immutable_holds_def, exprLoweringPropsTheory.stmt_state_rel_def,
     state_rel_def, immutables_rel_def] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  simp[rich_listTheory.TAKE_APPEND1]
QED

(* A word immutable at runtime: a DLOAD. *)
Theorem unwrap_runtime_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' /\
       stmt_state_rel func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
    `word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s1.vs_data_section ++ REPLICATE 32 0w))`,
    `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule step_DLOAD >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`,
               `word_of_bytes T (0w:bytes32)
                  (TAKE 32 (DROP (w2n w) s1.vs_data_section ++
                            REPLICATE 32 0w))`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  simp[]) >>
  gvs[]
QED

(* A pointer into memory: an MLOAD for a word, the pointer itself for an
   aggregate. *)
Theorem unwrap_memory_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `is_word_type t`
  >- (irule unwrap_memory_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
  rw[] >> metis_tac[expr_post_of_vv_post_memory]
QED

(* A word in storage or transient storage: an SLOAD or TLOAD.  Cheated:
   storage_holds relates the slot through decode_base_from_slot, which
   truncates, so a slot holding a word outside the type's range (0x1FF for a
   uint8) decodes to a value of the type while the load returns the raw
   word.  storage_rel as it stands does not rule such a slot out, so this
   is false as stated, and so is expr_sim_of_vv_sim for such a read; the
   fix is a storage invariant that keeps each slot in its type's range. *)
Theorem unwrap_storage_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* A word immutable in the constructor: an ILOAD.  Cheated, and not
   provable: the lowering differs from Python here.  compile_ptr_load emits
   ILOAD at the immutable's offset, and ILOAD reads memory there, while
   Python's load_word adds the immutables' buffer first
   (iload(add(offset, immutables_alloca))); and immutables_rel relates the
   constructor's immutables to vs_immutables, not to memory. *)
Theorem unwrap_ctor_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* An aggregate in storage, transient storage or code: a copy into a buffer
   of the expression's own, allocated at instruction id sm.cs_next_id.
   Cheated.  From storage and transient storage it is the copy loop's
   proof.  From code it is not provable as things stand.  At runtime,
   immutables_rel relates only an immutable's 32-byte word, where Python
   copies the value's whole memory layout (copy_to_memory of
   memory_bytes_required bytes); the fix is for immutables_rel to say the
   data section holds the value as val_in_memory lays it out at its offset.
   In the constructor the lowering differs from Python:
   compile_code_to_memory copies with DLOAD from the data section, where
   Python's load_word reads the immutables' buffer with ILOAD, so it needs
   a lowering fix as well. *)
Theorem unwrap_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* No value_vv points into calldata. *)
Theorem vv_post_calldata:
  !func cenv cx e es sa sm s0 es' tv t p s.
    p.ptr_location = LocCalldata ==>
    ~vv_post func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s
Proof
  rw[vv_post_def, vv_holds_def]
QED

Theorem unwrap_value_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
      gvs[fragExecTheory.frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (Cases_on `is_word_type t`
      >- (irule unwrap_storage_word_sim >> gvs[]) >>
      irule unwrap_copy_sim >> gvs[] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `is_word_type t` >~ [`~is_word_type t`]
      >- (irule unwrap_copy_sim >> gvs[]) >>
      Cases_on `cenv.ce_is_ctor`
      >- (irule unwrap_ctor_immutable_word_sim >> gvs[]) >>
      irule unwrap_runtime_immutable_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  `p.ptr_location = LocMemory` by (Cases_on `p.ptr_location` >> gvs[]) >>
  irule unwrap_memory_sim >> simp[]
QED

(* unwrap_value's step: expr_vv_sim gives expr_sim.  compile_expr's
   fragment ends in vv_post, and unwrap_value's code takes that to
   expr_post. *)
Theorem expr_sim_of_vv_sim:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es ==> expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `expr_vv_res_ok res` by simp[expr_vv_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `res`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> first_x_assum (irule_at Any) >> simp[] >>
  Cases_on `?v. res = INL (Value v)`
  >- (gvs[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`,
                   `s0`, `es'`, `v`, `vv`, `op`, `expr_exit (INL (Value v))`]
        mp_tac unwrap_value_sim >>
      impl_tac >- asm_rewrite_tac[] >>
      strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. F`, `\s. F`, `expr_exit res`] >>
  simp[fragExecTheory.frag_exec_false_pre] >>
  gvs[expr_res_ok_def]
QED

