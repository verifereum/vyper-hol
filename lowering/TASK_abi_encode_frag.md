# TASK: ABI encoder correctness over frag_exec

## Meta
Status: planned
Priority: P1
Created: 2026-10-25
Location: lowering/ (file lowering/abiEncoderPropsScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem compile_abi_encode_frag:
  (!dst child_ptr ei is_dyn static_ofst dyn_ptr st op st' ctx env ty tv v
    av s0 dst_w src_w lo top.
     compile_abi_encode_child dst child_ptr ei is_dyn static_ofst dyn_ptr st =
       (op, st') /\
     abi_enc_plan env ty ei /\
     is_dyn = is_dynamic (vyper_to_abi_type env ty) /\
     evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     vyper_to_abi env ty v = SOME av /\
     eval_operand dst s0 = SOME dst_w /\
     eval_operand child_ptr s0 = SOME src_w ==>
     if ~is_dyn then
       enc_pre st st' [dst; child_ptr] lo top tv v (w2n src_w)
         [(w2n dst_w + static_ofst,
           LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
       frag_exec ctx st st' (\s. s = s0)
         (\s. mem_bytes_at (w2n dst_w + static_ofst)
                (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
              enc (vyper_to_abi_type env ty) av /\
              eval_operand op s =
                SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
              enc_frame st st' lo top
                [(w2n dst_w + static_ofst,
                  LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
         (\r. F)
     else
       !c d j.
         eval_operand dyn_ptr s0 = SOME (n2w c) /\
         mem_word_at c s0.vs_memory = n2w d /\
         j NOTIN frag_ids st st' /\
         FLOOKUP s0.vs_allocas j = SOME (c, 32) /\ lo <= c /\
         static_ofst + 32 <= d /\
         enc_pre st st' [dst; child_ptr; dyn_ptr] lo top tv v (w2n src_w)
           [(w2n dst_w + static_ofst, 32);
            (w2n dst_w + d,
             LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
         frag_exec ctx st st' (\s. s = s0)
           (\s. mem_bytes_at (w2n dst_w + d)
                  (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
                enc (vyper_to_abi_type env ty) av /\
                mem_word_at (w2n dst_w + static_ofst) s.vs_memory = n2w d /\
                mem_word_at c s.vs_memory =
                  n2w (d + LENGTH (enc (vyper_to_abi_type env ty) av)) /\
                eval_operand op s =
                  SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
                enc_frame st st' lo top
                  [(w2n dst_w + static_ofst, 32);
                   (w2n dst_w + d,
                    LENGTH (enc (vyper_to_abi_type env ty) av));
                   (c, 32)] s0 s)
           (\r. F)) /\
  (!dst src ei st op st' ctx env ty tv v av s0 dst_w src_w lo top.
     compile_abi_encode_to_buf dst src ei st = (op, st') /\
     abi_enc_plan env ty ei /\
     evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     vyper_to_abi env ty v = SOME av /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     enc_pre st st' [dst; src] lo top tv v (w2n src_w)
       [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w)
              (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
            enc (vyper_to_abi_type env ty) av /\
            eval_operand op s =
              SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
            enc_frame st st' lo top
              [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
       (\r. F)) /\
  (!dst src elems src_offset head_offset dyn_ptr st op st' ctx env ts tvs vs
    avs s0 dst_w src_w lo top c d.
     compile_abi_encode_complex_elems dst src elems src_offset head_offset
       dyn_ptr st = (op, st') /\
     abi_enc_plans env ts elems /\
     LIST_REL (\t tv. evaluate_type env t = SOME tv) ts tvs /\
     LIST_REL value_has_type tvs vs /\
     vyper_to_abi_list env ts vs = SOME avs /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     (EXISTS (\(_, _, _, is_dyn). is_dyn) elems ==>
        eval_operand dyn_ptr s0 = SOME (n2w c) /\
        mem_word_at c s0.vs_memory = n2w d /\
        (?j. j NOTIN frag_ids st st' /\
             FLOOKUP s0.vs_allocas j = SOME (c, 32)) /\ lo <= c /\
        head_offset + SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems) <= d) /\
     enc_pre st st' [dst; src; dyn_ptr] lo top (TupleTV tvs)
       (ArrayV (TupleV vs)) (w2n src_w + src_offset)
       [(w2n dst_w + head_offset, SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
        (w2n dst_w + d,
         LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
         SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems))] s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w + head_offset)
              (SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems)) s.vs_memory ++
            mem_bytes_at (w2n dst_w + d)
              (LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
               SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems)) s.vs_memory =
            enc_tuple d 0 (vyper_to_abi_types env ts) avs [] [] /\
            (EXISTS (\(_, _, _, is_dyn). is_dyn) elems ==>
             mem_word_at c s.vs_memory =
               n2w (d +
                 LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
                 SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems))) /\
            enc_frame st st' lo top
              [(w2n dst_w + head_offset,
                SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
               (w2n dst_w + d,
                LENGTH (enc_tuple d 0 (vyper_to_abi_types env ts) avs [] []) -
                SUM (MAP (\(_, abi_sz, _, _). abi_sz) elems));
               (c, 32)] s0 s)
       (\r. F)) /\
  (!dst src ei asz msz len_op st op st' ctx env t n tv vs av s0 dst_w src_w
    lo top.
     compile_abi_encode_dyn_loop dst src ei asz msz len_op st = (op, st') /\
     abi_enc_plan env (ArrayT t (Dynamic n))
       (AbiDynArray ei asz msz T) /\
     evaluate_type env (ArrayT t (Dynamic n)) = SOME tv /\
     value_has_type tv (ArrayV (DynArrayV vs)) /\
     vyper_to_abi env (ArrayT t (Dynamic n)) (ArrayV (DynArrayV vs)) =
       SOME av /\
     eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
     eval_operand len_op s0 = SOME (n2w (LENGTH vs)) /\
     enc_pre st st' [dst; src; len_op] lo top tv (ArrayV (DynArrayV vs))
       (w2n src_w)
       [(w2n dst_w,
         LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) - 32)]
       s0 ==>
     frag_exec ctx st st' (\s. s = s0)
       (\s. mem_bytes_at (w2n dst_w)
              (LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) -
               32) s.vs_memory =
            DROP 32 (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) /\
            eval_operand op s =
              SOME (n2w (LENGTH
                (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av))) /\
            enc_frame st st' lo top
              [(w2n dst_w,
                LENGTH (enc (vyper_to_abi_type env (ArrayT t (Dynamic n))) av) -
                32)] s0 s)
       (\r. F))
```

Supporting definitions (in lowering/abiEncoderPropsScript.sml, just above the theorem; frozen too):

```sml
(* ===== Encoding plans ===== *)

(* abi_enc_plan env ty ei: ei is a right plan for encoding a value of type
   ty, in type environment env.  It fixes what the encoder takes on trust
   from its abi_enc_info: an AbiCopy size is the value's memory size, an
   element's head size, memory size and dynamic flag are those of its
   type, and an aggregate's elements are its components, in order (for a
   struct, typed in env \\ nsid, as vyper_to_abi_type does).  AbiComplex
   is for dynamic aggregates only: a static one is an AbiCopy, which is what
   type_to_abi_enc_info builds and what the static-element loop of a
   dynamic array handles. *)
Inductive abi_enc_plan:
[~prim:]
  is_word_type ty ==> abi_enc_plan env ty AbiPrimWord
[~bytes:]
  abi_enc_plan env (BaseT (BytesT (Dynamic n))) (AbiBytestring n)
[~string:]
  abi_enc_plan env (BaseT (StringT n)) (AbiBytestring n)
[~copy:]
  ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv ==>
  abi_enc_plan env ty (AbiCopy (type_memory_size tv))
[~dynarray:]
  evaluate_type env t = SOME tv /\ abi_enc_plan env t ei ==>
  abi_enc_plan env (ArrayT t (Dynamic n))
    (AbiDynArray ei
       (if is_dynamic (vyper_to_abi_type env t) then 32
        else static_length (vyper_to_abi_type env t))
       (type_memory_size tv) (is_dynamic (vyper_to_abi_type env t)))
[~tuple:]
  is_dynamic (vyper_to_abi_type env (TupleT ts)) /\
  abi_enc_plans env ts elems ==>
  abi_enc_plan env (TupleT ts) (AbiComplex elems)
[~sarray:]
  is_dynamic (vyper_to_abi_type env t) /\
  abi_enc_plans env (REPLICATE n t) elems ==>
  abi_enc_plan env (ArrayT t (Fixed n)) (AbiComplex elems)
[~struct:]
  FLOOKUP env nsid = SOME (StructArgs args) /\
  is_dynamic (vyper_to_abi_type env (StructT nsid)) /\
  abi_enc_plans (env \\ nsid) (MAP SND args) elems ==>
  abi_enc_plan env (StructT nsid) (AbiComplex elems)
[~nil:]
  abi_enc_plans env [] []
[~cons:]
  evaluate_type env t = SOME tv /\ abi_enc_plan env t ei /\
  abi_enc_plans env ts elems ==>
  abi_enc_plans env (t::ts)
    ((ei,
      (if is_dynamic (vyper_to_abi_type env t) then 32
       else static_length (vyper_to_abi_type env t)),
      type_memory_size tv, is_dynamic (vyper_to_abi_type env t)) :: elems)
End

(* ===== Scratch cells and frames ===== *)

(* The instruction ids a compiled fragment emits. *)
Definition frag_ids_def:
  frag_ids (st : compile_state) (st' : compile_state) =
    {i | st.cs_next_id <= i /\ i < st'.cs_next_id}
End

(* The encoder's scratch cells (its ALLOCAs of 32 bytes) at ids in ids:
   each one already run lies at or above lo, and running the rest keeps
   the alloca frontier at or below top, which is below 2 ** 256, so no
   pointer wraps.  An encoder in a loop body runs again with its cells of
   the last iteration allocated, which ALLOCA then returns again. *)
Definition enc_scratch_def:
  enc_scratch ids lo top (s : venom_state) <=>
    alloca_inv s /\ lo <= s.vs_alloca_next /\ top < dimword (:256) /\
    (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b, sz) ==>
              lo <= b /\ sz = 32) /\
    s.vs_alloca_next +
      32 * CARD {i | i IN ids /\ FLOOKUP s.vs_allocas i = NONE} <= top
End

(* What running encoder code from st to st' changes from s0 to s: the
   memory only in the output regions outs and in the fragment's own
   scratch cells; the allocas only at the fragment's ids, keeping those
   already run; no variable bound before st; none of the effects. *)
Definition enc_frame_def:
  enc_frame st st' lo top outs (s0 : venom_state) (s : venom_state) <=>
    (!x w. not_fresh_at st x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!a. EVERY (\(b, n). a < b \/ b + n <= a) outs /\
         (!i b sz. i IN frag_ids st st' /\
                   FLOOKUP s.vs_allocas i = SOME (b, sz) ==>
                   a < b \/ b + sz <= a) ==>
         mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 s0.vs_memory) /\
    (!i. i NOTIN frag_ids st st' ==>
         FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\
    (!i r. FLOOKUP s0.vs_allocas i = SOME r ==>
           FLOOKUP s.vs_allocas i = SOME r) /\
    enc_scratch (frag_ids st st') lo top s /\
    s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
    s.vs_logs = s0.vs_logs /\ s.vs_requests = s0.vs_requests
End

(* The encoder's inputs at s0: its operands are bound before st, the
   source value of type tv is in memory at src below lo, each output
   region lies below lo and misses the source, and the scratch cells are
   as enc_scratch says. *)
Definition enc_pre_def:
  enc_pre st st' ops lo top tv v src outs (s0 : venom_state) <=>
    (!y. MEM (Var y) ops ==> not_fresh_at st y) /\
    val_in_memory tv v src s0.vs_memory /\
    src + type_memory_size tv <= lo /\
    EVERY (\(b, n). b + n <= lo /\
                    regions_disjoint (src, type_memory_size tv) (b, n)) outs /\
    enc_scratch (frag_ids st st') lo top s0
End
```

**Do not modify this statement or these definitions.** Prove it as-is, or produce a counterexample.

`frag_exec_loop` (end of lowering/fragExecScript.sml) is a frozen lemma: use it as stated; another prover run is proving it (it may still be `cheat` in your copy; that is fine).

## Completion Criteria

1. `holbuild -j4 build abiEncoderPropsTheory` passes with no failures and no CHEAT in `compile_abi_encode_frag` or the helpers you add (the pre-existing cheats `compile_abi_decode_static_correct` and `compile_abi_encode_to_buf_correct` in the same file are out of scope; leave them).
2. No duplicate lemmas; helpers in their most general form, in lowering/abiEncoderPropsScript.sml or, if large, a new script in lowering/ (register it the way the others are; check holproject.toml).
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).

**If the theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build abiEncoderPropsTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

The Vyper→Venom lowering ABI-encodes the value of an external function's `return` into a buffer and RETURNs it (lowering/defs/stmtLoweringScript.sml `compile_external_return_def`). The encoder (`compile_abi_encode_child` / `_to_buf` / `_complex_elems` / `_dyn_loop` and the helper `compile_abi_encode_dyn_static_loop`, lowering/defs/abiEncoderScript.sml) mirrors Python's vyper/codegen_venom/abi/abi_encoder.py. Dynamic arrays are encoded with loops over several basic blocks, so the correctness statement is over `frag_exec` (lowering/fragExecScript.sml), the fragment judgment for code emitted between two compile states. This theorem is the encoder half of the S1 halt bridge for dynamic external returns (vyper-hol issue #640). The old single-block statement `compile_abi_encode_to_buf_correct` in the same file is false as stated and is being replaced by this one.

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, rename1 rather than generated names.
- Don't edit files under semantics/ or venom/ or lowering/defs/, and don't change existing theorems; add helpers.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| encoder code | lowering/defs/abiEncoderScript.sml | compile_abi_encode_child_def (mutual), compile_abi_encode_dyn_static_loop_def, compile_abi_encode_static_info_def; induction compile_abi_encode_child_ind |
| frag_exec rules | lowering/fragExecScript.sml | frag_exec_seq, frag_exec_conseq, frag_exec_pointwise, frag_exec_run_inst_seq (lift straight-line code), frag_exec_enter, frag_exec_loop, cs_extends_*, cs_appends_* |
| existing encoder proofs | lowering/abiEncoderPropsScript.sml | compile_abi_encode_copy_frag (AbiCopy via frag_exec: the pattern to follow), compile_abi_encode_static_correct, val_in_memory_prim_enc, val_in_memory_flag_enc, mcopy lemmas |
| static value = ABI bytes | lowering/proofs/valueEncodingProofsScript.sml | val_in_memory_static_abi(_mutual), mem_bytes_at lemmas |
| memory model | lowering/defs/valueEncodingScript.sml | val_in_memory, mem_word_at, mem_bytes_at, type_memory_size |
| ABI | .holbuild/src/verifereum/util/contractABIScript.sml | enc, enc_tuple, head_lengths, is_dynamic, static_length, enc_has_static_length, enc_tuple_append, enc_tuple_static |
| Vyper→ABI | semantics/vyperABIScript.sml | vyper_to_abi, vyper_to_abi_type, vyper_abi_size_bound |
| typing / ABI facts | semantics/prop/vyperTypeABIScript.sml | vyper_to_abi_total, vyper_to_abi_enc_length_bound |
| emit helpers | lowering/emitHelperPropsScript.sml, lowering/exprLoweringPropsScript.sml | emitted_insts_*, emit_op_ADD_correct, step_MLOAD/MSTORE, eval_operand_update_fresh, not_fresh_at, fresh_vars_wrt |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | step_inst_base (MLOAD, MSTORE, MCOPY, CALLDATACOPY, ALLOCA via exec_alloca_def, JMP, JNZ) |
| alloca invariants | venom/defs/venomMemDefsScript.sml, venom/ (grep alloca_inv) | alloca_inv, allocas_non_overlapping, alloca_next_valid, regions_disjoint |
| Python encoder | ~/workspace/vyper at commit cd74ce4f: vyper/codegen_venom/abi/abi_encoder.py | reference |
