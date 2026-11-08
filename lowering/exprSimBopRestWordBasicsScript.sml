(* Basic representation and dispatch facts for variable-array membership. *)
Theory exprSimBopRestWordBasics
Ancestors
  exprLowering context compileEnv vyperValueOperation vyperValue
  loweringPosts exprSimMemorySource vyperLookupStorage vyperStorage list words

Theorem rest_word_sparse_empty:
  evaluate_in_array (ArrayTV et (Fixed 0)) v (SArrayV []) = F
Proof
  simp[evaluate_in_array_def]
QED

Theorem rest_word_sparse_default:
  evaluate_in_array (ArrayTV et (Fixed 1)) v (SArrayV []) =
  (v = default_value et)
Proof
  simp[evaluate_in_array_def]
QED

Theorem rest_word_dynamic_singleton:
  evaluate_in_array (ArrayTV et (Dynamic cap)) v (DynArrayV [x]) = (v = x)
Proof
  simp[evaluate_in_array_def]
QED

Theorem rest_word_vv_read_suffix:
  vv_holds cenv cx ty tv vv es s ==>
  ?v. !tail. read_result cx tv (es with gas_obs := tail) =
    (INL v, es with gas_obs := tail)
Proof
  Cases_on `vv` >> simp[vv_holds_def] >> strip_tac
  >- (drule read_result_gas_obs >> metis_tac[]) >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >>
  drule read_result_gas_obs >> metis_tac[]
QED

Theorem rest_word_fixed_dispatch:
  compile_var_array_membership cenv needle vv (ArrayT et (Fixed n)) is_in =
  compile_array_membership_loop needle (vv_operand vv) (Lit (n2w n))
    (elem_size_in_location cenv
      (case vv_location vv of SOME l => l | NONE => LocMemory) et) 0
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location vv of SOME l => l | NONE => LocMemory)) NONE is_in
Proof
  simp[compile_var_array_membership_def, LET_THM] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem rest_word_code_loader:
  compile_ptr_load is_ctor imm LocCode off =
  (if is_ctor then
     case imm of
       NONE => emit_op ILOAD [off]
     | SOME region_base => comp_bind (emit_op ADD [off; region_base])
                              (\addr. emit_op ILOAD [addr])
   else emit_op DLOAD [off])
Proof
  simp[compile_ptr_load_def, compile_imm_load_word_def]
QED

Theorem rest_word_dynamic_dispatch:
  compile_var_array_membership cenv needle vv (ArrayT et (Dynamic cap)) is_in =
  comp_bind
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location vv of SOME l => l | NONE => LocMemory) (vv_operand vv))
    (\len_op.
      compile_array_membership_loop needle (vv_operand vv) len_op
          (elem_size_in_location cenv
            (case vv_location vv of SOME l => l | NONE => LocMemory) et)
          (word_scale (case vv_location vv of SOME l => l | NONE => LocMemory))
          (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
            (case vv_location vv of SOME l => l | NONE => LocMemory)) (SOME cap) is_in)
Proof
  simp[compile_var_array_membership_def, LET_THM]
QED

Theorem rest_word_signed_decode_probe:
  truncate_signed 8 (-1w : 256 word) = -1
Proof
  CONV_TAC (LAND_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV))) >>
  pure_rewrite_tac[vyperStorageTheory.truncate_signed_def, LET_THM] >>
  simp[wordsTheory.word_2comp_n2w, wordsTheory.dimword_def,
       SF wordsLib.SIZES_ss] >> intLib.ARITH_TAC
QED

Theorem rest_word_signed_canonical_probe:
  word_slot_canonical (-1w) (BaseTV (IntT 8))
Proof
  simp[word_slot_canonical_def, decode_base_from_slot_def,
       rest_word_signed_decode_probe, encode_base_to_slot_def,
       integer_wordTheory.i2w_def]
QED

(* C1.1 finite contract inventory (PROPOSALS, NOT proved theorem declarations).

   C1.3 SOURCE BOUNDARY. Reuse array_length and array_index, not a second
   association-list/list view definition. The proposed indexed view is simply

     L = array_length (ArrayTV etv bd) av /\
     (!i. i < L ==> array_index (ArrayTV etv bd) av (&i) = SOME (E i)).

   Proposed single consumer theorem:

     is_word_type et /\ evaluate_type (get_tenv cx) et = SOME etv /\
     value_has_type etv needle /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
     L = array_length (ArrayTV etv bd) av /\
     (!i. i < L ==> array_index (ArrayTV etv bd) av (&i) = SOME (E i))
     ==>
     (evaluate_in_array (ArrayTV etv bd) needle av <=>
       ?i. i < L /\ typed_val_to_w256 etv (E i) =
                         typed_val_to_w256 etv needle).

   All names above except L/E are existing constants. E has type num->value,
   L:num, et:type, etv:type_value, av:array_value, needle:value. Here `type` denotes the
   existing source type datatype (infer it from evaluate_type), not an ML type.
   array_index already fills a missing fixed-array ALOOKUP with default_value
   etv; dynamic entries use oEL. No new definition is needed for that behavior.
   Missing proofs owned by C1.3: total indexed existence under value_has_type,
   sparse sorted/in-range keys -> missing-index equivalence, and typed-word
   equality reflection on well-typed values of ONE evaluated word type.

   C1.4/C1.5 LOAD BOUNDARY. One proposed aggregate adapter statement, with
   explicit let-bound terms instead of new global definitions:

     vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
     expr_type e = ArrayT et bd /\ is_word_type et /\
     evaluate_type (get_tenv cx) et = SOME etv /\
     read_result cx tv es' = (INL (ArrayV av),es') /\
     value_has_type (ArrayTV etv bd) (ArrayV av) /\
     L = array_length (ArrayTV etv bd) av /\
     (!j. j < L ==> array_index (ArrayTV etv bd) av (&j) = SOME (E j)) /\
     eval_operand (vv_operand vv) s = SOME base /\
     i < L
     ==>
     let loc = (case vv_location vv of SOME l => l | NONE => LocMemory) in
     let stride = elem_size_in_location cenv loc et in
     let hdr = (case bd of Fixed n => 0 | Dynamic cap => word_scale loc) in
     let a = w2n base + hdr + i * stride in
       L < dimword (:256) /\ a < dimword (:256) /\
       (case loc of
          LocMemory => mload a s = typed_val_to_w256 etv (E i)
        | LocStorage => sload (n2w a) s = typed_val_to_w256 etv (E i)
        | LocTransient => tload (n2w a) s = typed_val_to_w256 etv (E i)
        | LocCode =>
            (if cenv.ce_is_ctor then mload a s else
               word_of_bytes T (0w:bytes32)
                 (TAKE 32 (DROP a s.vs_data_section ++ REPLICATE 32 0w))) =
            typed_val_to_w256 etv (E i)
        | LocCalldata => F).

   This is NOT certified under just the displayed hypotheses: C1.4/C1.5 must
   audit whether expr_body_pre well-formedness/environment/allocation clauses
   are also needed, and derive them at the real use site, not strengthen the
   frozen theorem. In particular no L<dimword bound follows merely from the
   numeric constructor Fixed n. Need array typing/type-size/environment bounds.
   For a memory/code word also need a+32 <= valid represented region end;
   for storage need a+type_slot_size etv <= containing slot-region end.
   Once these are proved, n2w addition/multiplication matches natural a.

   Premise provenance:
   - vv_post already contains stmt_state_rel, vv_holds, vv_at and the frame.
   - rest_word_vv_read_suffix supplies read existence with arbitrary gas tail.
   - Runtime typing comes from expr_body_pre_runtime_typed/source preservation,
     NOT merely a pointer operand. Prove scalar element typing via array_index.
   - Memory LocatedValue: vv_holds supplies val_in_memory of the WHOLE array;
     vv_at supplies val_wf and an allocation/local footprint interval (or zero
     footprint). stmt_state_rel must provide its upper address-space bound.
     StackValue arrays use expr_val_rel/expr_val_at instead, not word encoding.
   - Code: immutable_holds supplies off+type_memory_size itv<dimword and
     sub_layout OR ctor staged-buffer bytes. Need an indexed sub_layout step.
     Runtime immutable_holds_dload then applies at the scalar element. Ctor
     immutable_holds_iload applies there; optional ce_imm_alloca ADD must use
     step_ADD_imm_base (state relation makes that base zero), not assume it.
   - Calldata is impossible directly from vv_holds_def.

   Storage-specific missing implication (C1.5), shared by tr=F and tr=T:

     storage_holds cx tr (ArrayT et bd) tv base es' s /\
     is_word_type et /\ evaluate_type (get_tenv cx) et = SOME etv /\
     read_result cx tv es' = (INL (ArrayV av),es') /\
     value_has_type (ArrayTV etv bd) (ArrayV av) /\
     array_index (ArrayTV etv bd) av (&i) = SOME elem /\
     i < array_length (ArrayTV etv bd) av
     ==>
     storage_holds cx tr et (Value elem)
       (base + n2w ((case bd of Fixed n => 0 | Dynamic cap => 1) +
                    i * type_slot_size etv)) es' s.

   To prove it, specialize decode_value, slots_in_range and storage_range_agree
   to that element interval. Only THEN use storage_holds_load. Decoding alone
   does not give equality of the full raw word for narrow int/address/bytes.
   Existing compile_ptr_load_memory_correct/storage_correct give run_inst_seq,
   fresh-vars, old operand preservation and unchanged memory; they do not alone
   prove preservation of stmt_state_rel or the required counted path. Transient
   and code require their respective load instruction contracts.

   Proposed predicate interface (not installed as a HOL definition here):

     rest_word_array_ready memory ctx func cenv cx et bd etv av vv es s <=>
       stmt_state_rel ctx func cenv cx es s /\
       is_word_type et /\ evaluate_type (get_tenv cx) et = SOME etv /\
       value_has_type (ArrayTV etv bd) (ArrayV av) /\
       let loc = (case vv_location vv of SOME l => l | NONE => LocMemory) in
       let L = array_length (ArrayTV etv bd) av in
       let stride = elem_size_in_location cenv loc et in
       let hdr = (case bd of Fixed n => 0 | Dynamic cap => word_scale loc) in
       ?base.
         eval_operand (vv_operand vv) s = SOME base /\
         L < dimword (:256) /\
         w2n base + hdr + L * stride <= dimword (:256) /\
         (memory /\ (loc = LocMemory \/ loc = LocCode /\ cenv.ce_is_ctor) ==>
            w2n base + hdr + L * stride <= s.vs_alloca_next) /\
         (case bd of Fixed n => T | Dynamic cap =>
            L <= cap /\
            (case loc of
               LocMemory => mload (w2n base) s
             | LocStorage => sload base s
             | LocTransient => tload base s
             | LocCode => if cenv.ce_is_ctor then mload (w2n base) s else
                 word_of_bytes T (0w:bytes32)
                   (TAKE 32 (DROP (w2n base) s.vs_data_section ++
                             REPLICATE 32 0w))
             | LocCalldata => 0w) = n2w L) /\
         loc <> LocCalldata /\
         (!i elem. i < L /\
            array_index (ArrayTV etv bd) av (&i) = SOME elem ==>
            let a = w2n base + hdr + i * stride in
            (case loc of
               LocMemory => mload a s
             | LocStorage => sload (n2w a) s
             | LocTransient => tload (n2w a) s
             | LocCode => if cenv.ce_is_ctor then mload a s else
                 word_of_bytes T (0w:bytes32)
                   (TAKE 32 (DROP a s.vs_data_section ++ REPLICATE 32 0w))
             | LocCalldata => 0w) = typed_val_to_w256 etv elem).

   Derivability of this proposed predicate, particularly whole-array end and
   memory extent bounds for the zero-length and immutable alternatives, is NOT
   established. If too strong, C1.4/C1.5 must refine it before investment in the
   loop; it is not permission to require it in the frozen theorem. C1.6 must
   prove its raw-read component stable under its fresh variable updates using
   the actual fixed compile_ptr_load, not posit arbitrary-loader preservation.

   C1.6/C1.7 COUNTED PATH BOUNDARY. Generic loader proof is supplied as a body
   interface: at each i<L and each frame-preserving intermediate state, it
   returns typed_val_to_w256 etv (E i), preserves the represented regions and
   protected operands, and has zero GAS reads. Its exact emitted body endpoints
   must come from C1.6 layout; do not quantify only over the initial state.
   Proposed consumer theorem for the whole instantiated variable-array tail:

     compile_var_array_membership cenv needle_op vv (ArrayT et bd) is_in
       sm = (out,sb) /\ fn_has_code sm sb func /\
     eval_operand needle_op u = SOME (typed_val_to_w256 etv needle) /\
     (!x. needle_op = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
     fresh_vars_wrt sm u /\ ~u.vs_halted /\
     u.vs_current_bb = sm.cs_current_bb /\
     u.vs_inst_idx = LENGTH sm.cs_current_insts /\
     rest_word_array_ready memory ctx func cenv cx et bd etv av vv fin u /\
     value_has_type etv needle
     ==>
     ?z. gas_marked_path memory ctx func u 0 (OK z) /\
         eval_operand out z = SOME
           (bool_to_word (if is_in then
              evaluate_in_array (ArrayTV etv bd) needle av
            else ~evaluate_in_array (ArrayTV etv bd) needle av)) /\
         (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
         z.vs_memory = u.vs_memory /\ z.vs_accounts = u.vs_accounts /\
         z.vs_allocas = u.vs_allocas /\
         z.vs_current_bb = sb.cs_current_bb /\
         z.vs_inst_idx = LENGTH sb.cs_current_insts.

   rest_word_array_ready above is deliberately a PROPOSED definition interface,
   not a compiled definition or an assumption silently added to the target.
   C1.6 must fix its precise state predicate and loader endpoints. C1.7 must
   show dynamic length<=cap assertion succeeds from source typing. The frame
   needs transient/data-section preservation too (account equality alone is
   insufficient); preserve the full non-vars/control/gas record frame or an
   established stmt_state_rel invariant. Do not assert fresh result/index vars
   are unchanged. For memory-counted mode include the memory extent premises
   required by gas_marked_path; derive these from allocations, not new axioms.

   Gas bridge: membership dispatch/loop/load instructions contain no GAS.
   After proving the actual zero-read path, gas_marked_exec_def with marks=[]
   and gas_explicit_nil reduces its source side to

     !tail. bop_result cx ann bop [expr_type e1;expr_type e2] needle (ArrayV av)
              (fin with gas_obs:=tail) = INL (BoolV b),

   where bop=In or NotIn and b is the matching source Boolean. Source tail
   leaves fin unchanged; hence es_end=fin. This is the exact final premise of
   rest_word_mixed_marked_tail, with suffix=[] and r=OK z. It still requires
   proof of the source result/type evaluation and of zero GAS on EVERY loader
   branch; conditional composition does not prove these premises. The prior
   left/right operand marks may be arbitrary. No global zero-events assumption.
*)
