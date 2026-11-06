(* Diagnostic only: independent layouts, not a typed-copy execution theorem.
   An outer fixed array contains dynamic arrays widened from capacity 1 to 3.
   No padding cleanliness follows from either full-buffer coverage or typing. *)
Theory bodyPtrMakeArrayTypedLayoutProbe
Ancestors
  bodyPtrMakeArrayTypedBounds typedCopyCompatibilityPtr typedCopyLayoutPtr ptrCoverage
  compileEnv valueEncoding vyperTypeSystem

Theorem nested_widening_layout_probe:
  arg_type_fits
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Fixed 2)) /\
  type_memory_bytes cenv (ArrayT (BaseT (UintT 256)) (Dynamic 1)) = 64 /\
  type_memory_bytes cenv (ArrayT (BaseT (UintT 256)) (Dynamic 3)) = 128 /\
  type_memory_bytes cenv
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2)) = 128 /\
  type_memory_bytes cenv
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (Fixed 2)) = 256
Proof
  simp[arg_type_fits_def, type_memory_bytes_def]
QED

(* The second nested value begins at 64 in the source, 128 in the
   destination. Header and full child windows both fit, independently. *)
Theorem nested_widening_windows_probe:
  64 + 32 <= (128:num) /\ 128 + 32 <= (256:num) /\
  64 + 64 <= (128:num) /\ 128 + 128 <= (256:num) /\
  64 <> (128:num)
Proof
  decide_tac
QED

Theorem nested_source_coverage_probe:
  ptr_covers G tn p s 128 /\ lookup_var p s = SOME w /\
  FLOOKUP G p = SOME (b,cap) /\ b + cap <= dimword(:256) /\
  lookup_var q s' = SOME (w + n2w 64) /\
  FLOOKUP G' q = SOME (b,cap) /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' 64
Proof
  strip_tac >> irule ptr_covers_offset >> simp[] >>
  qexistsl_tac [`G`, `64`, `p`, `s`, `tn`, `128`, `w`] >> simp[] >> metis_tac[]
QED

(* Robust length controls ASSERT; it does not certify unused capacity.
   The same live sequence fits both layouts, including the empty case. *)
Theorem widened_dynamic_header_probe:
  LENGTH vs <= 1 /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (ArrayTV tv (Dynamic 1))
      (ArrayV (DynArrayV vs)) addr m) ==>
  LENGTH vs <= 3 /\
  !m. mem_agree_outside tn.t_mem mem m ==>
    mem_word_at addr m = n2w (LENGTH vs)
Proof
  strip_tac >> conj_tac >- decide_tac >>
  metis_tac[dynarray_in_memory_robust_length]
QED

(* Proposed recursive contract (a specification, NOT an asserted theorem).

   Common parameters: cx ctx PG func cenv tenv sa sb src dst G tn s,
   evaluated source/destination layouts stv/dtv and a semantic value v.
   Common premises: the indicated compiler computation sa=((),sb);
   fn_has_code sa sb func, fn_inst_ids_distinct func, installed entry cursor
   at sa in s; ctx_has_dalloca ctx is false; src/dst are non-fresh variables
   with values a/b; both layout evaluations succeed; compiler byte sizes
   agree with evaluated sizes and are <2**64; v has BOTH evaluated types;
   acyclic_struct_metadata and coherent evaluated struct fields; separate
   full-window ptr_covers facts; disjoint source/destination full windows;
   robust val_in_memory stv v at w2n a for every memory agreeing outside
   tn.t_mem. No premise says that unused source padding is untainted.

   Common conclusion: exists k Gf tnf sf, gas_path_ptr at the installed
   sa/sb cursors, with normal endpoint sf; robust val_in_memory dtv v at
   w2n b under tnf; every not_fresh_at sa variable retains lookup_var,
   FLOOKUP provenance and op_taint; memory bytes and memory-taint membership
   outside the destination window are unchanged; storage/transient/immutable
   taints and semantic ambient state are unchanged; stor_taint_ok preserved;
   every robust val_in_memory ft fv p disjoint from that window survives.
   Destination/source pointer coverage survives. These frame properties,
   not global tnf.t_mem SUBSET tn.t_mem, are the inductive interface.

   1. compile_store_memory_typed cenv dst dty src sty:
      common contract, with stv/dtv the evaluations of sty/dty, and full
      windows type_memory_bytes cenv sty/dty. Type compatibility is
      arg_type_fits sty dty (or a separately justified same-layout branch).
      Dispatch induction uses the destination type_rank, unchanged cenv.
      The word branch needs robust clean 32-byte source and resets load
      result provenance to NONE; the bytes branch can propagate padding
      taint while preserving a robust live destination representation.

   2. compile_typed_copy_fields cenv dst src dtys stys doff soff:
      equal list lengths, LIST_REL evaluate_type for each side, same value
      list with values_have_types on both evaluated lists. Each child is
      robust at source base+soff+SUM(source preceding sizes). Prefix bounds
      doff+SUM(destination sizes)<=destination total, independently
      soff+SUM(source sizes)<=source total. Conclusion reconstructs tuple
      memory at destination base+doff and frames the complement of that
      suffix window, retaining the initialized preceding prefix. Tail IH
      advances by DIFFERENT head sizes. Empty lists emit no access.

   3. compile_copy_sarray_typed cenv dst de src se count:
      evaluated layouts ArrayTV dev (Fixed count), ArrayTV sev (Fixed count),
      same sparse value, both typed. Windows count*destination stride and
      count*source stride, separately. Loop IH for i<=count carries robust
      destination elements below i and robust source elements from i on,
      plus common frame; absent sparse entries use typed default values.
      Equal stride/non-ABI-dynamic fast branch still needs semantic layout
      agreement: stride equality ALONE is not a general semantic contract.

   4. compile_copy_dynarray_typed cenv dst de dcap src se:
      source layout ArrayTV sev (Dynamic scap), destination layout
      ArrayTV dev (Dynamic dcap), same DynArrayV vs, LENGTH vs<=scap and
      LENGTH vs<=dcap. Full windows 32+scap*source stride and
      32+dcap*destination stride; live loop windows use LENGTH vs instead.
      Robust source header gives n2w(LENGTH vs); size bounds prevent word
      wrap, so GT/ISZERO/ASSERT succeeds. Header store establishes robust
      destination length. Loop IH adds initialized header to the static
      prefix IH. Empty vs executes header accesses but no data access;
      dirty unused capacity must remain permitted. Source read coverage
      cannot be replaced by val_footprint; word/bytes fast copies can read
      padding. Source robustness cannot be replaced by ptr_covers either.

   5. compile_struct_typed_copy cenv dst src dfs sfs doff soff:
      same field names/order in coherent metadata, successful ALOOKUP for
      each name; paired field values typed at both evaluated field types;
      numeric field sizes equal their own layout byte sizes. IH carries
      the same robust prefix/suffix contract as fields, using independently
      accumulated metadata sizes. The compiler's fallback on missing names
      is not justified by compatibility; coherence must exclude that case.

   Widened-call seam: lowered_value_type cenv (Call _ (IntCall f) _ _) is
   ce_func_return_type (nsid_to_string f), NOT expr_type of the call.
   A child expr_post represents the declared expr_type, whereas ptr_buf_ok
   covers the FULL lowered buffer capacity. Neither supplies robust source
   representation at the lowered evaluated type: SourceLayoutProbe's checked
   displaced-field tuple counterexample rules out generic layout transport.
   To instantiate (1), body_inv's return-type environment agreement and
   source well-typedness must separately imply arg_type_fits of that return
   type into the declared literal element, evaluation/size coherence, and
   destination value typing. Fresh literal allocation supplies separation.
   body_make_array_widened_call_elem in the S1 reference is admitted and
   supplies no such intermediate compatibility theorem. The above probe
   checks a compatible example, NOT this missing general derivation.
   Counted installed execution for (1)-(5), including loop cursors/backedges,
   and the complete body-level compatibility derivation remain unproved.
*)
