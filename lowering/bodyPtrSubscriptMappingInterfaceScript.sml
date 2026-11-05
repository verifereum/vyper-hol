(* Mapping-result interface probes; no execution or concrete J is defined. *)
Theory bodyPtrSubscriptMappingInterface
Ancestors
  bodyPtrDefs exprSimDefs exprSimHypsDefs loweringPosts gasContext

(* place_ptr_rel_def already supplies the exact HashMapRef slot equation;
   it is intentionally reused rather than duplicated here. *)

Theorem gas_admissible_mono:
  (!r. P r ==> Q r) /\ gas_admissible source P es ==>
  gas_admissible source Q es
Proof
  rw[gas_admissible_def] >> metis_tac[]
QED

Theorem mapping_result_domain_ordinary:
  expr_vv_res_ok r ==>
  expr_vv_res_ok r \/ (?tr slot kt vt. r = INL (HashMapRef tr slot kt vt))
Proof
  simp[]
QED

Theorem mapping_result_domain_slot:
  expr_vv_res_ok (INL (HashMapRef tr slot kt vt)) \/
  (?tr' slot' kt' vt'.
    INL (HashMapRef tr slot kt vt) = INL (HashMapRef tr' slot' kt' vt'))
Proof
  simp[]
QED

Theorem mapping_result_not_ordinary:
  ~expr_vv_res_ok (INL (HashMapRef tr slot kt vt))
Proof
  simp[expr_vv_res_ok_def]
QED

(* Proposed interface, NOT an execution theorem or a definition of J.

   Precondition: copy expr_body_pre_def, changing ONLY well_typed_expr env e
   to (well_typed_expr env e OR
       ?kt vt. type_place_expr env e = SOME (HashMapT kt vt)).
   Retain verbatim:
     expr_sim_inv cenv cx env es;
     byte_widths_expr e; alloc_limits_expr cenv e;
     call_evaluation_safe cx (int_calls_expr e); ~expr_has_evm_run e;
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                  get_module_code cx NONE = SOME tops) (int_calls_expr e);
     the supported_expr_exists/occurs_abi_decode_target implication;
     the dynamic ABI type implication at lines 159-160 of exprSimHypsDefs.
   This does not drop call/default/ABI restrictions. It is a proposed
   disjunction, not a proof that mapping typing supplies those restrictions.

   Initial execution hypotheses: all of expr_vv_sim_ptr_def lines 248-260,
   replacing only the admissibility predicate by the widened domain above.
   Keep gas_outcome_ptr and its exception post unchanged.

   Normal post: split ordinary results from INL (HashMapRef tr slot kt vt).
   Ordinary branch retains ALL of lines 263-273 of expr_vv_sim_ptr_def.
   Mapping branch requires res = INL (HashMapRef tr slot kt vt) and:
     vv = LocatedValue t' p;
     p.ptr_location = slot_loc tr;
     eval_operand p.ptr_operand t = SOME slot;
     op_taint tn p.ptr_operand = {};
     place_ptr_rel cenv cx t (HashMapRef tr slot kt vt)
       slot (SOME p.ptr_location) (HashMapT kt vt).
   The last clause is exactly the existing place_ptr_rel_def equation,
   independently of source reads and memory representation.
   Retain stmt_state_rel ctx func cenv cx ee t; landing bb/inst_idx at sb;
   old-variable preservation from sa; allocation lookup preservation;
   disjoint old-allocation memory framing (including aid < sa.cs_next_id);
   locals_kept cenv es s0 t; ghost_inv d cenv cx ee G tn t;
   ghost_kept cenv es sa G0 tn0 s0 G tn.

   Replace vv_holds and vv_at rather than retaining them: they require an
   ordinary readable value, which a HashMapRef does not provide. Similarly
   do not require ptr_vv_ok or ptr_buf_ok for the slot. target_post_def is
   a useful framing template, but its value_type_place/type and
   place_readable clauses do not certify mapping execution. Operand
   freshness at sb should be retained explicitly (as in target_post),
   rather than lost with vv_at, to allow subsequent compiled code to keep
   the captured slot.

   gas_admissible_mono proves only weakening of an input domain test.
   Neither it nor the domain facts produce marks, a gas_summary_ptr_at,
   a counted pointer path, or a gas_exempt_cert. gas_outcome_ptr_def
   requires those witnesses separately. In particular an ordinary
   expr_vv_sim_ptr cannot be applied at a mapping-success input merely by
   widening its precondition: the implication is in the wrong direction.
*)
