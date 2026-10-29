(* Construction/inspection boundary shared by HOL and standalone JSON imports. *)
signature jsonImportTerm = sig
  type term
  type hol_type
  val constant : {Thy : string, Name : string} -> term
  val named_type : {Thy : string, Tyop : string} -> hol_type
  val bool_ty : hol_type
  val string_ty : hol_type
  val int_ty : hol_type
  val num_ty : hol_type
  val mk_type : string * hol_type list -> hol_type
  val mk_prod : hol_type * hol_type -> hol_type
  val mk_option : hol_type -> hol_type
  val word_ty : int -> hol_type
  val word_literal : int * IntInf.int -> term
  val address_from_hex : string -> term
  val bytes32_from_hex : string -> term
  val bytes_from_hex : string -> term
  val flat_bytes_from_hex : string -> term
  val mk_comb : term * term -> term
  val list_mk_comb : term * term list -> term
  val mk_pair : term * term -> term
  val dest_pair : term -> term * term
  val mk_list : term list * hol_type -> term
  val mk_some : term -> term
  val mk_none : hol_type -> term
  val is_some : term -> bool
  val dest_some : term -> term
  val mk_bool : bool -> term
  val fromMLstring : string -> term
  val natural : IntInf.int -> term
  val integer : IntInf.int -> term
  (* Inspection is structural, not evaluation. For a constructor constant c,
     strip_comb (list_mk_comb (c, args)) must recover c and args in order,
     including when the backend uses specialized list/pair/option nodes.
     aconv compares imported syntax: identical constructors and recursively
     identical arguments compare equal; distinct constructors remain distinct.
     Equal CV encodings alone do not imply equal imported terms. *)
  val strip_comb : term -> term * term list
  val aconv : term -> term -> bool
  (* dest_list (mk_list (xs, ty)) recovers xs and ty. *)
  val dest_list : term -> term list * hol_type
  (* True exactly for imported strings and natural numbers. The legacy-call
     validator stops here instead of traversing their representation; integers,
     words, booleans, and nullary AST constructors are not covered by this guard. *)
  val is_string_or_natural : term -> bool
  val mk_record : hol_type * (string * term) list -> term
end
