(** Syntax ====================================================================================== *)

type variable =
 | String of string
 | Gensym of string * int
 | Dummy

(** Abstract syntax of expressions. *)
type expr =
  | Var of variable
  | Universe of int
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr

(** An abstraction [(x,t,e)] indicates that [x] of type [t] is bound in [e]. *)
and abstraction = variable * expr * expr

(** Substitution ================================================================================ *)

(** [refresh x] generates a fresh variable name whose preferred form is [x]. *)
let refresh =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Dummy -> (incr k ; Gensym ("_", !k))

(** [subst [(x1,e1); ...; (xn;en)] e] performs the given substitution of
    expressions [e1], ..., [en] for variables [x1], ..., [xn] in expression [e]. *)
let rec subst s = function
  | Var x -> (try List.assoc x s with Not_found -> Var x)
  | Universe k -> Universe k
  | Pi a -> Pi (subst_abstraction s a)
  | Lambda a -> Lambda (subst_abstraction s a)
  | App (e1, e2) -> App (subst s e1, subst s e2)

and subst_abstraction s (x, t, e) =
  let x' = refresh x in
    (x', subst s t, subst ((x, Var x') :: s) e)

(** Type inference ============================================================================== *)

(** [lookup_ty x ctx] returns the type of [x] in context [ctx]. *)
let lookup_ty x ctx = fst (List.assoc x ctx)

(** [lookup_value x ctx] returns the value of [x] in context [ctx], or [None]
    if [x] has no assigned value. *)
let lookup_value x ctx = snd (List.assoc x ctx)

(** [extend x t ctx] returns [ctx] extended with variable [x] of type [t],
    whereas [extend x t ~value:e ctx] returns [ctx] extended with variable [x]
    of type [t] and assigned value [e]. *)
let extend x t ?value ctx = (x, (t, value)) :: ctx

(** [infer_type ctx e] infers the type of expression [e] in context [ctx].  *)
let rec infer_type ctx = function
  | Var x ->
    (try lookup_ty x ctx
     with Not_found -> Error.typing "unkown identifier %t" (Print.variable x))
  | Universe k -> Universe (k + 1)
  | Pi (x, t1, t2) ->
    let k1 = infer_universe ctx t1 in
    let k2 = infer_universe (extend x t1 ctx) t2 in
      Universe (max k1 k2)
  | Lambda (x, t, e) ->
    let _ = infer_universe ctx t in
    let te = infer_type (extend x t ctx) e in
      Pi (x, t, te)
  | App (e1, e2) ->
    let (x, s, t) = infer_pi ctx e1 in
    let te = infer_type ctx e2 in
      check_equal ctx s te ;
      subst [(x, e2)] t

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer_type ctx t in
    match normalize ctx u with
      | Universe k -> k
      | App _ | Var _ | Pi _ | Lambda _ -> Error.typing "type expected"

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
    and infer_pi ctx e =
    let t = infer_type ctx e in
      match normalize ctx t with
        | Pi a -> a
        | Var _ | App _ | Universe _ | Lambda _ -> Error.typing "function expected"

  (** [check_equal ctx e1 e2] checks that expressions [e1] and [e2] are equal. *)
  and check_equal ctx e1 e2 =
    if not (equal ctx e1 e2)
    then Error.typing "expressions %t and %t are not equal" (Print.expr e1) (Print.expr e2)

type context = (Syntax.variable * (Syntax.expr * Syntax.expr option)) list

(** Normalization and equality ================================================================== *)

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.  *)
let rec normalize ctx = function
  | Var x ->
    (match
        (try lookup_value x ctx
         with Not_found -> Error.runtime "unkown identifier %t" (Print.variable x))
     with
       | None -> Var x
       | Some e -> normalize ctx e)
  | App (e1, e2) ->
    let e2 = normalize ctx e2 in
      (match normalize ctx e1 with
        | Lambda (x, _, e1') -> normalize ctx (subst [(x,e2)] e1')
        | e1 -> App (e1, e2))
  | Universe k -> Universe k
  | Pi a -> Pi (normalize_abstraction ctx a)
  | Lambda a -> Lambda (normalize_abstraction ctx a)

and normalize_abstraction ctx (x, t, e) =
  let t = normalize ctx t in
    (x, t, normalize (extend x t ctx) e)

(** [equal ctx e1 e2] determines whether normalized [e1] and [e2] are equal up to renaming
    of bound variables. *)
let equal ctx e1 e2 =
  let rec equal e1 e2 =
    match e1, e2 with
      | Var x1, Var x2 -> x1 = x2
      | App (e11, e12), App (e21, e22) -> equal e11 e21 && equal e12 e22
      | Universe k1, Universe k2 -> k1 = k2
      | Pi a1, Pi a2 -> equal_abstraction a1 a2
      | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
      | (Var _ | App _ | Universe _ | Pi _ | Lambda _), _ -> false
  and equal_abstraction (x, t1, e1) (y, t2, e2) =
    equal t1 t2 && (equal e1 (subst [(y, Var x)] e2))
  in
    equal (normalize ctx e1) (normalize ctx e2)

(** Main ======================================================================================== *)

let () = print_endline "Hello, World!"
