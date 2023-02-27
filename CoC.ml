type term =
  | Lam of (term -> term)
  | Pi of term * (term -> term)
  | Appl of term * term
  | Ann of term * term
  | FreeVar of int
  | Star
  | Box

let unfurl lvl f = f (FreeVar lvl)
let unfurl2 lvl (f, g) = (unfurl lvl f, unfurl lvl g)

let rec print lvl =
  let plunge f = print (lvl + 1) (unfurl lvl f) in
  function
  | Lam f -> "(λ" ^ plunge f ^ ")"
  | Pi (a, f) -> "(Π" ^ print lvl a ^ "." ^ plunge f ^ ")"
  | Appl (m, n) -> "(" ^ print lvl m ^ " " ^ print lvl n ^ ")"
  | Ann (m, a) -> "(" ^ print lvl m ^ " : " ^ print lvl a ^ ")"
  | FreeVar x -> string_of_int x
  | Star -> "*"
  | Box -> "☐"

let rec eval = function
  | Lam f -> Lam (fun n -> eval (f n))
  | Pi (a, f) -> Pi (eval a, fun n -> eval (f n))
  | Appl (m, n) -> (
      match (eval m, eval n) with Lam f, n -> f n | m, n -> Appl (m, n))
  | Ann (m, _a) -> eval m
  | (FreeVar _ | Star | Box) as t -> t

let rec equate lvl =
  let plunge (f, g) = equate (lvl + 1) (unfurl2 lvl (f, g)) in
  function
  | Lam f, Lam g -> plunge (f, g)
  | Pi (a, f), Pi (b, g) -> equate lvl (a, b) && plunge (f, g)
  | Appl (m, n), Appl (m', n') -> equate lvl (m, m') && equate lvl (n, n')
  | Ann (m, a), Ann (m', b) -> equate lvl (m, m') && equate lvl (a, b)
  | FreeVar x, FreeVar y -> x = y
  | Star, Star | Box, Box -> true
  | _, _ -> false

let panic lvl t fmt =
  let open Printf in
  let fail fmt = ksprintf failwith fmt in
  ksprintf (fun s -> fail "%s: %s" s (print lvl t)) fmt

let rec infer_ty lvl ctx = function
  | Pi (a, f) ->
      let _s1 = infer_sort lvl ctx a in
      let s2 = infer_sort (lvl + 1) (eval a :: ctx) (unfurl lvl f) in
      s2
  | Appl (m, n) -> (
      match infer_ty lvl ctx m with
      | Pi (a, f) ->
          let _ = check_ty lvl ctx (n, a) in
          f n
      | m_ty -> panic lvl m "Want a Pi type, got %s" (print lvl m_ty))
  | Ann (m, a) ->
      let _s = infer_sort lvl ctx a in
      check_ty lvl ctx (m, eval a)
  | FreeVar x -> List.nth ctx (lvl - x - 1)
  | Star -> Box
  | Box -> panic lvl Box "Has no type"
  | t -> panic lvl t "Not inferrable"

and infer_sort lvl ctx a =
  match infer_ty lvl ctx a with
  | (Star | Box) as s -> s
  | ty -> panic lvl a "Want a sort, got %s" (print lvl ty)

and check_ty lvl ctx = function
  | Lam f, Pi (a, g) ->
      let _ = check_ty (lvl + 1) (a :: ctx) (unfurl2 lvl (f, g)) in
      Pi (a, g)
  | Lam f, ty -> panic lvl (Lam f) "Want a Pi type, got %s" (print lvl ty)
  | t, ty ->
      let got_ty = infer_ty lvl ctx t in
      if equate lvl (ty, got_ty) then ty
      else panic lvl t "Want type %s, got %s" (print lvl ty) (print lvl got_ty)
