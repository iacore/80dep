(* Currying functions for lambdas. This is only for convenience. *)
let curry2 f = Lam (fun x -> Lam (fun y -> f x y))
let curry3 f = Lam (fun x -> curry2 (f x))
let curry4 f = Lam (fun x -> curry3 (f x))
let curry5 f = Lam (fun x -> curry4 (f x))

(* A left-folded application. *)
let appl f args = List.fold_left (fun m n -> Appl (m, n)) f args

(* Tests two terms for beta-convertibility. *)
let assert_beta_eq m n = assert (equate 0 (eval m, eval n))

let () =
  (* Church numerals. *)
  let n_ty =
    Pi (Star, fun a -> Pi (Pi (a, fun _x -> a), fun _f -> Pi (a, fun _x -> a)))
  in

  (* The zero constant and successor function. *)
  let zero = Ann (curry3 (fun _a _f x -> x), n_ty) in
  let succ =
    Ann
      ( curry4 (fun n a f x -> Appl (f, appl n [ a; f; x ])),
        Pi (n_ty, fun _n -> n_ty) )
  in

  (* 1, 2, 3, 4 derived from zero and the successor function. *)
  let one = Appl (succ, zero) in
  let two = Appl (succ, one) in
  let three = Appl (succ, two) in
  let four = Appl (succ, three) in
  assert_infer [] zero n_ty;
  assert_infer [] one n_ty;
  assert_infer [] two n_ty;
  assert_infer [] three n_ty;
  assert_infer [] four n_ty;

  (* The addition function on two numerals. *)
  let add_ty = Pi (n_ty, fun _n -> Pi (n_ty, fun _m -> n_ty)) in
  let add =
    Ann (curry5 (fun n m a f x -> appl n [ a; f; appl m [ a; f; x ] ]), add_ty)
  in
  assert_infer [] add add_ty;

  (* Test addition on the derived numerals. *)
  assert_beta_eq (appl add [ zero; zero ]) zero;
  assert_beta_eq (appl add [ zero; one ]) one;
  assert_beta_eq (appl add [ one; zero ]) one;
  assert_beta_eq (appl add [ three; one ]) four;

  (* Church pairs. *)
  let pair_ty = Pi (Star, fun _a -> Pi (Star, fun _b -> Star)) in
  let pair =
    Ann
      ( Lam
          (fun a ->
            Lam
              (fun b ->
                Pi
                  ( Star,
                    fun c ->
                      Pi (Pi (a, fun _x -> Pi (b, fun _y -> c)), fun _f -> c) ))),
        pair_ty )
  in
  assert_infer [] pair pair_ty;

  (* Type-safe programming with vectors. First, define a typing context that
     represents a hypothetical vector module. *)
  let vect_ty n a = appl (FreeVar 0) [ n; a ] in
  let item_ty = FreeVar 1 in

  let vect_ctx =
    [
      (* A vector parameterized by its length and item type. *)
      Pi (n_ty, fun _n -> Pi (Star, fun _a -> Star));
      (* The uninterpreted vector item type. *)
      Star;
      (* The item value. *)
      item_ty;
      (* The replicate function that constructs a vector containing N items
         of the same value. *)
      Pi (n_ty, fun n -> Pi (Star, fun a -> Pi (a, fun _x -> vect_ty n a)));
      (* The concatenate function on two vectors. *)
      Pi
        ( n_ty,
          fun n ->
            Pi
              ( n_ty,
                fun m ->
                  Pi
                    ( Star,
                      fun a ->
                        Pi
                          ( vect_ty n a,
                            fun _x ->
                              Pi
                                ( vect_ty m a,
                                  fun _y -> vect_ty (appl add [ n; m ]) a ) ) )
              ) );
      (* The zip function that takes two vectors of the same length and
         returns a new zipped vector. *)
      Pi
        ( n_ty,
          fun n ->
            Pi
              ( Star,
                fun a ->
                  Pi
                    ( Star,
                      fun b ->
                        Pi
                          ( vect_ty n a,
                            fun _x ->
                              Pi
                                ( vect_ty n b,
                                  fun _y -> vect_ty n (appl pair [ a; b ]) ) )
                    ) ) );
    ]
    (* A typing context must contain only evaluated types. *)
    |> List.map eval
    (* Context bindings must be indexed by De Bruijn indices, not levels. *)
    |> List.rev
  in

  let vect_ty n = eval @@ vect_ty n item_ty in
  let item = FreeVar 2 in
  let replicate n x = appl (FreeVar 3) [ n; item_ty; x ] in
  let concat n m x y = appl (FreeVar 4) [ n; m; item_ty; x; y ] in
  let zip n x y = appl (FreeVar 5) [ n; item_ty; item_ty; x; y ] in

  let assert_infer = assert_infer vect_ctx in

  (* Produce a one-value, three-value, and four-value vectors using the
     functions above. *)
  let vect_one = replicate one item in
  let vect_three = replicate three item in
  let vect_four = concat one three vect_one vect_three in
  assert_infer vect_one (vect_ty one);
  assert_infer vect_three (vect_ty three);
  assert_infer vect_four (vect_ty four);

  (* If we attempt to zip two vectors of different lengths, the type checker
     will produce an appropriate error message. This would be impossible
     to assure statically without dependent types or a similar mechanism, such
     as refinement types. *)
  try
    assert_infer (zip four vect_one vect_four) Box;
    assert false
  with Failure msg ->
    let p = print (List.length vect_ctx) in
    assert (
      msg
      = Printf.sprintf "Want type %s, got %s: %s"
          (p @@ vect_ty four)
          (p @@ vect_ty one)
          (p vect_one))
