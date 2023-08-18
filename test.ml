let test_print () =
  assert (print 123 @@ FreeVar 42 = "42");
  assert (print 42 Star = "*");
  assert (print 42 Box = "☐");
  (* Lambdas. *)
  assert (print 3 @@ Lam (fun x -> x) = "(λ3)");
  assert (print 3 @@ Lam (fun x -> Appl (x, FreeVar 42)) = "(λ(3 42))");
  (* Pi types. *)
  assert (print 3 @@ Pi (FreeVar 0, fun x -> x) = "(Π0.3)");
  assert (
    print 3 @@ Pi (FreeVar 0, fun x -> Appl (x, FreeVar 42)) = "(Π0.(3 42))");
  (* Applications. *)
  assert (print 42 @@ Appl (FreeVar 1, FreeVar 2) = "(1 2)");
  (* Annotations. *)
  assert (print 42 @@ Ann (FreeVar 1, FreeVar 2) = "(1 : 2)")

let test_equate () =
  let assert_eq t = assert (equate 42 (t, t)) in
  let assert_neq m n =
    assert (not @@ equate 42 (m, n));
    assert (not @@ equate 42 (n, m))
  in
  (* Free variables. *)
  assert_eq (FreeVar 0);
  assert_neq (FreeVar 0) (FreeVar 123);
  assert_neq (FreeVar 0) Star;
  (* Star and box. *)
  assert_eq Star;
  assert_neq Star (FreeVar 0);
  assert_eq Box;
  assert_neq Box (FreeVar 0);
  (* Lambdas. *)
  assert_eq (Lam (fun x -> x));
  assert_neq (Lam (fun x -> x)) (Lam (fun _ -> Star));
  assert_neq (Lam (fun x -> x)) Star;
  (* Pi types. *)
  assert_eq (Pi (FreeVar 0, fun x -> x));
  assert_neq (Pi (FreeVar 0, fun x -> x)) (Pi (FreeVar 123, fun x -> x));
  assert_neq (Pi (FreeVar 0, fun x -> x)) (Pi (FreeVar 0, fun _ -> Star));
  assert_neq (Pi (FreeVar 0, fun x -> x)) Star;
  (* Do not evaluate under a binder automatically. *)
  assert_neq (Lam (fun x -> x)) (Lam (fun x -> Appl (Lam (fun x -> x), x)));
  assert_neq
    (Pi (FreeVar 0, fun x -> x))
    (Pi (FreeVar 0, fun x -> Appl (Lam (fun x -> x), x)));
  (* Applications. *)
  assert_eq (Appl (FreeVar 0, FreeVar 1));
  assert_neq (Appl (FreeVar 0, FreeVar 1)) (Appl (FreeVar 123, FreeVar 1));
  assert_neq (Appl (FreeVar 0, FreeVar 1)) (Appl (FreeVar 0, FreeVar 123));
  assert_neq (Appl (FreeVar 0, FreeVar 1)) Star;
  (* Annotations. *)
  assert_eq (Ann (FreeVar 0, FreeVar 1));
  assert_neq (Ann (FreeVar 0, FreeVar 1)) (Ann (FreeVar 123, FreeVar 1));
  assert_neq (Ann (FreeVar 0, FreeVar 1)) (Ann (FreeVar 0, FreeVar 123));
  assert_neq (Ann (FreeVar 0, FreeVar 1)) Star

let test_eval () =
  let assert_eval t expected = assert (equate 0 (eval t, expected)) in
  assert_eval (FreeVar 42) (FreeVar 42);
  assert_eval Star Star;
  assert_eval Box Box;
  (* Lambdas. *)
  assert_eval (Lam (fun x -> x)) (Lam (fun x -> x));
  assert_eval (Lam (fun x -> Appl (Lam (fun x -> x), x))) (Lam (fun x -> x));
  (* Pi types. *)
  assert_eval (Pi (FreeVar 42, fun x -> x)) (Pi (FreeVar 42, fun x -> x));
  assert_eval
    (Pi (FreeVar 42, fun x -> Appl (Lam (fun x -> x), x)))
    (Pi (FreeVar 42, fun x -> x));
  (* Applications. *)
  assert_eval (Appl (Lam (fun x -> x), FreeVar 42)) (FreeVar 42);
  assert_eval (Appl (FreeVar 0, FreeVar 42)) (Appl (FreeVar 0, FreeVar 42));
  assert_eval
    (Appl (Appl (Lam (fun x -> x), FreeVar 0), FreeVar 42))
    (Appl (FreeVar 0, FreeVar 42));
  (* Annotations. *)
  assert_eval (Ann (FreeVar 42, FreeVar 0)) (FreeVar 42)

let assert_infer_sort ctx t expected_ty =
  let lvl = List.length ctx in
  assert (equate lvl (infer_sort lvl ctx t, expected_ty))

let test_infer_sort () =
  assert_infer_sort [] Star Box;
  assert_infer_sort [ Star ] (FreeVar 0) Star;
  assert_infer_sort [ Box ] (FreeVar 0) Box;
  try
    assert_infer_sort [ FreeVar 0; Star ] (FreeVar 1) Box;
    assert false
  with Failure msg -> assert (msg = "Want a sort, got 0: 1")

let assert_infer ctx t expected_ty =
  let lvl = List.length ctx in
  assert (equate lvl (infer_ty lvl ctx t, expected_ty))

let test_infer_var () =
  assert_infer [ Star ] (FreeVar 0) Star;
  assert_infer [ Box; Star ] (FreeVar 0) Star;
  assert_infer [ Box; Box; Star ] (FreeVar 0) Star;
  assert_infer [ Star; Box ] (FreeVar 1) Star;
  assert_infer [ Box; Star; Box ] (FreeVar 1) Star;
  assert_infer [ Star; Box; Box ] (FreeVar 2) Star;
  assert_infer [ Box; Star; Box; Box ] (FreeVar 2) Star;
  try
    assert_infer [ Star; Box; Box ] (FreeVar 3) Box;
    assert false
  with Invalid_argument msg -> assert (msg = "List.nth")

let test_infer_star_box () =
  assert_infer [] Star Box;
  assert_infer [ Box; Box; Box ] Star Box;
  try
    assert_infer [] Box Box;
    assert false
  with Failure msg -> assert (msg = "Has no type: ☐")

let test_infer_pi () =
  (* A term depending on a term. *)
  assert_infer
    [ Pi (FreeVar 0, fun _ -> Star); Star ]
    (Pi (FreeVar 0, fun x -> Appl (FreeVar 1, x)))
    Star;
  (* A term depending on a type. *)
  assert_infer
    [ Pi (Star, fun _ -> Star) ]
    (Pi (Star, fun x -> Appl (FreeVar 0, x)))
    Star;
  (* A type depending on a term. *)
  assert_infer
    [ Pi (FreeVar 0, fun _ -> Box); Star ]
    (Pi (FreeVar 0, fun x -> Appl (FreeVar 1, x)))
    Box;
  (* A type depending on a type. *)
  assert_infer
    [ Pi (Star, fun _ -> Box) ]
    (Pi (Star, fun x -> Appl (FreeVar 0, x)))
    Box;
  try
    assert_infer [ FreeVar 0; Star ] (Pi (FreeVar 1, fun _ -> Star)) Box;
    assert false
  with Failure msg -> (
    assert (msg = "Want a sort, got 0: 1");
    try
      assert_infer [ FreeVar 0; Star ] (Pi (Star, fun _ -> FreeVar 1)) Box;
      assert false
    with Failure msg -> assert (msg = "Want a sort, got 0: 1"))

let test_infer_appl () =
  (* An argument is checkable. *)
  assert_infer
    [ Pi (Pi (Star, fun _ -> Star), fun _ -> FreeVar 0); Star ]
    (Appl (FreeVar 1, Lam (fun x -> x)))
    (FreeVar 0);
  (* An argument is inferrable. *)
  assert_infer
    [ Pi (Star, fun x -> x); Star ]
    (Appl (FreeVar 1, FreeVar 0))
    (FreeVar 0);
  (* Evaluate the resulting type. *)
  assert_infer [ FreeVar 0; Star ]
    (Appl
       ( Ann
           ( Lam (fun _ -> FreeVar 1),
             Pi
               ( Star,
                 fun _ ->
                   Appl
                     ( Ann (Lam (fun x -> x), Pi (Star, fun _ -> Star)),
                       FreeVar 0 ) ) ),
         FreeVar 0 ))
    (FreeVar 0);
  try
    assert_infer [] (Appl (Star, Star)) Box;
    assert false
  with Failure msg -> assert (msg = "Want a Pi type, got ☐: *")

let test_infer_ann () =
  (* Annotate a checkable term. *)
  assert_infer [ Star ]
    (Ann (Lam (fun _ -> FreeVar 0), Pi (FreeVar 0, fun _ -> Star)))
    (Pi (FreeVar 0, fun _ -> Star));
  (* Annotate an inferrable term. *)
  assert_infer [ Star ] (Ann (FreeVar 0, Star)) Star;
  (* Evaluate the resulting type. *)
  assert_infer [ Star ]
    (Ann
       ( Lam (fun x -> x),
         Pi
           ( FreeVar 0,
             fun _ ->
               Appl (Ann (Lam (fun x -> x), Pi (Star, fun _ -> Star)), FreeVar 0)
           ) ))
    (Pi (FreeVar 0, fun _ -> FreeVar 0));
  try
    assert_infer [ FreeVar 0; Star ] (Ann (Star, FreeVar 1)) Box;
    assert false
  with Failure msg -> (
    assert (msg = "Want a sort, got 0: 1");
    try
      assert_infer [ FreeVar 0; Star ] (Ann (FreeVar 1, Star)) Box;
      assert false
    with Failure msg -> assert (msg = "Want type *, got 0: 1"))

let test_infer_lam () =
  try
    assert_infer [] (Lam (fun x -> x)) Box;
    assert false
  with Failure msg -> assert (msg = "Not inferrable: (λ0)")

let assert_check ctx t ty =
  let lvl = List.length ctx in
  assert (equate lvl (check_ty lvl ctx (t, ty), ty))

let test_check_lam () =
  assert_check
    [ Pi (Star, fun _ -> FreeVar 0); Star ]
    (Lam (fun x -> Appl (FreeVar 1, x)))
    (Pi (Star, fun _ -> FreeVar 0));
  try
    assert_check [ Star ] (Lam (fun x -> x)) (Pi (Star, fun _ -> FreeVar 0));
    assert false
  with Failure msg -> (
    assert (msg = "Want type 0, got *: 1");
    try
      assert_check [] (Lam (fun x -> x)) Star;
      assert false
    with Failure msg -> assert (msg = "Want a Pi type, got *: (λ0)"))

let test_check_infer () =
  assert_check [ Star ] (FreeVar 0) Star;
  try
    assert_check [ Box ] (FreeVar 0) Star;
    assert false
  with Failure msg -> assert (msg = "Want type *, got ☐: 0")

let impredicative_id () =
  let id_ty = Pi (Star, fun a -> Pi (a, fun _ -> a)) in
  let id_lam = Lam (fun _ -> Lam (fun x -> x)) in
  let id = Ann (id_lam, id_ty) in
  let id_id = Appl (Appl (id, id_ty), id) in
  assert_infer [] id_ty Star;
  assert_infer [] id id_ty;
  assert_infer [] id_id id_ty;
  assert (equate 0 (eval id_id, id_lam))

let () =
  test_print ();
  test_eval ();
  test_equate ();
  test_infer_sort ();
  test_infer_var ();
  test_infer_star_box ();
  test_infer_pi ();
  test_infer_appl ();
  test_infer_ann ();
  test_infer_lam ();
  test_check_lam ();
  test_check_infer ();
  impredicative_id ()