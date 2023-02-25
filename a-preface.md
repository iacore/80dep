# How to implement dependent types in 80 lines of code

> The only difference(!) between Shakespeare and you was the size of his idiom list -- not the size of his vocabulary.<br>&emsp; &emsp; <b>-- Alan Perlis, Epigrams on Programming [^epigrams]</b>

Dependent types are constantly gaining more and more attention in the world of functional programming. Some believe that, through the unification of type and term-level syntax [^unified-syntax] [^cayenne], they are capable of displacing many specific typing features of traditional languages, such as Haskell or OCaml, whereas others believe in the feasibility of proving theorems about code in the same language, through the fusion of programming and constructive mathematics [^curry-howard] [^idris-lang].

But what are dependent types, actually? Just as in most general-purpose programming languages we have types dependent on _types_, colloquially known as "generic types", in dependently typed languages, we have types dependent on _terms_. This addition makes the language very expressive, effectively enabling a user to perform term computation at compile-time. For example, consider what should happen when the type checker sees some argument `x` applied to `f` -- it should _check_ that the type of `x` is computationally equal (or "beta-convertible", as used in the literature) to the parameter type of `f`; this check involves reducing these two types to their beta normal forms and comparing them for alpha equivalence [^alpha-eq] [^eta-conv].

The fact that type checking can literally invoke evaluation makes dependent types not only interesting from a user's standpoint but also from that of a language implementer. In particular, one may wonder about the easiest way to implement dependent types. Of course, to fully answer the question, we must consider the exact features to be implemented -- dependent type systems range from some of the most minimalistic lambda calculi to some of the most sophisticated type systems used in practice. For the purposes of this writing, we are going to consider [Calculus of Constructions (CoC)] [^coc], which situates at the top of [Barendregt's lambda cube]. What makes CoC exciting is its simplicity and expressiveness: by permitting all four combinations of terms and types to depend on each other and by being strongly normalizing [^strong-norm], it can serve both as a type theory for a programming language [^CoC-pl] and as a type-theoretical foundation of (constructive) mathematics; at the same time, it has only one syntactic category that accommodates both terms and types.

[Calculus of Constructions (CoC)]: https://en.wikipedia.org/wiki/Calculus_of_constructions
[Barendregt's lambda cube]: https://en.wikipedia.org/wiki/Lambda_cube

As it turns out, implementing CoC should not take much code. A few months ago, I demonstrated the [implementation of CoC in about 120 lines of OCaml]. It was using a named representation of variables -- this is how lambda calculi are described in a typical textbook. However, there is still room for improvement: since variables are strings, we should take care of capture-avoiding substitution, renaming of bound variables during an alpha-equivalence check, and so on. This approach is notoriously wordy, inefficient, and error-prone. Using [De Bruijn indices] would not grant much simplification either since free variables now have to be reindexed each time we substitute under a binder.

[implementation of CoC in about 120 lines of OCaml]: https://gist.github.com/Hirrolot/89c60f821270059a09c14b940b454fd6
[De Bruijn indices]: https://en.wikipedia.org/wiki/De_Bruijn_index

Naturally, to come up with the most succinct (yet readable) implementation, we should _reuse_ as much of the metalanguage (OCaml in our case) as possible. Thus we arrive at [Higher-Order Abstract Syntax (HOAS)] -- a technique to encode object-language binders in terms of metalanguage functions [^hoas]. By doing this, we can now get rid of the machinery that was in charge of manipulating the first-order representation and instead focus on the essential parts of the implementation. To allow the manipulation of open terms, we extend HOAS with a constructor for free variables represented as [De Bruijn _levels_]. The file `CoC.ml` below uses the technique just described and consists of 80 lines of standalone OCaml. In contrast to the previous implementation, it also employs bidirectional typing [^bidirectional-typing] [^elab-zoo], which lets us omit type annotations in certain cases, e.g., we can omit the parameter type of a lambda abstraction if the latter is located in the argument position.

[Higher-Order Abstract Syntax (HOAS)]: https://cstheory.stackexchange.com/questions/20071/what-is-higher-order-in-higher-order-abstract-syntax
[De Bruijn _levels_]: https://proofassistants.stackexchange.com/questions/900/when-should-i-use-de-bruijn-levels-instead-of-indices

As an application of the developed system, I present a classical example of using dependent types: vectors parameterized by their length. Since vector lengths now dwell on type-level, we can guarantee statically that, for example, the `replicate` operation returns a vector of a given length, `concat` returns a vector whose length is equal to the sum of lengths of two passed vectors, and `zip` takes two vectors of the _same_ length and returns a vector of that length. The code relies on some rudimentary facilities of Church numerals and pairs, which also serve as a warm-up.

To learn about the theory behind Calculus of Constructions, I recommend reading the first seven chapters of ["Type Theory and Formal Proof: An Introduction"].

["Type Theory and Formal Proof: An Introduction"]: https://www.amazon.com/Type-Theory-Formal-Proof-Introduction/dp/110703650X

If something is unclear, feel free to ask in the comments [^future-directions].

[^epigrams]: [Epigrams on Programming](https://web.archive.org/web/19990117034445/http://www-pu.informatik.uni-tuebingen.de/users/klaeren/epigrams.html) by Alan Perlis
[^unified-syntax]: [Unified Syntax with Iso-Types](https://i.cs.hku.hk/~bruno/papers/aplas2016.pdf) by Yanpeng Yang, Xuan Bi, and Bruno C. d. S. Oliveira
[^cayenne]: [Cayenne — A Language with Dependent Types](https://link.springer.com/chapter/10.1007/10704973_6) by Lennart Augustsson
[^curry-howard]: [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) by Wikipedia
[^idris-lang]: [Idris: A Language for Type-Driven Development](https://www.idris-lang.org/) by Edwin Brady
[^alpha-eq]: Two terms are alpha-equivalent if they are syntactically equal up to renaming of bound variables; e.g., `\x . \y . x` (the so-called "K combinator") is alpha-equivalent to `\a . \b . a`.
[^eta-conv]: Additional checks may apply to make type checking more permissive; this includes eta conversion -- when `\x . f x` and `f` are considered equal.
[^coc]: [The Calculus of Constructions](https://hal.inria.fr/file/index/docid/76024/filename/RR-0530.pdf) by Thierry Coquand and Gérard Huet
[^strong-norm]: Strong normalization means that every term in the system eventually reduces to its value.
[^CoC-pl]: One may argue that unrestricted recursion is essential for _programming_, which obviously destroys strong normalization. However, we can remedy this either by adding a fixed-point combinator to CoC (the [Neut] way) or by only executing total functions at type-level (the [Idris] way).
[^hoas]: One well-known problem with HOAS is that you can define "exotic" terms that pattern-match on a binder variable (e.g., using OCaml's `match`). At least two solutions exist: Parametric Higher-Order Abstract Syntax (PHOAS) [^phoas-1] [^phoas-2] [^phoas-3] and Tagless Final [^tf-1] [^tf-2] [^tf-3], both of which make an object language representation parametrically polymorphic over a binder type, thus prohibiting examination of binder variables.
[^phoas-1]: [Parametric Higher-Order Abstract Syntax for Mechanized Semantics](http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf) by Adam Chlipala
[^phoas-2]: [Parametric HOAS with first-class modules](https://web.archive.org/web/20230224205154/https://syntaxexclamation.wordpress.com/2014/06/27/parametric-hoas-with-first-class-modules/) by Matthias Puech
[^phoas-3]: [Boxes Go Bananas: Encoding Higher-Order Abstract Syntax with Parametric Polymorphism](https://www.seas.upenn.edu/~sweirich/papers/itabox/icfp-published-version.pdf) by Geoffrey Washburn and Stephanie Weirich
[^tf-1]: [Finally Tagless, Partially Evaluated](https://okmij.org/ftp/tagless-final/JFP.pdf) by Jacques Carette, Oleg Kiselyov and Chung-chieh Shan
[^tf-2]: [Typed Tagless Final Interpreters](https://okmij.org/ftp/tagless-final/course/lecture.pdf) by Oleg Kiselyov
[^tf-3]: [Tagless-Final Style: Applications and Examples](https://okmij.org/ftp/tagless-final/cookbook.html) by Oleg Kiselyov
[^bidirectional-typing]: [Bidirectional Typing Rules: A Tutorial](https://davidchristiansen.dk/tutorials/bidirectional.pdf) by David Raymond Christiansen
[^elab-zoo]: [Minimal implementations for dependent type checking and elaboration](https://github.com/AndrasKovacs/elaboration-zoo) by András Kovács
[^future-directions]: If you wish to adopt the implementation below for your needs, it may be worth using Normalization by Evaluation (NbE) [^elab-zoo] [^NbE]. With NbE, instead of `term`, you would have `term` and `value`, and instead of `eval`, you would have 1) `eval`, which goes from `term` to `value`, and 2) `quote`, which goes back from `value` to `term`. The apparent advantage of this approach is that you would have a dedicated type for values, which you could use in some places to guarantee type safety; e.g., `infer_ty`, `infer_sort`, and `check_ty` in our implementation could return `value` instead of `term` (you could also make the typing context contain only values). The "Boxes Go Bananas" [^phoas-3] paper shows how to encode both `term` and `value` in terms of HOAS.
[^NbE]: [Checking Dependent Types with Normalization by Evaluation: A Tutorial](https://davidchristiansen.dk/tutorials/nbe/) ([Haskell version](https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf)) by David Thrane Christiansen

[Neut]: https://github.com/vekatze/neut
[idris]: https://www.idris-lang.org/

<details>
  <summary>Show unit tests</summary>

```ml
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
```

</details>

<div align="center">
  <img src="https://user-images.githubusercontent.com/40539574/221297687-b3171e0b-3323-41a5-ab67-7e33984f2826.gif" width="350px">
</div>
